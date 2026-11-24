import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1663 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ w W : Fin N, (w = s ∧ W = Ms ∨ w = p ∧ W = Mp) → ∀ P ∈ L W,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L Mv)))) ∧
    (∀ w S1 : Fin N, (w = s ∨ w = p) → w ∈ L S1 → (∀ u : Fin N, (u = v ∨ u = s ∨ u = p) → u ∈ L S1 → u = w) → ∀ P ∈ L Mv,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S)) ∧ (P ∈ L S1 ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S1)))) := by
  intro q N L v s p Mv Ms Mp _ _ _ hinter htriangle hsMv hpMv hpMs hvMs hvMp hsMp
    S hvS hsS hpS
  have uniquePoint {A B x y : Fin N} (hab : A ≠ B)
      (hxA : x ∈ L A) (hxB : x ∈ L B) (hyA : y ∈ L A) (hyB : y ∈ L B) : x = y :=
    Finset.card_le_one_iff.mp (hinter A B hab).le
      (Finset.mem_inter.mpr ⟨hxA, hxB⟩) (Finset.mem_inter.mpr ⟨hyA, hyB⟩)
  have hvMv : v ∉ L Mv := fun h => htriangle Mv ⟨h, hsMv, hpMv⟩
  have hsp : s ≠ p := by
    intro e
    exact htriangle Ms ⟨hvMs, e ▸ hpMs, hpMs⟩
  constructor
  · intro w W hw P hPW htest
    obtain ⟨hS, hMv⟩ := htest
    have facts : w ∉ L S ∧ v ∈ L W ∧ W ≠ S := by
      rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hsS, hvMs, fun h => hpS (h ▸ hpMs)⟩
      · exact ⟨hpS, hvMp, fun h => hsS (h ▸ hsMp)⟩
    obtain ⟨hwS, hvW, hWS⟩ := facts
    have hPS : P ∈ L S := hS.elim id (fun h => (hwS h.2.2.2).elim)
    have heq := uniquePoint hWS hPW hPS hvW hvS
    subst P
    exact hMv.elim hvMv (fun h => h.1 rfl)
  · intro w S1 hw hwS1 hspecial P hPMv htest
    obtain ⟨hS, hS1⟩ := htest
    have hwS : w ∉ L S := hw.elim (fun e => e ▸ hsS) (fun e => e ▸ hpS)
    have hwMv : w ∈ L Mv := hw.elim (fun e => e ▸ hsMv) (fun e => e ▸ hpMv)
    have hvS1 : v ∉ L S1 := by
      intro h
      have e := hspecial v (Or.inl rfl) h
      exact hwS (e ▸ hvS)
    have hlines : Mv ≠ S1 := by
      intro e
      have es := hspecial s (Or.inr (Or.inl rfl)) (e ▸ hsMv)
      have ep := hspecial p (Or.inr (Or.inr rfl)) (e ▸ hpMv)
      exact hsp (es.trans ep.symm)
    have hPS1 : P ∈ L S1 := hS1.elim id (fun h => (hvS1 h.2.2.2).elim)
    have heq := uniquePoint hlines hPMv hPS1 hwMv hwS1
    subst P
    rcases hS with h | h
    · exact hwS h
    · exact hw.elim h.2.1 h.2.2.1
