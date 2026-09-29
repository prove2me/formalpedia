-- Prove2me | solution 1 for Hirsch.diamLE_of_nonzero_rows
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:27:51.101964+00:00
-- url     : https://prove2.me/submissions/a0c81d06-3cd0-4ac7-9128-456a0224d68a

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
set_option autoImplicit false

namespace NumberHirschRows

lemma diam_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {B C : ℕ} (hBC : B ≤ C) (h : Hirsch.DiamLE P B) :
    Hirsch.DiamLE P C := by
  intro u hu v hv
  obtain ⟨w, h0, hB, hw⟩ := h u hu v hv
  refine ⟨fun i => w (min i B), by simpa using h0, ?_, ?_⟩
  · simpa [Nat.min_eq_right hBC] using hB
  · intro i hi
    by_cases hiB : i < B
    · have hiB' : i + 1 ≤ B := by omega
      simpa [Nat.min_eq_left (Nat.le_of_lt hiB), Nat.min_eq_left hiB'] using hw i hiB
    · left
      change w (min i B) = w (min (i + 1) B)
      rw [Nat.min_eq_right (by omega : B ≤ i), Nat.min_eq_right (by omega : B ≤ i + 1)]

end NumberHirschRows

theorem solution (d : ℕ) (β : ℕ → ℕ) (hβ : Monotone β)
    (h : ∀ (m : ℕ) (a : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ), (∀ j, a j ≠ 0) →
      Bornology.IsBounded (Hirsch.Hpoly a b) → Hirsch.DiamLE (Hirsch.Hpoly a b) (β m))
    (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b)) :
    Hirsch.DiamLE (Hirsch.Hpoly a b) (β n) := by
  classical
  by_cases hempty : Hirsch.Hpoly a b = ∅
  · simp [hempty, Hirsch.DiamLE]
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  let S := {j : Fin n // a j ≠ 0}
  let m := Fintype.card S
  let e : Fin m ≃ S := (Fintype.equivFin S).symm
  let a' : Fin m → EuclideanSpace ℝ (Fin d) := fun i => a (e i).val
  let b' : Fin m → ℝ := fun i => b (e i).val
  have hnz : ∀ j, a' j ≠ 0 := fun j => (e j).property
  have heq : Hirsch.Hpoly a' b' = Hirsch.Hpoly a b := by
    ext z
    constructor
    · intro hz j
      by_cases hj : a j = 0
      · have hxj := hx j
        simpa [hj] using hxj
      · have hzj := hz (e.symm ⟨j, hj⟩)
        simpa [a', b'] using hzj
    · intro hz j
      exact hz (e j).val
  have hmn : m ≤ n := by
    calc m = Fintype.card S := rfl
         _ ≤ Fintype.card (Fin n) := Fintype.card_le_of_injective
           (fun j : S => j.val) Subtype.val_injective
         _ = n := Fintype.card_fin n
  have hsmall := h m a' b' hnz (heq.symm ▸ hbd)
  rw [heq] at hsmall
  exact NumberHirschRows.diam_mono (hβ hmn) hsmall

#print axioms solution
