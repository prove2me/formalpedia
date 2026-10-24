-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_fiber_volume_homothety
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:35:27.880589+00:00
-- url     : https://prove2.me/submissions/fde93536-9d40-4d13-b26c-cd155b7d2d48

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open scoped BigOperators Pointwise

theorem solution
    (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
    ENNReal.ofReal r ^ n *
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by
  let S : Set (Fin n → Real) :=
    {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1}
  have hset :
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
        Set.image (fun y : Fin n → Real => r • y) S := by
    by_cases hr0 : r = 0
    · subst r
      ext x
      constructor
      · rintro ⟨hcoord, hsum⟩
        have hxzero : x = 0 := by
          funext i
          have hle : x i ≤ ∑ j, x j := by
            exact Finset.single_le_sum (s := Finset.univ) (f := fun j => x j)
              (fun j hj => hcoord j) (Finset.mem_univ i)
          exact le_antisymm (le_trans hle hsum) (hcoord i)
        refine ⟨0, ?_, ?_⟩
        · constructor
          · intro i
            simp
          · simp
        · simp [hxzero]
      · rintro ⟨y, hy, rfl⟩
        constructor
        · intro i
          simp
        · simp
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      ext x
      constructor
      · rintro ⟨hcoord, hsum⟩
        refine ⟨r⁻¹ • x, ?_, ?_⟩
        · constructor
          · intro i
            have hi := hcoord i
            simpa [Pi.smul_apply, smul_eq_mul] using
              mul_nonneg (inv_nonneg.mpr hrpos.le) hi
          · have hsum' : (∑ i, (r⁻¹ • x) i) = r⁻¹ * ∑ i, x i := by
              simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
            rw [hsum']
            calc
              r⁻¹ * ∑ i, x i ≤ r⁻¹ * r :=
                mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hrpos.le)
              _ = 1 := inv_mul_cancel₀ hr0
        · ext i
          simp only [Pi.smul_apply, smul_eq_mul]
          calc
            r * (r⁻¹ * x i) = (r * r⁻¹) * x i := by ring
            _ = x i := by rw [mul_inv_cancel₀ hr0]; ring
      · rintro ⟨y, hy, rfl⟩
        constructor
        · intro i
          simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hr (hy.1 i)
        · have hsum' : (∑ i, (r • y) i) = r * ∑ i, y i := by
            simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          rw [hsum']
          simpa [mul_one] using mul_le_mul_of_nonneg_left hy.2 hr
  change MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} = _
  rw [hset]
  change MeasureTheory.volume (r • S) = _
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg MeasureTheory.volume hr S]
  rw [ENNReal.ofReal_pow hr]
  simp [S, Module.finrank_pi, Fintype.card_fin]
