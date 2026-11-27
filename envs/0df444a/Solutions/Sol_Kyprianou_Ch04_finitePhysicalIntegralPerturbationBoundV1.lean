-- Prove2me | solution 1 for Kyprianou.Ch04.finitePhysicalIntegralPerturbationBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:12:16.257316+00:00
-- url     : https://prove2.me/submissions/46bc2da9-d53f-47ab-ad51-788e29226d55

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
open MeasureTheory Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The large-jump integral perturbation is bounded by the finite absolute mark ledger. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j H L : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ r ≤ T, 0 < r → |H r - L r| ≤ d) :
    ∀ t ≤ T, |(∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * H z.1.toNNReal ∂ R) -
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * L z.1.toNNReal ∂ R)| ≤ (∑ r ∈ S, |j r|) * d := by
  intro t ht
  let D : Set (ℝ × ℝ) := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}
  let A : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  have hA : MeasurableSet A := measurableSet_Icc.prod
    (measurableSet_le measurable_const measurable_id.abs)
  have hAD : A ⊆ D := by
    intro z hz
    exact ⟨⟨hz.1.1,hz.1.2.trans (by exact_mod_cast ht)⟩,
      (show (1/2 : ℝ) < 1 by norm_num).trans_le hz.2⟩
  have hH := Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR
    A hA hAD (fun z => z.2 * H z.1.toNNReal)
  have hL := Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR
    A hA hAD (fun z => z.2 * L z.1.toNNReal)
  change |(∫ z in A, z.2 * H z.1.toNNReal ∂ R) -
    (∫ z in A, z.2 * L z.1.toNNReal ∂ R)| ≤ _
  rw [hH,hL,← Finset.sum_sub_distrib]
  simp only [Real.toNNReal_coe]
  calc
    _ ≤ ∑ r ∈ S, |(if ((r : ℝ),j r) ∈ A then j r * H r else 0) -
      (if ((r : ℝ),j r) ∈ A then j r * L r else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ S, (|j r| * d) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hz : ((r : ℝ),j r) ∈ A
      · rw [if_pos hz,if_pos hz,← mul_sub,abs_mul]
        exact mul_le_mul_of_nonneg_left (h r (hS r hr).2 (hS r hr).1) (abs_nonneg _)
      · simp [hz,mul_nonneg (abs_nonneg (j r)) hd]
    _ = _ := by rw [Finset.sum_mul]
