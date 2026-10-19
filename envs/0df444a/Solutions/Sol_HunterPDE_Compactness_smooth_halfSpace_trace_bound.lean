-- Prove2me | solution 1 for HunterPDE.Compactness.smooth_halfSpace_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T09:57:24.44999+00:00
-- url     : https://prove2.me/submissions/7b03066b-7070-4036-8493-8e7528dc761a

import Theorems.Thm_HunterPDE_Compactness_memLp_boundary_of_continuousOn_compact
import Theorems.Thm_HunterPDE_Compactness_smooth_halfSpace_trace_power_le_normal_energy

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ m : ℕ,
      ∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        IsSmoothCompactClosedHalfSpace f →
          MemLp (fun x' => f (boundaryPoint x')) p volume ∧
          eLpNorm (fun x' => f (boundaryPoint x')) p volume ≤
            (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  let C : ℝ≥0 := p.toNNReal ^ (1 / p.toReal)
  refine ⟨C, fun m f hf => ⟨memLp_boundary_of_continuousOn_compact p f
    hf.1.continuousOn hf.2, ?_⟩⟩
  let E : (Fin (m + 1) → ℕ) → ℝ≥0∞ := fun α =>
    eLpNorm (HunterPDE.Shared.weakDeriv (upperHalfSpace m) α f)
      p (volume.restrict (upperHalfSpace m)) ^ p.toReal
  let α : Fin (m + 1) → ℕ := Pi.single (Fin.last m) 1
  have hα0 : (0 : Fin (m + 1) → ℕ) ≠ α := by
    intro h
    have he := congrFun h (Fin.last m)
    simp [α] at he
  have hzero : (0 : Fin (m + 1) → ℕ) ∈ multiIndicesLe (m + 1) 1 := by
    simp [multiIndicesLe]
  have hnormal : α ∈ multiIndicesLe (m + 1) 1 := by
    simp [multiIndicesLe, α, Fintype.mem_piFinset]
    intro a
    by_cases ha : a = Fin.last m <;> simp [ha]
  have hsub : ({0, α} : Finset (Fin (m + 1) → ℕ)) ⊆ multiIndicesLe (m + 1) 1 :=
    by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
      And.intro hzero hnormal
  have henergy : E 0 + E α ≤ ∑ β ∈ multiIndicesLe (m + 1) 1, E β := by
    simpa only [Finset.sum_pair hα0] using
      (Finset.sum_le_sum_of_subset hsub :
        ∑ β ∈ ({0, α} : Finset (Fin (m + 1) → ℕ)), E β ≤
          ∑ β ∈ multiIndicesLe (m + 1) 1, E β)
  have hpower := smooth_halfSpace_trace_power_le_normal_energy p hp hp' f hf
  have htotal : eLpNorm (fun x' => f (boundaryPoint x')) p volume ^ p.toReal ≤
      ENNReal.ofReal p.toReal * (∑ β ∈ multiIndicesLe (m + 1) 1, E β) :=
    hpower.trans (mul_le_mul_right henergy _)
  have hroot := ENNReal.rpow_le_rpow htotal (le_of_lt (one_div_pos.mpr hpr))
  have hcancel : p.toReal * (1 / p.toReal) = 1 := mul_one_div_cancel hpr.ne'
  rw [← ENNReal.rpow_mul, hcancel, ENNReal.rpow_one, ENNReal.mul_rpow_of_nonneg]
    at hroot
  · simpa only [sobolevNorm, if_neg hp', C,
      ENNReal.coe_rpow_of_nonneg _ (le_of_lt (one_div_pos.mpr hpr)),
      ENNReal.coe_toNNReal hp', ENNReal.ofReal_toReal hp'] using hroot
  · exact le_of_lt (one_div_pos.mpr hpr)
