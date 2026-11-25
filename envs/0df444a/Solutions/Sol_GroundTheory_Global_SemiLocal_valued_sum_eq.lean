-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.valued_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:36:02.49896+00:00
-- url     : https://prove2.me/submissions/c62daff0-cb90-4145-8acb-0e761a69e4db

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_completion
import Theorems.Thm_GroundTheory_Global_SemiLocal_valued_sum_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]
omit [Fintype ι]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution [Fintype ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (c : ι → v.adicCompletion K) (j0 : ι) (hj0 : ∀ j, Valued.v (c j) ≤ Valued.v (c j0)) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) =
      Valued.v (c j0) ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  have he0 : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  by_cases h0 : c j0 = 0
  · have hc : ∀ j, c j = 0 := fun j ↦ by
      have := hj0 j
      rw [h0, map_zero] at this
      exact (Valuation.zero_iff _).1 (le_antisymm this zero_le)
    simp [hc, zero_pow he0]
  · have hv0 : Valued.v (c j0) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    set d : ι → v.adicCompletion K := fun j ↦ c j * (c j0)⁻¹ with hd_def
    have hcd : ∀ j, c j = c j0 * d j := fun j ↦ by
      simp only [hd_def]
      rw [mul_comm (c j), ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
    have hd : ∀ j, Valued.v (d j) ≤ 1 := fun j ↦ by
      simp only [hd_def, map_mul, map_inv₀]
      rw [← mul_inv_cancel₀ hv0]
      exact mul_le_mul_left (hj0 j) _
    have hdj0 : Valued.v (d j0) = 1 := by simp [hd_def, mul_inv_cancel₀ h0]
    have : ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
        algebraMap (𝓞 L) (w.adicCompletion L) (ω j) =
        algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j0) *
          ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
            algebraMap (𝓞 L) (w.adicCompletion L) (ω j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hcd j, map_mul, mul_assoc]
    rw [this, map_mul, valued_algebraMap_completion, valued_sum_eq_one v w ω hω d hd j0 hdj0,
      mul_one]
end GroundTheory.Global.SemiLocal
