-- Prove2me | solution 1 for GroundTheory.Global.complexFourier_complexGaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:54.778989+00:00
-- url     : https://prove2.me/submissions/18ee04ac-80ce-4eb9-945e-4df1dcf8cd95

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Theorems.Thm_GroundTheory_Global_complexGaussian_natCast
import Theorems.Thm_GroundTheory_Global_complexGaussian_neg_natCast
import Theorems.Thm_GroundTheory_Global_complexFourier_pow_mul_gaussian
import Theorems.Thm_GroundTheory_Global_complexFourier_conj_pow_mul_gaussian
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (m : ℤ) :
    complexFourier (complexGaussian m) = fun w ↦ (-I) ^ m.natAbs * complexGaussian (-m) w := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [complexGaussian_natCast, complexFourier_pow_mul_gaussian, complexGaussian_neg_natCast]
    simp
  · rw [complexGaussian_neg_natCast, complexFourier_conj_pow_mul_gaussian, neg_neg,
      complexGaussian_natCast]
    simp
end GroundTheory.Global
