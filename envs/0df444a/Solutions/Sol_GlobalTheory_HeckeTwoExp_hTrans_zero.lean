-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.hTrans_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:24:44.259707+00:00
-- url     : https://prove2.me/submissions/50968d31-a8bb-4d76-8739-be9a07e1a441

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformSigmaZeroEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinWeightTwoQSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinWeightTwoQExpansion
import Theorems.Thm_GlobalTheory_HeckeTwoExp_hTrans_zero_neg
import Theorems.Thm_GlobalTheory_T_heckePhiFourierTransform_sigma_zero_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution (ν y : ℝ) (hy : y ≠ 0) :
    hTrans 0 ν y = if 0 < ν * y then
      -4 * (Real.pi : ℂ) ^ 2 * ((|ν| : ℝ) : ℂ) * ((Real.exp (-(2 * Real.pi * (ν * y))) : ℝ) : ℂ) else 0 := by
  rcases hy.lt_or_gt with h | h
  · have e := hTrans_zero_neg (-ν) y
    rw [neg_neg] at e
    rw [← e, GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq _ _ (neg_pos.2 h)]
    by_cases hν : 0 < -ν
    · have h2 : 0 < ν * y := by nlinarith
      rw [if_pos hν, if_pos h2, abs_of_neg (by linarith : ν < 0),
        show -(2 * Real.pi * -ν * -y) = -(2 * Real.pi * (ν * y)) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]
  · rw [GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq _ _ h]
    by_cases hν : 0 < ν
    · have h2 : 0 < ν * y := mul_pos hν h
      rw [if_pos hν, if_pos h2, abs_of_pos hν, show 2 * Real.pi * ν * y = 2 * Real.pi * (ν * y) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]
end GlobalTheory.HeckeTwoExp
