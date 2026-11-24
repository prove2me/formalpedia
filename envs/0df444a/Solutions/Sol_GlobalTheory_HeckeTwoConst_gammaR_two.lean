-- Prove2me | solution 1 for GlobalTheory.HeckeTwoConst.gammaR_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:24:47.69283+00:00
-- url     : https://prove2.me/submissions/571a7f38-5c08-4466-920b-59db506965e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoConstantTermEqPartialZetaNegOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwoConst
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoConst
theorem _root_.solution : Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
  rw [Gammaℝ_def, show (2 : ℂ) / 2 = 1 by norm_num, show -(2 : ℂ) / 2 = -1 by norm_num, Complex.Gamma_one, cpow_neg_one,
    mul_one]
end GlobalTheory.HeckeTwoConst
