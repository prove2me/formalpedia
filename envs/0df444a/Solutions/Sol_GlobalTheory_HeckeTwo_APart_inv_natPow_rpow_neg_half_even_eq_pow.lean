-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.APart.inv_natPow_rpow_neg_half_even_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:20:35.590237+00:00
-- url     : https://prove2.me/submissions/6dbca241-fe90-4745-a63c-a5c302db12f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn

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
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.APart
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwo.APart
theorem _root_.solution {x : ℝ} (hx : 0 < x) (t : ℝ) : x ^ (-(2 + 2 * t)) = x⁻¹ ^ 2 * x ^ (-2 * t) := by
  rw [show -(2 + 2 * t) = -(2 : ℝ) + -2 * t by ring, Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_two, inv_pow]
end GlobalTheory.HeckeTwo.APart
