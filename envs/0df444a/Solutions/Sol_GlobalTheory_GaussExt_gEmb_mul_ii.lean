-- Prove2me | solution 1 for GlobalTheory.GaussExt.gEmb_mul_ii
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:10:08.803541+00:00
-- url     : https://prove2.me/submissions/4af0aa9d-15f3-4aed-bdb0-9667aadc924e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgebraNormRatGaussianExtensionOfPair
import Theorems.Thm_GlobalTheory_GaussExt_basisOneI_zero
import Theorems.Thm_GlobalTheory_GaussExt_basisOneI_one
import Theorems.Thm_GlobalTheory_GaussExt_ii_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.GaussExt
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.GaussExt
theorem _root_.solution (a b : F) : gEmb F (a, b) * ii F = (-b) • basisOneI F 0 + a • basisOneI F 1 := by
  simp only [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def, map_neg]
  linear_combination (algebraMap F (Ext F) b) * ii_sq F
end GlobalTheory.GaussExt
