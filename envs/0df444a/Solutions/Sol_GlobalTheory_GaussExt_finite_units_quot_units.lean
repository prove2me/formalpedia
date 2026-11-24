-- Prove2me | solution 1 for GlobalTheory.GaussExt.finite_units_quot_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:56.77339+00:00
-- url     : https://prove2.me/submissions/16d320ce-6b44-404d-a78b-512535e5a089

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaussianExtensionUnitsQuotUnits
import Theorems.Thm_GlobalTheory_GaussExt_UnitIdx_finite_quot

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
namespace GlobalTheory.GaussExt
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸
      (Units.map (algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) :=
  fun F _ _ _ => GlobalTheory.GaussExt.UnitIdx.finite_quot F
end GlobalTheory.GaussExt
