-- Prove2me | solution 1 for GlobalTheory.GaussExt.UnitIdx.isIntegral_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:10:06.644678+00:00
-- url     : https://prove2.me/submissions/dbccf0c4-269a-47b4-8913-715f17813c9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaussianExtensionUnitsQuotUnits

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
open GlobalTheory GlobalTheory.GaussExt GlobalTheory.GaussExt.UnitIdx
variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
namespace GlobalTheory.GaussExt.UnitIdx
theorem _root_.solution {x : Ext F} (hx : IsIntegral ℤ x) : IsIntegral ℤ (conj F x) :=
  hx.map ((conj F).toRingHom.toIntAlgHom)
end GlobalTheory.GaussExt.UnitIdx
