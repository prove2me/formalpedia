-- Prove2me | solution 1 for GlobalTheory.HostModel.witData_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:04.504977+00:00
-- url     : https://prove2.me/submissions/42ca55ce-2ca2-4326-a8bc-a2f55f8dc687

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
import Theorems.Thm_GlobalTheory_HostModel_witData_of_isometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)
namespace GlobalTheory.HostModel
theorem _root_.solution : WitData (arcIn c k bF) (witP c k bF) (witAct c k bF) (witMap c k bF) (witMap_eSec c k bF)
    (witIso c k bF) (LinearEquiv.neg (𝓞 E) : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) :=
  witData_of_isometry c k bF _ fun y => by
    rw [LinearEquiv.neg_apply, arcIn_be_apply, arcIn_be_apply, map_neg, map_neg, LinearMap.neg_apply, neg_neg]
end GlobalTheory.HostModel
