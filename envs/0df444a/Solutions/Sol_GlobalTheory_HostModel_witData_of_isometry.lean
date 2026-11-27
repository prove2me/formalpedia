-- Prove2me | solution 1 for GlobalTheory.HostModel.witData_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:34:03.665792+00:00
-- url     : https://prove2.me/submissions/f3cfe6e2-c99a-4fea-9e39-3cec179a16bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
import Theorems.Thm_GlobalTheory_ToricData_baseIso_isGen
import Theorems.Thm_GlobalTheory_ToricData_baseIso_rig
import Theorems.Thm_GlobalTheory_ToricData_baseMap_pb
import Theorems.Thm_GlobalTheory_ToricData_c_baseMap
import Theorems.Thm_GlobalTheory_ToricData_genRel_arcData_psi


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
theorem _root_.solution (e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E)
    (h : ∀ y : 𝓞 E, (arcIn c k bF).be (e y) (e y) = (arcIn c k bF).be y y) :
    WitData (arcIn c k bF) (witP c k bF) (witAct c k bF) (witMap c k bF) (witMap_eSec c k bF) (witIso c k bF) e := by
  refine ⟨baseMap_pb _ _ _, baseIso_isGen _ _ _, baseIso_rig _ _ _ _, fun _ => end_baseMap _ _ _ _ _,
    fun _ => c_baseMap _ _ _ _ _, ?_⟩
  intro F _ _ _ _ u hF hu y
  exact genRel_arcData_psi (X := 𝓞 E) k _ _ _ _ F u hF hu (e y) y (h y)
end GlobalTheory.HostModel
