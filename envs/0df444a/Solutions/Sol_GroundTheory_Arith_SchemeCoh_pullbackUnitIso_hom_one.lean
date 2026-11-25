-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.pullbackUnitIso_hom_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:49:11.630321+00:00
-- url     : https://prove2.me/submissions/a1505e78-176d-4e35-8cde-e3b120a3df01

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
import Theorems.Thm_GroundTheory_Arith_Etale_openInclLE_left
import Theorems.Thm_GroundTheory_Arith_Etale_openIncl_left
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Etale.openInclLE_left
attribute [local simp] GroundTheory.Arith.Etale.openIncl_left



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res pullbackUnitApp_comp
  pullbackUnitApp_comp_hom pullbackUnitApp_bijective)
universe u
noncomputable section
variable {Y Z : Scheme.{u}}
set_option backward.isDefEq.respectTransparency.types false
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (f : Y ⟶ Z) :
    (pullbackUnitIso f).hom.app ⊤
      (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤)) = unitOne Y ⊤ := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (fun ψ => ψ.val.app (op ⊤) (1 : Z.ringCatSheaf.obj.obj (op ⊤))) h
  simp only [SheafOfModules.unitToPushforwardObjUnit_val_app_apply, map_one] at h'
  exact h'
end GroundTheory.Arith.SchemeCoh
