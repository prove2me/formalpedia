-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isBasisOn_pullbackUnitApp_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:17:44.413244+00:00
-- url     : https://prove2.me/submissions/93569ec5-bf06-41a1-81d7-254a7f325b2c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitIso_hom_one
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_res
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_map_iso
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res pullbackUnitApp_comp
  pullbackUnitApp_comp_hom pullbackUnitApp_bijective)
universe u
noncomputable section
variable {Y Z : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (f : Y ⟶ Z) :
    IsBasisOn ((preMod Y).obj ((Scheme.Modules.pullback f).obj
      (SheafOfModules.unit Z.ringCatSheaf))) ⊤
      (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤)) := by
  have hb : IsBasisOn ((preMod Y).obj (SheafOfModules.unit Y.ringCatSheaf)) ⊤ (unitOne Y ⊤) :=
    isBasisOn_one ⊤
  have h2 := hb.map_iso (pullbackUnitIso f).symm
  have hx : ((preMod Y).map (pullbackUnitIso f).symm.hom).app (op ⊤)
      ((pullbackUnitIso f).hom.app ⊤
        (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤))) =
      pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤) := by
    have e2 := congrArg (fun φ => (Scheme.Modules.Hom.app φ ⊤).hom
      (pullbackUnitApp f (SheafOfModules.unit Z.ringCatSheaf) ⊤ (unitOne Z ⊤)))
      (pullbackUnitIso f).hom_inv_id
    exact e2
  rw [← pullbackUnitIso_hom_one f, hx] at h2
  exact h2
end GroundTheory.Arith.SchemeCoh
