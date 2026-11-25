-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.pullbackUnitApp_naturality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:43:50.49282+00:00
-- url     : https://prove2.me/submissions/6d777189-bf1d-4aa1-9dcb-f56495e62eb2

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
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (f : Y ⟶ Z) {N N' : Z.Modules} (φ : N ⟶ N') (O : Z.Opens)
    (n : Γ(N, O)) :
    ((Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ O) (pullbackUnitApp f N O n) =
      pullbackUnitApp f N' O (φ.app O n) := by
  have := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ
  have h := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ O).hom n) this
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h
  exact h.symm
end GroundTheory.Arith.SchemeCoh
