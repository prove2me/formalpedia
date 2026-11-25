-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isBasisOn_pullbackUnitApp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:43:48.58406+00:00
-- url     : https://prove2.me/submissions/6811bd08-6e3d-4727-910b-979582e1ce1a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_res
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_map_iso


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
theorem _root_.solution {T : Scheme.{u}} (c : T ⟶ Y) (d : Y ⟶ Z) (N : Z.Modules)
    (O : Z.Opens) (t : Γ(N, O))
    (h : IsBasisOn ((preMod T).obj ((Scheme.Modules.pullback (c ≫ d)).obj N)) ((c ≫ d) ⁻¹ᵁ O)
      (pullbackUnitApp (c ≫ d) N O t)) :
    IsBasisOn ((preMod T).obj ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback d).obj N)))
      (c ⁻¹ᵁ (d ⁻¹ᵁ O)) (pullbackUnitApp c _ (d ⁻¹ᵁ O) (pullbackUnitApp d N O t)) := by
  have h2 := h.map_iso ((Scheme.Modules.pullbackComp c d).app N).symm
  have e := GroundTheory.Arith.Etale.pullbackUnitApp_comp c d N O t
  change IsBasisOn _ _ (((Scheme.Modules.pullbackComp c d).inv.app N).app ((c ≫ d) ⁻¹ᵁ O)
    (pullbackUnitApp (c ≫ d) N O t)) at h2
  rw [e] at h2
  exact h2
end GroundTheory.Arith.SchemeCoh
