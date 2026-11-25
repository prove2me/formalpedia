-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.pullbackUnitApp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:00.763388+00:00
-- url     : https://prove2.me/submissions/a9b81845-c2a1-4f86-ac91-461e0e29fff4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_res
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_smul


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
theorem _root_.solution (f : Y ⟶ Z) (N : Z.Modules) (O : Z.Opens) (r : Γ(Z, O))
    (n : Γ(N, O)) : pullbackUnitApp f N O (r • n) = f.app O r • pullbackUnitApp f N O n :=
  Scheme.Modules.Hom.app_smul _ r n
end GroundTheory.Arith.SchemeCoh
