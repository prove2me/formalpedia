-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isBasisOn_pullbackUnitApp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:34:07.20415+00:00
-- url     : https://prove2.me/submissions/7d8f740f-f5e5-4052-9821-26996e78ae69

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_pullbackUnitApp_of_top
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_pullbackUnitApp_iff
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_of_pullbackUnitApp_comp
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
theorem _root_.solution (f : Y ⟶ Z) {N : Z.Modules} {W : Z.Opens} {t : Γ(N, W)}
    (ht : IsBasisOn ((preMod Z).obj N) W t) :
    IsBasisOn ((preMod Y).obj ((Scheme.Modules.pullback f).obj N)) (f ⁻¹ᵁ W)
      (pullbackUnitApp f N W t) := by

  have h1 : IsBasisOn ((preMod W.toScheme).obj ((Scheme.Modules.pullback W.ι).obj N)) (W.ι ⁻¹ᵁ W)
      (pullbackUnitApp W.ι N W t) :=
    (isBasisOn_pullbackUnitApp_iff W.ι N (by rw [Scheme.Opens.opensRange_ι]) t).2 ht

  have h2 := isBasisOn_pullbackUnitApp_of_top (f ∣_ W) (by rw [Scheme.Opens.ι_preimage_self]) h1
  have h3 := isBasisOn_of_pullbackUnitApp_comp (f ∣_ W) W.ι N W t h2
  rw [morphismRestrict_ι] at h3
  have h4 := isBasisOn_pullbackUnitApp_comp (f ⁻¹ᵁ W).ι f N W t h3
  exact (isBasisOn_pullbackUnitApp_iff (f ⁻¹ᵁ W).ι _ (by rw [Scheme.Opens.opensRange_ι]) _).1 h4
end GroundTheory.Arith.SchemeCoh
