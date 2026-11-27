-- Prove2me | solution 1 for GlobalTheory.range_toImage_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:27.204054+00:00
-- url     : https://prove2.me/submissions/3eab5441-1b91-409c-a6ae-41dec39bc751

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
variable {W P T' T Z : Scheme.{u}} (j : W ⟶ P)
namespace GlobalTheory
theorem _root_.solution {P' : Scheme.{u}} (c : W ⟶ P') (u : P' ⟶ P)
    [IsClosedImmersion c] [Flat u] [Mono u] (h : c ≫ u = j) [QuasiCompact j] :
    Set.range j.toImage = j.imageι ⁻¹' Set.range u := by
  have H := isPullback_toImage_of_isClosedImmersion j c u h
  rw [← H.isoPullback_hom_snd, ← Scheme.Pullback.range_snd, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, H.isoPullback.hom.surjective.range_eq, Set.image_univ]
end GlobalTheory
