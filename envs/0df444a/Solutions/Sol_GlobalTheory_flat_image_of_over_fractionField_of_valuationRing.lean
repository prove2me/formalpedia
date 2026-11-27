-- Prove2me | solution 1 for GlobalTheory.flat_image_of_over_fractionField_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:33.212469+00:00
-- url     : https://prove2.me/submissions/c9a215bf-07ec-4a51-a017-49a4d0716db0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Theorems.Thm_GlobalTheory_flat_image_of_valuationRing

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
theorem _root_.solution {O K : Type u} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (s : P ⟶ Spec (.of O))
    (s' : W ⟶ Spec (.of K))
    (h : s' ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) = j ≫ s) [QuasiCompact j] :
    Flat (j.imageι ≫ s) :=
  have := flat_of_over_fractionField (j ≫ s) s' h
  flat_image_of_valuationRing j s
end GlobalTheory
