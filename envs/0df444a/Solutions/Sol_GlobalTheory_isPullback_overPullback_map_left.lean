-- Prove2me | solution 1 for GlobalTheory.isPullback_overPullback_map_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:05.991597+00:00
-- url     : https://prove2.me/submissions/835b8094-a2a2-4287-aafa-b2d5e7985e82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S}
    (φ : X ⟶ Y) :
    IsPullback ((Over.pullback f).map φ).left (pullback.fst X.hom f) (pullback.fst Y.hom f)
      φ.left := by
  refine IsPullback.flip (IsPullback.of_bot (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) (h₃₁ := f)
    ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback Y.hom f))
  have h₁ : ((Over.pullback f).map φ).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
    pullback.lift_snd _ _ _
  rw [h₁, Over.w φ]
  exact IsPullback.of_hasPullback X.hom f
end GlobalTheory
