-- Prove2me | solution 1 for GlobalTheory.FibreFlat.FlatOver.source
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:25.223171+00:00
-- url     : https://prove2.me/submissions/4a3c0cba-9258-494d-95cc-2bc2e49b9c6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr

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
open TensorProduct IsLocalRing
open GlobalTheory
open GlobalTheory.FibreFlat
variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ S} {s : S' ⟶ S}
namespace GlobalTheory.FibreFlat
namespace FlatOver
theorem _root_.solution (H : FlatOver f g s) {X' : Scheme.{0}} (i : X' ⟶ X) [Flat i] :
    FlatOver (i ≫ f) g s := by
  intro W Z a b j h sq e
  have h1 := H _ _ j h (IsPullback.of_hasPullback f j) e
  let c : W ⟶ pullback f j := pullback.lift (a ≫ i) b (by simpa using sq.w)
  have hc : c ≫ pullback.snd f j = b := pullback.lift_snd _ _ _
  have sq2 : IsPullback a c i (pullback.fst f j) :=
    IsPullback.of_bot (by rw [hc]; exact sq) (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback f j)
  have h2 : Flat c := MorphismProperty.of_isPullback sq2 ‹Flat i›
  rw [← hc]
  infer_instance
end FlatOver
end GlobalTheory.FibreFlat
