-- Prove2me | solution 1 for GlobalTheory.FibreFlat.flatOver_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:07.853124+00:00
-- url     : https://prove2.me/submissions/b9c1b7cc-2406-429b-895c-c927ee9a7c42

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
theorem _root_.solution {X Y : Over S} (φ : X ⟶ Y) (s : S' ⟶ S)
    (H : Flat ((Over.pullback s).map φ).left) : FlatOver φ.left Y.hom s := by
  intro W Z a b j h sq e
  have sq0 : IsPullback (pullback.fst X.hom s) ((Over.pullback s).map φ).left φ.left
      (pullback.fst Y.hom s) := by
    have e1 : ((Over.pullback s).map φ).left ≫ pullback.fst Y.hom s =
        pullback.fst X.hom s ≫ φ.left := pullback.lift_fst _ _ _
    have e2 : ((Over.pullback s).map φ).left ≫ pullback.snd Y.hom s =
        pullback.snd X.hom s := pullback.lift_snd _ _ _
    refine IsPullback.of_bot ?_ e1.symm (IsPullback.of_hasPullback Y.hom s)
    rw [e2, Over.w]
    exact IsPullback.of_hasPullback X.hom s
  let j' : Z ⟶ pullback Y.hom s := pullback.lift j h e
  have hj : j' ≫ pullback.fst Y.hom s = j := pullback.lift_fst _ _ _
  let a' := sq0.lift a (b ≫ j') (by rw [Category.assoc, hj]; exact sq.w)
  have sq1 : IsPullback a' b ((Over.pullback s).map φ).left j' :=
    IsPullback.of_right (by rw [hj, sq0.lift_fst]; exact sq) (sq0.lift_snd _ _ _) sq0
  exact MorphismProperty.of_isPullback sq1 H
end GlobalTheory.FibreFlat
