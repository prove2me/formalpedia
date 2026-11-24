-- Prove2me | solution 1 for GlobalTheory.UnramifiedEndFlat.residueFieldMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:30.643908+00:00
-- url     : https://prove2.me/submissions/8c9b69ec-75d2-4b76-8c6d-3edc77b6d7f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd

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
open GlobalTheory.UnramifiedEndFlat
open IsLocalRing
namespace GlobalTheory.UnramifiedEndFlat
theorem _root_.solution {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ g)] (x : X)
    (hx : IsClosed {x}) : Function.Surjective (f.residueFieldMap x) := by
  have h : (residueFieldIsoBase (f ≫ g) x hx).inv =
      Spec.preimage (Y.fromSpecResidueField (f x) ≫ g) ≫ f.residueFieldMap x := by
    apply Spec.map_injective
    simp
  have h2 : Function.Surjective (residueFieldIsoBase (f ≫ g) x hx).inv :=
    (ConcreteCategory.bijective_of_isIso _).2
  rw [h] at h2
  exact Function.Surjective.of_comp (g := Spec.preimage (Y.fromSpecResidueField (f x) ≫ g)) h2
end GlobalTheory.UnramifiedEndFlat
