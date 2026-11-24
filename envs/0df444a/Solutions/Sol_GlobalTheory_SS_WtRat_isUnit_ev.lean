-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.isUnit_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:14.625612+00:00
-- url     : https://prove2.me/submissions/3f51b4bc-2ff6-409d-9439-42cd9ac0c31a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.WtRat
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}}
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}} in
private theorem isUnit_of_basicOpen_covers_scheme (X : Scheme) (s : Γ(X, ⊤))
    (hb : ⊤ ≤ X.basicOpen s) : IsUnit s := by
  have := (RingedSpace.isUnit_res_basicOpen _ s).map
    (ConcreteCategory.hom (X.presheaf.map (homOfLE hb).op))
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
  erw [Subsingleton.elim (_ ≫ _) (𝟙 (Opposite.op (⊤ : X.Opens))),
    CategoryTheory.Functor.map_id] at this
  simpa using this
end GlobalTheory.SS.WtRat
end
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}}
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}}
namespace GlobalTheory.SS.WtRat
namespace _root_.GlobalTheory.SS.WtRat
theorem _root_.solution (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) (hu : ⊤ ≤ g ⁻¹ᵁ Y.basicOpen u) :
    IsUnit (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by
  have hb : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R).basicOpen ((g.appLE V ⊤ h).hom u) := by
    have := Scheme.basicOpen_appLE g ⊤ V h u
    erw [this]
    exact le_inf le_rfl hu
  exact (isUnit_of_basicOpen_covers_scheme _ _ hb).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
end _root_.GlobalTheory.SS.WtRat
end GlobalTheory.SS.WtRat
