-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.ev_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:16.000512+00:00
-- url     : https://prove2.me/submissions/7eb7683e-e882-4b3f-9da1-fafda1952230

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
theorem _root_.solution (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(Y, ⊤)) :
    _root_.GlobalTheory.SS.WtRat.ev g ⊤ h u =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl
end _root_.GlobalTheory.SS.WtRat
end GlobalTheory.SS.WtRat
