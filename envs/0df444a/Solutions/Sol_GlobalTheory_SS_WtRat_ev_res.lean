-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.ev_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:53.164385+00:00
-- url     : https://prove2.me/submissions/eb00ffc8-9ab6-4ebe-9aea-d622bddbfa05

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
theorem _root_.solution (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) {V W : Y.Opens} (e : W ≤ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev g W h ((Y.presheaf.map (homOfLE e).op).hom u) =
      _root_.GlobalTheory.SS.WtRat.ev g V h' u := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE]
end _root_.GlobalTheory.SS.WtRat
end GlobalTheory.SS.WtRat
