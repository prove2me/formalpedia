-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.ev_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:52.348826+00:00
-- url     : https://prove2.me/submissions/7f6ee952-6805-4edb-9fd1-789ae9f7d30f

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
theorem _root_.solution (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (φ : Y ⟶ Y') (V : Y'.Opens)
    (W : Y.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ V) (u : Γ(Y', V)) :
    _root_.GlobalTheory.SS.WtRat.ev g W h ((φ.appLE V W e).hom u) =
      _root_.GlobalTheory.SS.WtRat.ev (g ≫ φ) V h' u := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]
end _root_.GlobalTheory.SS.WtRat
end GlobalTheory.SS.WtRat
