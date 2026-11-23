-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.ev_spMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:06.707805+00:00
-- url     : https://prove2.me/submissions/2dc4bf69-e206-44f7-a1ef-19607da9b663

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Theorems.Thm_GlobalTheory_SS_WtRat_ev_appLE
import Theorems.Thm_GlobalTheory_SS_WtRat_ev_top

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
theorem _root_.solution (σ : R →+* R') (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) V h' u =
      σ (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by
  rw [← _root_.GlobalTheory.SS.WtRat.ev_appLE (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) g V ⊤ h le_top h' u]
  erw [_root_.GlobalTheory.SS.WtRat.ev_top]
  exact congrArg (fun f => CommRingCat.Hom.hom f ((g.appLE V ⊤ h).hom u))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))
end _root_.GlobalTheory.SS.WtRat
end GlobalTheory.SS.WtRat
