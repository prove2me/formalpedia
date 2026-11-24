-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.Basis.span_map_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:45.578781+00:00
-- url     : https://prove2.me/submissions/8061c888-b4ee-4d63-a93d-a20489b36a9e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.Basis
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']
namespace GlobalTheory.CatCoh.Desc.Basis
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) {S S' : C} (u : S ⟶ S') {n : ℕ}
    {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by
  have := congrArg (Ideal.map (mp F u)) hb
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
end GlobalTheory.CatCoh.Desc.Basis
