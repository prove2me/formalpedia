-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.isBaseRing_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:53:39.558804+00:00
-- url     : https://prove2.me/submissions/778dbb54-40ff-48ca-b448-6b71a831bdae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_FibreFramesOnModels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
theorem _root_.solution (c : Coeff l) (W : ValuationSubring ℂ) : IsBaseRing (c.V W).subtype := by
  refine ⟨Subtype.val_injective, fun x hx => ?_⟩
  have h : IsIntegral (c.V W) x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
  exact ⟨y, hy⟩
end GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
