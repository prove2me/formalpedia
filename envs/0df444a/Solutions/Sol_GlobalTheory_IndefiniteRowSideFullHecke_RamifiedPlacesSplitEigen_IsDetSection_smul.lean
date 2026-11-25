-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen.IsDetSection.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:57:23.290618+00:00
-- url     : https://prove2.me/submissions/6b6a36e3-a5f2-4191-a4f1-140e8defbe32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_RamifiedPlacesSplitEigen

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
namespace IsDetSection
theorem _root_.solution {Y : Model Xo c β} {τ : E →+* ℂ} {f : Rule Y} (hf : IsDetSection Y τ f) (a : c.F) :
    IsDetSection Y τ (fun R _ φ x v w => φ a * f R φ x v w) := by
  refine ⟨fun R _ φ x v v' w w' M N h h' hM hN => ?_, fun R R' _ _ g φ x v w v' w' h h' hv hw => ?_⟩
  · simp only [_root_.mul_assoc, hf.1 R φ x v v' w w' M N h h' hM hN]
  · simp only [hf.2 R R' g φ x v w v' w' h h' hv hw, map_mul, RingHom.comp_apply]
end IsDetSection
end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
