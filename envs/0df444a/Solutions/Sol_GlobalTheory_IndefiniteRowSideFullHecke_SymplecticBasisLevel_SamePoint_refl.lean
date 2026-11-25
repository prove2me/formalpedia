-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel.SamePoint.refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:53:48.998999+00:00
-- url     : https://prove2.me/submissions/a95bdee5-4ac4-4c19-86ed-85016de817fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_SymplecticBasisLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
namespace SamePoint
theorem _root_.solution (D' : Datum H) (l : Level H) {g : ℕ} (P : D'.La →+ (Fin g → ℂ)) : SamePoint D' l P P :=
  ⟨LinearEquiv.refl _ _, LinearEquiv.refl _ _,
    ⟨fun _ _ => rfl, fun _ => by simp, fun _ => ⟨0, by simp⟩⟩, fun _ => rfl⟩
end SamePoint
end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
