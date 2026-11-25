-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel.incl_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:53:56.24363+00:00
-- url     : https://prove2.me/submissions/dca0e698-3f20-4d11-a44a-3c3ae6f58666

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
theorem _root_.solution (l : Level H) : (KA l).val.toRingHom (baseKA l).ρ = H.rt0 := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
