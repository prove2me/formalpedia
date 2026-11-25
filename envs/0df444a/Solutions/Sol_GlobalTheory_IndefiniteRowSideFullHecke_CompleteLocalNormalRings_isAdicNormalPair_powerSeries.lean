-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.isAdicNormalPair_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:54:14.292946+00:00
-- url     : https://prove2.me/submissions/578a671f-d935-4ebe-a0b9-9ab9fdafdaed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
namespace GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] :
    IsAdicNormalPair (PowerSeries O) (Ideal.span {PowerSeries.X}) :=
  ⟨inferInstance, inferInstance, inferInstance⟩
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
