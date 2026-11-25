-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.IsCompleteLocalNormal.pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:50:11.290366+00:00
-- url     : https://prove2.me/submissions/4792d49d-9d59-477f-8846-f4f9a55aeaf1

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
namespace IsCompleteLocalNormal
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsCompleteLocalNormal R) : IsAdicNormalPair R (IsLocalRing.maximalIdeal R) :=
  ⟨h.noeth, h.normal, h.complete⟩
end IsCompleteLocalNormal
end GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings
