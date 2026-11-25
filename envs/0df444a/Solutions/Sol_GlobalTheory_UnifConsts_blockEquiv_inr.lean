-- Prove2me | solution 1 for GlobalTheory.UnifConsts.blockEquiv_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:28.359207+00:00
-- url     : https://prove2.me/submissions/4854bcc7-ba53-47fd-860c-a56115dc9da2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydisc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
open GlobalTheory GlobalTheory.UnifConsts
namespace GlobalTheory.UnifConsts
theorem _root_.solution (g rk : ℕ) (i) : ¬ (blockEquiv g rk (Sum.inr i)).val < rk :=
  ((Fintype.equivFin {j : Fin g // ¬ j.val < rk}).symm i).2
end GlobalTheory.UnifConsts
