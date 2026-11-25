-- Prove2me | solution 1 for GlobalTheory.HodgeGramLocal.hasDerivAt_locLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:30.433387+00:00
-- url     : https://prove2.me/submissions/d8716ba0-5b21-42ea-b033-beabb1b13e54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeGramLocal
namespace GlobalTheory.HodgeGramLocal
theorem _root_.solution {w₀ w : ℂ} (h : w / w₀ ∈ slitPlane) :
    HasDerivAt (locLog w₀) (1 / w₀ / (w / w₀)) w :=
  (((hasDerivAt_id w).div_const w₀).clog h).add_const _
end GlobalTheory.HodgeGramLocal
