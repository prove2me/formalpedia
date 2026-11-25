-- Prove2me | solution 1 for GlobalTheory.HodgeGramLocal.exp_locLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:25.240556+00:00
-- url     : https://prove2.me/submissions/5d2e1c29-d0dd-4556-a2ba-e11d205363ba

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
theorem _root_.solution {w₀ w : ℂ} (h0 : w₀ ≠ 0) (h : w / w₀ ∈ slitPlane) :
    exp (locLog w₀ w) = w := by
  rw [locLog, exp_add, exp_log (slitPlane_ne_zero h), exp_log h0, div_mul_cancel₀ _ h0]
end GlobalTheory.HodgeGramLocal
