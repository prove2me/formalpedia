-- Prove2me | solution 1 for GlobalTheory.PoincareBounds.pdiag_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:52:44.098399+00:00
-- url     : https://prove2.me/submissions/84120eaf-2005-4b61-b58e-bd83ef0dfd2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds

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
noncomputable section
open GlobalTheory GlobalTheory.PoincareBounds
namespace GlobalTheory.PoincareBounds
theorem _root_.solution {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) : 0 ≤ pdiag a z k := by
  unfold pdiag; split_ifs <;> positivity
end GlobalTheory.PoincareBounds
