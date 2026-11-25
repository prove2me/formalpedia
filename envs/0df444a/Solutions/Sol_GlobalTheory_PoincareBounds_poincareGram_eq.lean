-- Prove2me | solution 1 for GlobalTheory.PoincareBounds.poincareGram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:30.441635+00:00
-- url     : https://prove2.me/submissions/0e9f4749-e5d4-42ba-8de6-3d91d7c45971

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
theorem _root_.solution {n : ℕ} (a : ℕ) (z : Fin n → ℂ) :
    poincareGram a z = diagonal fun k => ((pdiag a z k : ℝ) : ℂ) := rfl
end GlobalTheory.PoincareBounds
