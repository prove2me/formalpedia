-- Prove2me | solution 1 for GlobalTheory.PoincareBounds.half_le_pdiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:26.314981+00:00
-- url     : https://prove2.me/submissions/194fd732-3b43-43c7-a1c9-6729f7e9bee1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PoincareMetricPuncturedPolydiscBounds
import Theorems.Thm_GlobalTheory_PoincareBounds_norm_mul_tlog_lt

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
theorem _root_.solution {n a : ℕ} (ha : a ≤ n) {ρ : ℝ} (hρ : ρ ≤ 1) {z : Fin n → ℂ}
    (hz : z ∈ punctured ha ρ) (k : Fin n) : 1 / 2 ≤ pdiag a z k := by
  unfold pdiag
  split_ifs with hk
  · have h0 : z k ≠ 0 := hz.2 ⟨k, hk⟩
    obtain ⟨hp, hl⟩ := norm_mul_tlog_lt h0 (lt_of_lt_of_le (hz.1 k) hρ)
    have hs : ‖z k‖ ^ 2 * tlog (z k) ^ 2 = (‖z k‖ * tlog (z k)) ^ 2 := by ring
    rw [hs]
    have h2 : 0 < (‖z k‖ * tlog (z k)) ^ 2 := by positivity
    have h3 : (‖z k‖ * tlog (z k)) ^ 2 < 1 := by nlinarith
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  · exact le_rfl
end GlobalTheory.PoincareBounds
