-- Prove2me | solution 1 for GlobalTheory.TraceUnit.exists_pow_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:38:41.359838+00:00
-- url     : https://prove2.me/submissions/c6944733-689d-426c-a4e6-219a67dc1075

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TraceUnit
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace GlobalTheory.TraceUnit
theorem _root_.solution [ProperSpace K] {w : K} (hw : ‖w‖ ≤ 1) :
    ∃ i j : ℕ, i < j ∧ ‖w ^ 2 ^ i - w ^ 2 ^ j‖ < 1 := by
  have hmem : ∀ n : ℕ, w ^ 2 ^ n ∈ Metric.closedBall (0 : K) 1 := fun n => by
    rw [mem_closedBall_zero_iff, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : K) 1).tendsto_subseq hmem
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (1 / 2) (by norm_num)
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  have h1 : dist (w ^ 2 ^ φ N) a < 1 / 2 := hN N le_rfl
  have h2 : dist (w ^ 2 ^ φ (N + 1)) a < 1 / 2 := hN (N + 1) (Nat.le_succ N)
  rw [← dist_eq_norm]
  calc dist (w ^ 2 ^ φ N) (w ^ 2 ^ φ (N + 1)) ≤ dist (w ^ 2 ^ φ N) a + dist a (w ^ 2 ^ φ (N + 1)) :=
        dist_triangle _ _ _
    _ < 1 / 2 + 1 / 2 := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = 1 := by norm_num
end GlobalTheory.TraceUnit
