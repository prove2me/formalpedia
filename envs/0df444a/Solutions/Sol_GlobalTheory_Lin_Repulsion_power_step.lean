-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.power_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:24.274738+00:00
-- url     : https://prove2.me/submissions/9162bf88-0f92-465e-8d22-1a6ac7f0f6c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
import Theorems.Thm_GlobalTheory_powerSum_repulsion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion
namespace GlobalTheory.Lin.Repulsion
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (M : Multiset ℂ) (z : ℂ) (L δ x : ℝ), z ∈ M → 1 ≤ L → 0 < δ →
    0 ≤ x → x ≤ 1 / 2 → 1 / (1 + x) ≤ ‖z‖ → (M.card : ℝ) ≤ L →
    (∀ j : ℕ, 1 ≤ j → (M.map fun y => y ^ j).sum.re ≤ 2 * j * δ + L / 2 ^ j) →
    Real.log (1 / (C * L * δ)) / (C * L) ≤ x := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.powerSum_repulsion
  refine ⟨C, hC, fun M z L δ x hz hL hδ hx hx' hn hc hs => ?_⟩
  refine H ℂ M.toFinset id (fun y => M.count y) z L δ x (Multiset.mem_toFinset.2 hz)
    (Multiset.one_le_count_iff_mem.2 hz) hL hδ hx hx' hn ?_ fun j hj => ?_
  · rw [← Multiset.toFinset_sum_count_eq] at hc
    exact_mod_cast hc
  · have := hs j hj
    rw [Finset.sum_multiset_map_count] at this
    simpa [nsmul_eq_mul] using this
end GlobalTheory.Lin.Repulsion
