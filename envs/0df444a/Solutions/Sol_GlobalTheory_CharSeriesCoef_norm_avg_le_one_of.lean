-- Prove2me | solution 1 for GlobalTheory.CharSeriesCoef.norm_avg_le_one_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:05.00773+00:00
-- url     : https://prove2.me/submissions/52a87de3-51ac-4918-bb32-aae123e6384f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CharSeriesCoef
namespace GlobalTheory.CharSeriesCoef
theorem _root_.solution {ι : Type} [Fintype ι] (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖(Fintype.card ι : ℂ)⁻¹ * ∑ i, f i‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · simp [h]
  have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast h
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hc, mul_one]
  calc ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum (fun i _ => hf i)
    _ = Fintype.card ι := by simp
end GlobalTheory.CharSeriesCoef
