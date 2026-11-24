-- Prove2me | solution 1 for GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:24.96515+00:00
-- url     : https://prove2.me/submissions/46a4d3c2-533b-4be4-870e-9e8f598fd2bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLe
import Theorems.Thm_GlobalTheory_SchwartzFstOp_norm_iteratedFDeriv_sliceCLM_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
open GlobalTheory GlobalTheory.SchwartzFstOp
namespace GlobalTheory.SchwartzFstOp
theorem _root_.solution {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ) :
    ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  set M := SchwartzMap.seminorm ℂ (j + k) n f
  have hM : 0 ≤ M := apply_nonneg _ _
  have hpt : ∀ x : V, ‖x'‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖) ≤ M := by
    intro x
    have hw : ‖x'‖ ^ k * ‖x‖ ^ j ≤ ‖(x, x')‖ ^ (j + k) := by
      rw [pow_add, mul_comm]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le (x, x')) _)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (x, x')) _) (by positivity) (by positivity)
    calc ‖x'‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖)
        = (‖x'‖ ^ k * ‖x‖ ^ j) * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖ := by ring
      _ ≤ ‖(x, x')‖ ^ (j + k) * ‖iteratedFDeriv ℝ n f (x, x')‖ :=
          mul_le_mul hw (norm_iteratedFDeriv_sliceCLM_le f x' n x) (norm_nonneg _) (by positivity)
      _ ≤ M := SchwartzMap.le_seminorm ℂ (j + k) n f (x, x')
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x') k : (0 : ℝ) ≤ ‖x'‖ ^ k) with h0 | hpos
  · rw [← h0, zero_mul]; exact hM
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ j n _ (div_nonneg hM hpos.le) (fun x => ?_)
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt x
end GlobalTheory.SchwartzFstOp
