-- Prove2me | solution 1 for GlobalTheory.FlowScaling.thetaShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:31.455374+00:00
-- url     : https://prove2.me/submissions/afa49911-8dd9-49da-a030-e6cb5a963cf5

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Theorems.Thm_GlobalTheory_FlowScaling_maxFlow_le_div
import Theorems.Thm_GlobalTheory_FlowScaling_mul_maxFlow_le
import Theorems.Thm_GlobalTheory_FlowScaling_fScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.FlowScaling
variable {l d : ℕ} [NeZero d]
namespace GlobalTheory.FlowScaling
theorem _root_.solution : ThetaShift := by
  intro l d _ hl _ _ n T θ w W th hT hw hW hth hθ
  have hl1 : 1 ≤ l := by omega
  have hl3 : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hθ0 : 0 ≤ θ := (hth 0).1.trans (hth 0).2
  have hW0 : ∀ a, 0 ≤ W a := fun a => by
    have h1 : 0 ≤ T * W a := by
      rw [hW a]
      exact mul_nonneg (hw a).le (by linarith [(hth a).2])
    exact (mul_nonneg_iff_of_pos_left hT).1 h1
  have hnw : ∀ a, 0 ≤ (n : ℝ) * w a := fun a => mul_nonneg hn (hw a).le
  have h1 : (1 - θ) * maxFlow l d (fun a => (n : ℝ) * w a) ≤
      maxFlow l d (fun a => T * ((n : ℝ) * W a)) := by
    refine mul_maxFlow_le hl1 (by linarith) hnw fun a => ?_
    have e : T * ((n : ℝ) * W a) = (1 - th a) * ((n : ℝ) * w a) := by
      rw [mul_left_comm, hW a]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith [(hth a).2]) (hnw a)
  have h2 : maxFlow l d (fun a => (n : ℝ) * w a) ≤ (∑ a, (n : ℝ) * w a) / l :=
    maxFlow_le_div hl1 hnw
  have h3 : ∑ a, T * ((n : ℝ) * W a) ≤ ∑ a, (n : ℝ) * w a := by
    refine Finset.sum_le_sum fun a _ => ?_
    have e : T * ((n : ℝ) * W a) = (1 - th a) * ((n : ℝ) * w a) := by
      rw [mul_left_comm, hW a]; ring
    rw [e]
    exact mul_le_of_le_one_left (hnw a) (by linarith [(hth a).1])
  have hg : 0 ≤ gam l := div_nonneg (by linarith) (by nlinarith)
  have h4 := mul_le_mul_of_nonneg_left h3 hg
  have h5 := mul_le_mul_of_nonneg_left h2 hθ0
  have h6 : 0 ≤ θ * ((∑ a, (n : ℝ) * w a) / l) :=
    mul_nonneg hθ0 (div_nonneg (Finset.sum_nonneg fun a _ => hnw a) (by linarith))
  have h7 : 6 * θ * n * (∑ a, w a) / l = 6 * (θ * ((∑ a, (n : ℝ) * w a) / l)) := by
    rw [← Finset.mul_sum]; ring
  rw [← fScale l d (by omega) T (fun a => (n : ℝ) * W a) hT.le
    (fun a => mul_nonneg hn (hW0 a)), h7]
  unfold Fnum
  linarith
end GlobalTheory.FlowScaling
