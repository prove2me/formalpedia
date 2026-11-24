-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.differentiableOn_tsum_emE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:08.528346+00:00
-- url     : https://prove2.me/submissions/2ebb1d7f-c2f1-42a1-8a6b-107fdfd7b039

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Theorems.Thm_GlobalTheory_ZetaLeft_norm_emE_le
import Theorems.Thm_GlobalTheory_ZetaLeft_summable_nine_pow_mul_inv_sq_succ
import Theorems.Thm_GlobalTheory_ZetaLeft_differentiable_emE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft
namespace GlobalTheory.ZetaLeft
theorem _root_.solution :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, emE ((n : ℝ) + 1) s) {s : ℂ | -(15/8 : ℝ) < s.re} := by
  intro s hs
  have ho : IsOpen ({z : ℂ | -(15/8 : ℝ) < z.re} ∩ Metric.ball 0 (‖s‖ + 1)) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (n : ℕ) (z : ℂ) => emE ((n : ℝ) + 1) z)
    (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 3) ^ 4))
    (fun n => (differentiable_emE (by positivity)).differentiableOn) ho (by
      intro n z hz
      have h1 : ‖z‖ < ‖s‖ + 1 := by simpa using hz.2
      refine (norm_emE_le (by simp) (le_of_lt hz.1)).trans ?_
      have h2 : ‖z‖ + 2 ≤ ‖s‖ + 3 := by linarith
      gcongr)
  exact (this.differentiableAt (ho.mem_nhds ⟨hs, by simp⟩)).differentiableWithinAt
end GlobalTheory.ZetaLeft
