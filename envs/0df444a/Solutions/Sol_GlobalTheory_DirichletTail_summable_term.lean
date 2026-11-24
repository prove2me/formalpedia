-- Prove2me | solution 1 for GlobalTheory.DirichletTail.summable_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:04:40.3324+00:00
-- url     : https://prove2.me/submissions/4adc7d46-a61a-468d-8ce8-be5081d602f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
import Theorems.Thm_GlobalTheory_DirichletTail_hasSum_telescope
import Theorems.Thm_GlobalTheory_DirichletTail_norm_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : Summable (fun n => term χ n s) := by
  have hT : Summable (fun n : ℕ ↦ (q : ℝ) * (‖s‖ / s.re) *
      (((n + 1 : ℕ) : ℝ) ^ (-s.re) - ((n + 1 + 1 : ℕ) : ℝ) ^ (-s.re))) :=
    ((hasSum_telescope hs 0).summable.mul_left ((q : ℝ) * (‖s‖ / s.re))).congr fun n ↦ by
      simp only [add_zero]
  exact Summable.of_norm_bounded hT fun n ↦ norm_term_le χ hχ n hs le_rfl le_rfl
end GlobalTheory.DirichletTail
