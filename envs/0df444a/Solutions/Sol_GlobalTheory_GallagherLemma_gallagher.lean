-- Prove2me | solution 1 for GlobalTheory.GallagherLemma.gallagher
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:24:46.557932+00:00
-- url     : https://prove2.me/submissions/5d298306-395e-49de-b277-bf46e6a82eb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Theorems.Thm_GlobalTheory_GallagherLemma_exp_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real
open GlobalTheory GlobalTheory.GallagherLemma
namespace GlobalTheory.GallagherLemma
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ T →
    (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n‖ ^ 2 / x := by
  refine ⟨8 * π, by positivity, fun N a T hT => ?_⟩
  have h := exp_sum (Finset.Icc 1 N) a (fun n => Real.log n) T (by linarith)
  convert h using 2
  · funext t
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : n ≠ 0)
    rw [cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    congr 2
    push_cast
    ring
  · rw [← Real.range_exp, ← Set.image_univ,
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      Measure.restrict_univ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [abs_of_pos (Real.exp_pos v), mul_div_cancel₀ _ (Real.exp_pos v).ne', Finset.sum_filter]
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : 0 < n)
    rw [Set.indicator_apply, ← Real.exp_add]
    refine if_congr ?_ rfl rfl
    rw [Set.mem_Ico, ← Real.lt_log_iff_exp_lt hn0, ← Real.log_le_iff_le_exp hn0]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
end GlobalTheory.GallagherLemma
