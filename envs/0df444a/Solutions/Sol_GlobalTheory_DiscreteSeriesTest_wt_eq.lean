-- Prove2me | solution 1 for GlobalTheory.DiscreteSeriesTest.wt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:40.156257+00:00
-- url     : https://prove2.me/submissions/89aac91a-dfa1-4293-bfd7-8d9c59edb80c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_LowKAddStrictAnti
import Theorems.Thm_GlobalTheory_DiscreteSeriesTest_torus_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI.UpqRep MeasureTheory Matrix Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.DiscreteSeriesTest
namespace GlobalTheory.DiscreteSeriesTest
theorem _root_.solution {ε : Fin 1 → Bool} (m : ℤ) (μ : Fin 1 → ℝ) (v : ℂ) (hv : v ≠ 0)
    (h : IsWtOn (Kset ε) (chi m) μ v) : μ = fun _ => (m : ℝ) := by
  have key : ∀ t : ℝ, Complex.exp ((((μ 0 - m) * t : ℝ) : ℂ) * Complex.I) = 1 := by
    intro t
    have h1 := h (fun _ => t) (torus_mem ε _)
    simp only [chi, Matrix.diagonal_apply_eq, Fin.sum_univ_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] at h1
    have h2 := mul_right_cancel₀ hv h1
    rw [← Complex.exp_int_mul] at h2
    have : (((μ 0 - m) * t : ℝ) : ℂ) * Complex.I = ((μ 0 * t : ℝ) : ℂ) * Complex.I - m * (t * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_sub, ← h2, div_self (Complex.exp_ne_zero _)]
  funext a
  obtain rfl : a = 0 := Subsingleton.elim _ _
  by_contra hne
  have hne' : μ 0 - m ≠ 0 := sub_ne_zero.2 hne
  have := key (Real.pi / (μ 0 - m))
  rw [mul_div_cancel₀ _ hne', Complex.exp_pi_mul_I] at this
  norm_num at this
end GlobalTheory.DiscreteSeriesTest
