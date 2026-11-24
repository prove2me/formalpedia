-- Prove2me | solution 1 for GlobalTheory.value_at_zero_eq_sum_integral_kernel_iteratedDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:21.41373+00:00
-- url     : https://prove2.me/submissions/c13f0ea5-aeeb-456e-a882-d006de42f85f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ ε : ℝ, 0 < ε → ∃ κ : Fin 3 → ℝ → ℂ,
      (∀ n, Continuous (κ n) ∧ tsupport (κ n) ⊆ Set.Icc (-ε) ε) ∧
      ∀ u : ℝ → ℂ, ContDiff ℝ ∞ u → u 0 = ∑ n : Fin 3, ∫ t, κ n t * iteratedDeriv n u t := by
  intro ε hε
  set e : ℂ := (ε : ℂ) with he_def
  have he : e ≠ 0 := by
    rw [he_def]; exact_mod_cast hε.ne'
  let s : ℝ → ℝ := fun t => max 0 (min t ε)
  have hs_cont : Continuous s := by fun_prop
  have hs_eq : ∀ t ∈ Set.Icc 0 ε, s t = t := by
    intro t ht; simp only [s]; rw [min_eq_left ht.2, max_eq_right ht.1]
  let P : Fin 3 → ℂ → ℂ := ![fun x => x * (6 / e ^ 2 * (1 - x / e)),
    fun x => x * (2 * (-3 / e * (1 - x / e) ^ 2)), fun x => x * (1 - x / e) ^ 3]
  have hP_cont : ∀ n, Continuous (P n) := by
    intro n; fin_cases n <;> simp [P] <;> fun_prop
  have hP0 : ∀ n, P n 0 = 0 := by
    intro n; fin_cases n <;> simp [P]
  have hPe : ∀ n, P n e = 0 := by
    intro n; fin_cases n <;> simp [P, div_self he]
  have hzero : ∀ n t, t ∉ Set.Ioc 0 ε → P n (s t : ℂ) = 0 := by
    intro n t ht
    rcases le_or_gt t 0 with h | h
    · have : s t = 0 := by simp only [s]; exact max_eq_left (min_le_of_left_le h)
      rw [this, Complex.ofReal_zero, hP0]
    · have h' : ε < t := by
        by_contra h''; exact ht ⟨h, not_lt.mp h''⟩
      have : s t = ε := by simp only [s]; rw [min_eq_right h'.le, max_eq_right hε.le]
      rw [this, ← he_def, hPe]
  refine ⟨fun n t => P n (s t : ℂ), ?_, ?_⟩
  · intro n
    refine ⟨(hP_cont n).comp (Complex.continuous_ofReal.comp hs_cont), ?_⟩
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    by_contra h
    apply ht
    apply hzero n t
    intro h2; exact h ⟨by linarith [h2.1], h2.2⟩
  · intro u hu
    have h1 := contDiff_infty_iff_deriv.mp hu
    have h2 := contDiff_infty_iff_deriv.mp h1.2
    have hu1 : ∀ x, HasDerivAt u (deriv u x) x := fun x => (h1.1 x).hasDerivAt
    have hu2 : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x => (h2.1 x).hasDerivAt
    have hc0 : Continuous u := h1.1.continuous
    have hc1 : Continuous (deriv u) := h2.1.continuous
    have hc2 : Continuous (deriv (deriv u)) := h2.2.continuous
    have hd2 : iteratedDeriv 2 u = deriv (deriv u) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hI : ∀ (g : ℝ → ℂ) (n : Fin 3),
        ∫ t, P n (s t : ℂ) * g t = ∫ t in (0:ℝ)..ε, P n (s t : ℂ) * g t := by
      intro g n
      rw [intervalIntegral.integral_of_le hε.le, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro t ht; rw [hzero n t ht, zero_mul]
    have hK : ∀ n, Continuous (fun t => P n (s t : ℂ)) := fun n =>
      (hP_cont n).comp (Complex.continuous_ofReal.comp hs_cont)
    rw [Fin.sum_univ_three]
    have e0 : iteratedDeriv ((0 : Fin 3) : ℕ) u = u := iteratedDeriv_zero
    have e1 : iteratedDeriv ((1 : Fin 3) : ℕ) u = deriv u := iteratedDeriv_one
    have e2 : iteratedDeriv ((2 : Fin 3) : ℕ) u = deriv (deriv u) := hd2
    rw [e0, e1, e2]
    rw [hI, hI, hI, ← intervalIntegral.integral_add, ← intervalIntegral.integral_add]
    all_goals try (apply Continuous.intervalIntegrable; have := hK 0; have := hK 1; have := hK 2; fun_prop)
    let F : ℝ → ℂ := fun t => (t : ℂ) * (-3 / e * (1 - (t : ℂ) / e) ^ 2 * u t
      + (1 - (t : ℂ) / e) ^ 3 * deriv u t) - (1 - (t : ℂ) / e) ^ 3 * u t
    have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F) (a := 0) (b := ε)
      (f' := fun t => P 0 (s t : ℂ) * u t + P 1 (s t : ℂ) * deriv u t
        + P 2 (s t : ℂ) * deriv (deriv u) t) ?_
      (by apply Continuous.intervalIntegrable; have := hK 0; have := hK 1; have := hK 2; fun_prop)
    · rw [key]
      simp only [F, Complex.ofReal_zero, zero_div, sub_zero, one_pow, one_mul, zero_mul,
        zero_sub, ← he_def, div_self he, sub_self]
      ring
    · intro x hx
      rw [Set.uIcc_of_le hε.le] at hx
      simp only [hs_eq x hx]
      have hx' : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using (hasDerivAt_id x).ofReal_comp
      have hL : HasDerivAt (fun t : ℝ => (1 : ℂ) - (t : ℂ) / e) (-(1 / e)) x := by
        convert (hx'.div_const e).const_sub 1 using 1
      have hφ : HasDerivAt (fun t : ℝ => (1 - (t : ℂ) / e) ^ 3) (-3 / e * (1 - (x : ℂ) / e) ^ 2) x := by
        exact (hL.pow 3).congr_deriv (by norm_num <;> ring)
      have hφ' : HasDerivAt (fun t : ℝ => -3 / e * (1 - (t : ℂ) / e) ^ 2)
          (6 / e ^ 2 * (1 - (x : ℂ) / e)) x := by
        exact ((hL.pow 2).const_mul (-3 / e)).congr_deriv (by norm_num <;> ring)
      have hF := (hx'.mul ((hφ'.mul (hu1 x)).add (hφ.mul (hu2 x)))).sub (hφ.mul (hu1 x))
      refine hF.congr_deriv ?_
      simp only [Pi.mul_apply, Pi.add_apply, P, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
end GlobalTheory
