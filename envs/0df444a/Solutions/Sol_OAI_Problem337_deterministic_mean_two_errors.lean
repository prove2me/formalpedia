-- Prove2me | solution 1 for OAI.Problem337.deterministic_mean_two_errors
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:06:48.41313+00:00
-- url     : https://prove2.me/submissions/21ab05a1-59fc-4b84-b50e-36b6e44b82aa

import Mathlib
import Definitions.Def_OAIQ8EF000

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Explicit derivatives of the reciprocal phase used in deterministic cancellation. -/
theorem reciprocal_phase_iteratedDeriv (k : ℕ) (Z x : ℝ) :
    iteratedDeriv k (fun y : ℝ => Z / y) x =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) * Z / x ^ (k + 1) := by
  simp only [div_eq_mul_inv]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  ring

theorem abs_reciprocal_phase_iteratedDeriv (k : ℕ) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv k (fun y : ℝ => Z / y) x| =
      (k.factorial : ℝ) * |Z| / x ^ (k + 1) := by
  rw [reciprocal_phase_iteratedDeriv]
  simp [abs_div, abs_mul, abs_pow, abs_of_pos hx]

/-- The same derivative estimate on an arbitrary positive interval. The flexible
upper endpoint allows the extra samples used in a second-derivative test. -/
theorem reciprocal_phase_derivative_bounds_interval (k : ℕ) (Z : ℝ) {U V x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x ≤ V) :
    (k.factorial : ℝ) * |Z| / V ^ (k + 1) ≤
        |iteratedDeriv k (fun y : ℝ => Z / y) x| ∧
      |iteratedDeriv k (fun y : ℝ => Z / y) x| ≤
        (k.factorial : ℝ) * |Z| / U ^ (k + 1) := by
  have hx0 : 0 < x := hU.trans_le hx
  rw [abs_reciprocal_phase_iteratedDeriv k Z hx0]
  constructor
  · apply div_le_div_of_nonneg_left (by positivity) (pow_pos hx0 _)
    exact pow_le_pow_left₀ hx0.le hxV _
  · apply div_le_div_of_nonneg_left (by positivity) (pow_pos hU _)
    exact pow_le_pow_left₀ hU.le hx _

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ForwardDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Set
open scoped ContDiff Topology

namespace Problem337

theorem forwardDifference_contDiffOn (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) :
    ContDiffOn ℝ ∞ (forwardDifference hs f) (Ioi 0) := by
  induction hs with
  | nil => exact hf
  | cons h hs ih =>
      have hh : 0 ≤ h := hhs h (by simp)
      have ih' := ih (fun d hd => hhs d (by simp [hd]))
      change ContDiffOn ℝ ∞ (fun x => forwardDifference hs f (x + h) - forwardDifference hs f x) (Ioi 0)
      apply ContDiffOn.sub _ ih'
      apply ih'.comp (contDiffOn_id.add contDiffOn_const)
      intro x hx
      change 0 < x + h
      change 0 < x at hx
      linarith

theorem deriv_forwardDifference (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    deriv (forwardDifference hs f) x = forwardDifference hs (deriv f) x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      have hh : 0 ≤ h := hhs h (by simp)
      have htail : ∀ d ∈ hs, 0 ≤ d := fun d hd => hhs d (by simp [hd])
      have hcont := forwardDifference_contDiffOn hs htail hf
      have hx' : 0 < x + h := by linarith
      have hdiff : DifferentiableAt ℝ (forwardDifference hs f) x :=
        (hcont.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)
      have hdiff' : DifferentiableAt ℝ (fun y => forwardDifference hs f (y + h)) x := by
        exact ((hcont.contDiffAt (isOpen_Ioi.mem_nhds hx')).differentiableAt (by simp)).comp x
          (differentiableAt_id.add_const h)
      change deriv (fun y => forwardDifference hs f (y + h) - forwardDifference hs f y) x = _
      rw [deriv_fun_sub hdiff' hdiff, deriv_comp_add_const]
      change deriv (forwardDifference hs f) (x + h) - deriv (forwardDifference hs f) x = _
      rw [ih htail, ih htail]
      rfl
      all_goals assumption

/-- Repeated mean value theorem for positive shifts. The witness remains in the
interval swept out by all shifts. -/
theorem forwardDifference_eq_derivative (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    ∃ ξ : ℝ, x ≤ ξ ∧ ξ ≤ x + hs.sum ∧
      forwardDifference hs f x = hs.prod * iteratedDeriv hs.length f ξ := by
  induction hs generalizing f x with
  | nil => exact ⟨x, le_rfl, by simp, by simp [forwardDifference]⟩
  | cons h hs ih =>
      have hh : 0 < h := hhs h (by simp)
      have htail : ∀ d ∈ hs, 0 < d := fun d hd => hhs d (by simp [hd])
      have hnonneg : ∀ d ∈ hs, 0 ≤ d := fun d hd => (htail d hd).le
      have hcont := forwardDifference_contDiffOn hs hnonneg hf
      have hcc : Icc x (x + h) ⊆ Ioi 0 := by intro y hy; exact hx.trans_le hy.1
      have hco : Ioo x (x + h) ⊆ Ioi 0 := Ioo_subset_Icc_self.trans hcc
      obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope (forwardDifference hs f)
        (by linarith : x < x + h) (hcont.continuousOn.mono hcc)
        ((hcont.differentiableOn (by simp)).mono hco)
      have hc0 : 0 < c := hx.trans hc.1
      rw [deriv_forwardDifference hs hnonneg hf hc0] at hderiv
      have hden : x + h - x = h := by ring
      rw [hden] at hderiv
      have hmul : forwardDifference (h :: hs) f x = h * forwardDifference hs (deriv f) c := by
        have heq := (eq_div_iff hh.ne').1 hderiv
        dsimp [forwardDifference]
        nlinarith
      have hf' : ContDiffOn ℝ ∞ (deriv f) (Ioi 0) :=
        hf.deriv_of_isOpen isOpen_Ioi (by simp)
      obtain ⟨ξ, hcξ, hξ, heq⟩ := ih htail hf' hc0
      refine ⟨ξ, hc.1.le.trans hcξ, ?_, ?_⟩
      · simp only [List.sum_cons]
        linarith [hc.2]
      · rw [hmul, heq]
        simp only [List.prod_cons, List.length_cons, iteratedDeriv_succ']
        ring

theorem iteratedDeriv_forwardDifference (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (forwardDifference hs f) x = forwardDifference hs (iteratedDeriv k f) x := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
      have heq : deriv (forwardDifference hs f) =ᶠ[𝓝 x] forwardDifference hs (deriv f) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact deriv_forwardDifference hs hhs hf hy
      rw [iteratedDeriv_succ', heq.iteratedDeriv_eq k]
      rw [ih (hf.deriv_of_isOpen isOpen_Ioi (by simp))]
      rw [iteratedDeriv_succ']

private theorem smooth_iteratedDeriv_Ioi (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) : ContDiffOn ℝ ∞ (iteratedDeriv k f) (Ioi 0) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

private theorem iteratedDeriv_order_add (r k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv r (iteratedDeriv k f) = iteratedDeriv (r + k) f := by
  induction r with
  | zero => simp
  | succ r ih => simp only [iteratedDeriv_succ, ih, Nat.succ_add]

/-- The derivative of an iterated difference is a scaled higher derivative at an
intermediate point. This avoids a multi-dimensional integral in the phase estimate. -/
theorem iteratedDeriv_forwardDifference_eq (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    ∃ ξ : ℝ, x ≤ ξ ∧ ξ ≤ x + hs.sum ∧
      iteratedDeriv k (forwardDifference hs f) x =
        hs.prod * iteratedDeriv (hs.length + k) f ξ := by
  rw [iteratedDeriv_forwardDifference k hs (fun h hh => (hhs h hh).le) hf hx]
  obtain ⟨ξ, hxξ, hξ, heq⟩ := forwardDifference_eq_derivative hs hhs
    (smooth_iteratedDeriv_Ioi k hf) hx
  refine ⟨ξ, hxξ, hξ, ?_⟩
  simpa only [iteratedDeriv_order_add] using heq

/-- Endpoint-flexible version, allowing the upper endpoint to extend beyond
an exponential sum's support by the one or two derivative-test samples. -/
theorem reciprocal_forwardDifference_derivative_bounds_interval (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (Z : ℝ) {U V x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxend : x + hs.sum ≤ V) :
    hs.prod * ((hs.length + k).factorial : ℝ) * |Z| /
        V ^ (hs.length + k + 1) ≤
      |iteratedDeriv k (forwardDifference hs (fun y => Z / y)) x| ∧
    |iteratedDeriv k (forwardDifference hs (fun y => Z / y)) x| ≤
      hs.prod * ((hs.length + k).factorial : ℝ) * |Z| /
        U ^ (hs.length + k + 1) := by
  have hf : ContDiffOn ℝ ∞ (fun y : ℝ => Z / y) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun y hy => ne_of_gt hy)
  obtain ⟨ξ, hxξ, hξ, heq⟩ := iteratedDeriv_forwardDifference_eq k hs hhs hf (hU.trans_le hx)
  have hp : 0 ≤ hs.prod := List.prod_nonneg (fun h hh => (hhs h hh).le)
  rw [heq, abs_mul, abs_of_nonneg hp]
  obtain ⟨hl, hu⟩ := reciprocal_phase_derivative_bounds_interval (hs.length + k) Z hU
    (hx.trans hxξ) (hξ.trans hxend)
  constructor
  · simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hl hp
  · simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hu hp

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FourierSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators
open Complex ComplexConjugate

namespace Problem337

lemma re_finset_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ a ∈ s, f a).re = ∑ a ∈ s, (f a).re :=
  map_sum Complex.reAddGroupHom f s

/-- Expand a finite complex second moment into pairwise correlations. -/
theorem finite_complex_second_moment_identity {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) :
    (∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2) =
      ∑ t ∈ T, ∑ s ∈ T, (∑ u ∈ U, z u t * conj (z u s)).re := by
  have hpoint (u : α) : ‖∑ t ∈ T, z u t‖ ^ 2 =
      ∑ t ∈ T, ∑ s ∈ T, (z u t * conj (z u s)).re := by
    calc
      ‖∑ t ∈ T, z u t‖ ^ 2 =
          ((∑ t ∈ T, z u t) * conj (∑ t ∈ T, z u t)).re := by
            rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      _ = _ := by
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum, re_finset_sum]
        rw [Finset.sum_comm]
  simp_rw [hpoint, re_finset_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]

/-- Unit phases have a second moment bounded by their diagonal contribution
plus a uniform bound for all off-diagonal correlations. -/
theorem finite_complex_second_moment_bound {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) (E : ℝ)
    (hunit : ∀ u ∈ U, ∀ t ∈ T, ‖z u t‖ = 1)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * conj (z u s)‖ ≤ E) :
    (∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2) ≤
      (U.card : ℝ) * T.card + (T.card : ℝ) * (T.card - 1 : ℝ) * E := by
  classical
  rw [finite_complex_second_moment_identity]
  have hentry (t : β) (ht : t ∈ T) (s : β) (hs : s ∈ T) :
      (∑ u ∈ U, z u t * conj (z u s)).re ≤
        E + if t = s then (U.card : ℝ) - E else 0 := by
    by_cases hts : t = s
    · subst s
      have hd : (∑ u ∈ U, z u t * conj (z u t)).re = U.card := by
        simp only [re_finset_sum, Complex.mul_conj, Complex.ofReal_re]
        calc
          (∑ u ∈ U, Complex.normSq (z u t)) = ∑ _u ∈ U, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Complex.normSq_eq_norm_sq, hunit u hu t ht]
            norm_num
          _ = _ := by simp
      simp [hd]
    · simpa [hts] using (Complex.re_le_norm (∑ u ∈ U, z u t * conj (z u s))).trans
        (hcorr t ht s hs hts)
  calc
    (∑ t ∈ T, ∑ s ∈ T, (∑ u ∈ U, z u t * conj (z u s)).re) ≤
        ∑ t ∈ T, ∑ s ∈ T, (E + if t = s then (U.card : ℝ) - E else 0) := by
      apply Finset.sum_le_sum
      intro t ht
      exact Finset.sum_le_sum (fun s hs => hentry t ht s hs)
    _ = (T.card : ℝ) * ((T.card : ℝ) * E + (U.card : ℝ) - E) := by
      have hrow (t : β) (ht : t ∈ T) :
          (∑ s ∈ T, (E + if t = s then (U.card : ℝ) - E else 0)) =
            (T.card : ℝ) * E + (U.card : ℝ) - E := by
        simp [Finset.sum_add_distrib, ht]
        ring
      simp_rw [Finset.sum_congr rfl hrow]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by ring

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_VanDerCorput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators
open ComplexConjugate

namespace Problem337

/-- Cauchy--Schwarz for the norm of a finite complex sum. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {α : Type*}
    (U : Finset α) (f : α → ℂ) :
    ‖∑ u ∈ U, f u‖ ^ 2 ≤ (U.card : ℝ) * ∑ u ∈ U, ‖f u‖ ^ 2 := by
  have hn := norm_sum_le U f
  have hs := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) (fun u => ‖f u‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs

/-- Averaging equal column sums and bounding their pairwise correlations.
This is the finite algebraic core of van der Corput differencing. -/
theorem averaged_columns_correlation_bound {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ)
    (S : ℂ) (D E : ℝ)
    (hcol : ∀ t ∈ T, ∑ u ∈ U, z u t = S)
    (hdiag : ∀ t ∈ T, ∑ u ∈ U, ‖z u t‖ ^ 2 ≤ D)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * conj (z u s)‖ ≤ E) :
    (T.card : ℝ) ^ 2 * ‖S‖ ^ 2 ≤
      (U.card : ℝ) * ((T.card : ℝ) * D +
        (T.card : ℝ) * (T.card - 1 : ℝ) * E) := by
  classical
  have havg : (∑ u ∈ U, ∑ t ∈ T, z u t) = (T.card : ℂ) * S := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_congr rfl hcol]
    simp
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq U (fun u => ∑ t ∈ T, z u t)
  rw [havg, norm_mul, Complex.norm_natCast, mul_pow] at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [finite_complex_second_moment_identity]
  have hentry (t : β) (ht : t ∈ T) (s : β) (hs : s ∈ T) :
      (∑ u ∈ U, z u t * conj (z u s)).re ≤
        E + if t = s then D - E else 0 := by
    by_cases heq : t = s
    · subst s
      simp only [re_finset_sum, Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq, ite_true, add_sub_cancel]
      exact hdiag t ht
    · simpa [heq] using (Complex.re_le_norm _).trans (hcorr t ht s hs heq)
  calc
    (∑ t ∈ T, ∑ s ∈ T, (∑ u ∈ U, z u t * conj (z u s)).re) ≤
        ∑ t ∈ T, ∑ s ∈ T, (E + if t = s then D - E else 0) := by
      exact Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun s hs => hentry t ht s hs))
    _ = (T.card : ℝ) * D + (T.card : ℝ) * (T.card - 1 : ℝ) * E := by
      have hrow (t : β) (ht : t ∈ T) :
          (∑ s ∈ T, (E + if t = s then D - E else 0)) =
            (T.card : ℝ) * E + D - E := by
        simp [Finset.sum_add_distrib, ht]
        ring
      simp_rw [Finset.sum_congr rfl hrow]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Translation does not change a finite sum once the summation interval
    contains all translated points in its support. -/
theorem sum_shift_supported {M : Type*} [AddCommMonoid M]
    (a : ℤ → M) (N H : ℕ) (t : ℤ) (ht0 : 0 ≤ t) (htH : t ≤ H)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0) :
    (∑ n ∈ Finset.Icc (1 - (H : ℤ)) N, a (n + t)) =
      ∑ n ∈ Finset.Icc (1 : ℤ) N, a n := by
  classical
  apply Finset.sum_bij_ne_zero (fun n _ _ => n + t)
  · intro n hn hne
    by_contra hout
    exact hne (hsupport (n + t) hout)
  · intro n hn hn0 m hm hm0 heq
    omega
  · intro n hn hn0
    refine ⟨n - t, ?_, ?_, by omega⟩
    · simp only [Finset.mem_Icc] at hn ⊢
      omega
    · simpa using hn0
  · intros
    rfl

/-- A concrete finite-support shift bound, before using `H ≤ N` to simplify
    the two endpoint losses. Correlation assumptions are symmetric in the shift. -/
theorem van_der_corput_interval_exact
    (a : ℤ → ℂ) (N H : ℕ) (hH : 1 ≤ H) (E : ℝ) (hE : 0 ≤ E)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, -(H : ℤ) < h → h < H → h ≠ 0 →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ^ 2 ≤
      ((N : ℝ) + H) * ((N : ℝ) / H + E) := by
  classical
  let U := Finset.Icc (1 - (H : ℤ)) (N : ℤ)
  let T := Finset.range H
  let z : ℤ → ℕ → ℂ := fun n t => a (n + t)
  have hcardU : (U.card : ℝ) = (N : ℝ) + H := by
    dsimp [U]
    rw [Int.card_Icc]
    have heq : (N : ℤ) + 1 - (1 - (H : ℤ)) = ((N + H : ℕ) : ℤ) := by omega
    rw [heq]
    norm_cast
  have hcol (t : ℕ) (ht : t ∈ T) :
      (∑ n ∈ U, z n t) = ∑ n ∈ Finset.Icc (1 : ℤ) N, a n := by
    exact sum_shift_supported a N H t (by omega) (by have := Finset.mem_range.mp ht; omega) hsupport
  have hdiag (t : ℕ) (ht : t ∈ T) : (∑ n ∈ U, ‖z n t‖ ^ 2) ≤ (N : ℝ) := by
    have hs : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → ‖a n‖ ^ 2 = 0 := by
      intro n hn
      simp [hsupport n hn]
    have heq := sum_shift_supported (fun n => ‖a n‖ ^ 2) N H t
      (by omega) (by have := Finset.mem_range.mp ht; omega) hs
    change (∑ n ∈ U, ‖a (n + t)‖ ^ 2) ≤ (N : ℝ)
    rw [heq]
    calc
      (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖a n‖ ^ 2) ≤
          ∑ _n ∈ Finset.Icc (1 : ℤ) N, (1 : ℝ) := by
        exact Finset.sum_le_sum (fun n _ => by have := hnorm n; have := norm_nonneg (a n); nlinarith)
      _ = (N : ℝ) := by simp [Int.card_Icc]
  have hcorr' (t : ℕ) (ht : t ∈ T) (s : ℕ) (hs : s ∈ T) (hne : t ≠ s) :
      ‖∑ n ∈ U, z n t * conj (z n s)‖ ≤ E := by
    let b : ℤ → ℂ := fun n => a (n + ((t : ℤ) - s)) * conj (a n)
    have hb : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → b n = 0 := by
      intro n hn
      simp [b, hsupport n hn]
    have heq := sum_shift_supported b N H s (by omega)
      (by have := Finset.mem_range.mp hs; omega) hb
    have hz : (∑ n ∈ U, z n t * conj (z n s)) = ∑ n ∈ U, b (n + s) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [z, b]
    rw [hz, heq]
    apply hcorr
    · have := Finset.mem_range.mp ht
      have := Finset.mem_range.mp hs
      omega
    · have := Finset.mem_range.mp ht
      have := Finset.mem_range.mp hs
      omega
    · omega
  have hraw := averaged_columns_correlation_bound U T z
    (∑ n ∈ Finset.Icc (1 : ℤ) N, a n) N E hcol hdiag hcorr'
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  simp only [T, Finset.card_range, hcardU] at hraw
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hHR)).mp
  have hweak : (H : ℝ)^2 * ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖^2 ≤
      ((N : ℝ) + H) * ((H : ℝ) * N + (H : ℝ)^2 * E) := by
    apply hraw.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have heq : (((N : ℝ) + H) * ((N : ℝ) / H + E)) * (H : ℝ)^2 =
      ((N : ℝ) + H) * ((H : ℝ) * N + (H : ℝ)^2 * E) := by
    field_simp
  rw [heq]
  simpa [mul_comm] using hweak

/-- Opposite shifts give conjugate autocorrelations, with zero extension
    supplying the endpoint cancellation. -/
theorem interval_correlation_neg (a : ℤ → ℂ) (N : ℕ) (h : ℤ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + -h) * conj (a n)) =
      conj (∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)) := by
  classical
  rw [map_sum]
  apply Finset.sum_bij_ne_zero (fun n _ _ => n - h)
  · intro n hn hn0
    by_contra hout
    have hz := hsupport (n - h) hout
    simp [sub_eq_add_neg] at hz
    simp [hz] at hn0
  · intro n hn hn0 m hm hm0 heq
    omega
  · intro n hn hn0
    have hmem : n + h ∈ Finset.Icc (1 : ℤ) N := by
      by_contra hout
      have hz := hsupport (n + h) hout
      simp [hz] at hn0
    refine ⟨n + h, hmem, ?_, by omega⟩
    simpa [map_mul, mul_comm] using hn0
  · intro n hn hn0
    simp [map_mul, sub_eq_add_neg, mul_comm]

/-- The elementary van der Corput inequality for an interval-supported
    sequence, in the positive-shift form required for iterated differencing. -/
theorem van_der_corput_interval
    (a : ℤ → ℂ) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (E : ℝ) (hE : 0 ≤ E)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, 0 < h → h < H →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ^ 2 ≤
      2 * (N : ℝ)^2 / H + 2 * (N : ℝ) * E := by
  have hsym : ∀ h : ℤ, -(H : ℤ) < h → h < H → h ≠ 0 →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤ E := by
    intro h hl hu hn
    by_cases hp : 0 < h
    · exact hcorr h hp hu
    · have hneg : 0 < -h := by omega
      have hnegb : -h < (H : ℤ) := by omega
      have heq := interval_correlation_neg a N (-h) hsupport
      simp only [neg_neg] at heq
      rw [heq, Complex.norm_conj]
      exact hcorr (-h) hneg hnegb
  have hraw := van_der_corput_interval_exact a N H hH E hE hsupport hnorm hsym
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hHNR : (H : ℝ) ≤ N := by exact_mod_cast hHN
  calc
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ^ 2 ≤
        ((N : ℝ) + H) * ((N : ℝ) / H + E) := hraw
    _ ≤ (2 * (N : ℝ)) * ((N : ℝ) / H + E) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = 2 * (N : ℝ)^2 / H + 2 * (N : ℝ) * E := by ring

/-- Normalized van der Corput differencing, with an explicit absolute constant. -/
theorem van_der_corput_interval_normalized
    (a : ℤ → ℂ) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (E : ℝ) (hE : 0 ≤ E)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, 0 < h → h < H →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤ E) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ^ 2 / (N : ℝ)^2 ≤
      2 / (H : ℝ) + 2 * E / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  apply (div_le_iff₀ (sq_pos_of_pos hNR)).mpr
  have hraw := van_der_corput_interval a N H hH hHN E hE hsupport hnorm hcorr
  have heq : (2 / (H : ℝ) + 2 * E / N) * (N : ℝ)^2 =
      2 * (N : ℝ)^2 / H + 2 * (N : ℝ) * E := by
    field_simp
  rw [heq]
  exact hraw

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_IteratedDifferencing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate
namespace Problem337

theorem correlationShift_supported (a : ℤ → ℂ) (N : ℕ) (h : ℤ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0) :
    ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → correlationShift a h n = 0 := by
  intro n hn
  simp [correlationShift, hsupport n hn]

theorem correlationShift_norm_le_one (a : ℤ → ℂ) (h : ℤ)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1) :
    ∀ n : ℤ, ‖correlationShift a h n‖ ≤ 1 := by
  intro n
  simp only [correlationShift, norm_mul, Complex.norm_conj]
  have h := mul_le_mul (hnorm (n + h)) (hnorm n) (norm_nonneg (a n)) (by norm_num : (0 : ℝ) ≤ 1)
  simpa using h

theorem differencingBudget_nonneg (H r : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ differencingBudget H r B := by
  cases r with
  | zero => exact hB
  | succ r => exact Real.sqrt_nonneg _

/-- If every terminal `r`-fold correlation is small, the original sum is
    bounded by the iterated van der Corput square-root budget. -/
theorem iterated_differencing_bound (r : ℕ) (N H : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (B : ℝ) (hB : 0 ≤ B)
    (a : ℤ → ℂ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hterminal : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ / (N : ℝ) ≤ B) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ / (N : ℝ) ≤ differencingBudget H r B := by
  induction r generalizing a with
  | zero =>
    simpa [differencingBudget, iteratedCorrelation] using
      hterminal [] rfl (by simp)
  | succ r ih =>
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hbudget : 0 ≤ differencingBudget H r B := differencingBudget_nonneg H r hB
    have hcorr (h : ℤ) (hh : 0 < h) (hhH : h < H) :
        ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a (n + h) * conj (a n)‖ ≤
          (N : ℝ) * differencingBudget H r B := by
      have hchild := ih (correlationShift a h)
        (correlationShift_supported a N h hsupport)
        (correlationShift_norm_le_one a h hnorm) (by
          intro hs hlen hgood
          simpa [iteratedCorrelation] using hterminal (h :: hs) (by simp [hlen])
            (by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro (And.intro hh hhH) hgood))
      have := (div_le_iff₀ hNR).mp hchild
      simpa [correlationShift, mul_comm] using this
    have hvdc := van_der_corput_interval_normalized a N H hH hHN
      ((N : ℝ) * differencingBudget H r B) (mul_nonneg (le_of_lt hNR) hbudget)
      hsupport hnorm hcorr
    have hcancel : 2 * ((N : ℝ) * differencingBudget H r B) / N =
        2 * differencingBudget H r B := by field_simp
    rw [hcancel, ← div_pow] at hvdc
    exact (Real.le_sqrt (div_nonneg (norm_nonneg _) (le_of_lt hNR)) (by positivity)).mpr hvdc

/-- A uniform bound for the square-root budget. Its constant does not grow
    with the number of differencing steps. -/
theorem differencingBudget_le_rpow (H r : ℕ) {ε B : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hHB : 2 / (H : ℝ) ≤ ε)
    (hB : B ≤ ε) :
    differencingBudget H r B ≤ 3 * ε ^ (1 / (2 : ℝ)^r) := by
  induction r with
  | zero =>
    simp only [differencingBudget, pow_zero, div_one, Real.rpow_one]
    linarith
  | succ r ih =>
    have hpow : (0 : ℝ) < (2 : ℝ)^r := by positivity
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ)^r := one_le_pow₀ (by norm_num)
    have halpha : 1 / (2 : ℝ)^r ≤ 1 := (div_le_one hpow).mpr hpow1
    have heps : ε ≤ ε ^ (1 / (2 : ℝ)^r) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 halpha
    have hpower : (ε ^ (1 / (2 : ℝ)^(r + 1)))^2 = ε ^ (1 / (2 : ℝ)^r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hε)]
      congr 1
      rw [pow_succ]
      field_simp
      norm_num
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · change 2 / (H : ℝ) + 2 * differencingBudget H r B ≤
        (3 * ε ^ (1 / (2 : ℝ)^(r + 1)))^2
      rw [mul_pow, hpower]
      have heps0 : 0 ≤ ε ^ (1 / (2 : ℝ)^r) := Real.rpow_nonneg (le_of_lt hε) _
      nlinarith

/-- Power-saving form of iterated van der Corput differencing. -/
theorem iterated_differencing_power_bound (r : ℕ) (N H : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hHε : 2 / (H : ℝ) ≤ ε) (a : ℤ → ℂ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hterminal : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ / (N : ℝ) ≤ ε) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ / (N : ℝ) ≤
      3 * ε ^ (1 / (2 : ℝ)^r) :=
  (iterated_differencing_bound r N H hH hHN ε (le_of_lt hε) a hsupport hnorm hterminal).trans
    (differencingBudget_le_rpow H r hε hε1 hHε le_rfl)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CorrelationPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate
namespace Problem337

theorem differencingPhase_sub (x y : ℝ) :
    differencingPhase (x - y) = differencingPhase x * conj (differencingPhase y) := by
  simp only [differencingPhase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem correlationShift_intervalPhase (f : ℝ → ℝ) (L U h : ℤ) (hh : 0 ≤ h) :
    correlationShift (intervalPhase f L U) h =
      intervalPhase (fun x => f (x + h) - f x) L (U - h) := by
  funext n
  by_cases hn : L ≤ n ∧ n ≤ U - h
  · have hn0 : L ≤ n ∧ n ≤ U := by omega
    have hn1 : L ≤ n + h ∧ n + h ≤ U := by omega
    simp [correlationShift, intervalPhase, hn, hn0, hn1, differencingPhase_sub]
  · have hbad : ¬ (L ≤ n + h ∧ n + h ≤ U) ∨ ¬ (L ≤ n ∧ n ≤ U) := by omega
    rcases hbad with hbad | hbad
    · simp [correlationShift, intervalPhase, hn, hbad]
    · simp [correlationShift, intervalPhase, hn, hbad]

theorem forwardDifference_sub_input (hs : List ℝ) (f g : ℝ → ℝ) :
    forwardDifference hs (fun x => f x - g x) =
      fun x => forwardDifference hs f x - forwardDifference hs g x := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    funext x
    simp only [forwardDifference, ih]
    ring

theorem forwardDifference_translate_input (hs : List ℝ) (f : ℝ → ℝ) (h : ℝ) :
    forwardDifference hs (fun x => f (x + h)) =
      fun x => forwardDifference hs f (x + h) := by
  induction hs with
  | nil => rfl
  | cons t hs ih =>
    funext x
    simp only [forwardDifference, ih]
    congr 1
    congr 1
    ring

theorem forwardDifference_cons_input (hs : List ℝ) (f : ℝ → ℝ) (h : ℝ) :
    forwardDifference hs (fun x => f (x + h) - f x) =
      forwardDifference (h :: hs) f := by
  rw [forwardDifference_sub_input, forwardDifference_translate_input]
  rfl

/-- Positive iterated correlations of a truncated phase are exactly the
    differentiated phase on the interval shortened by the total shift. -/
theorem iteratedCorrelation_intervalPhase (hs : List ℤ) (f : ℝ → ℝ) (L U : ℤ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) :
    iteratedCorrelation (intervalPhase f L U) hs =
      intervalPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ))) f) L (U - hs.sum) := by
  induction hs generalizing f L U with
  | nil => simp [iteratedCorrelation, forwardDifference]
  | cons h hs ih =>
    have hh : 0 ≤ h := hhs h (by simp)
    have htail : ∀ t ∈ hs, 0 ≤ t := fun t ht => hhs t (by simp [ht])
    rw [iteratedCorrelation, correlationShift_intervalPhase f L U h hh,
      ih _ _ _ htail, forwardDifference_cons_input]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    omega

/-- A zero-extended interval phase sums to its untruncated phase sum on
    any larger integer interval. Empty subintervals are included. -/
theorem intervalPhase_sum (f : ℝ → ℝ) (L U A B : ℤ)
    (hAL : A ≤ L) (hUB : U ≤ B) :
    (∑ n ∈ Finset.Icc A B, intervalPhase f L U n) =
      ∑ n ∈ Finset.Icc L U, differencingPhase (f n) := by
  classical
  have hsub : Finset.Icc L U ⊆ Finset.Icc A B := Finset.Icc_subset_Icc hAL hUB
  calc
    (∑ n ∈ Finset.Icc A B, intervalPhase f L U n) =
        ∑ n ∈ Finset.Icc L U, intervalPhase f L U n := by
      apply (Finset.sum_subset hsub _).symm
      intro n hn hnot
      simp only [Finset.mem_Icc] at hnot
      simp [intervalPhase, hnot]
    _ = ∑ n ∈ Finset.Icc L U, differencingPhase (f n) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [intervalPhase, Finset.mem_Icc.mp hn]

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DyadicSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Decompose a positive integer initial interval into dyadic shells. -/
theorem sum_dyadic_shells {E : Type*} [AddCommMonoid E] (f : ℕ → E) (J : ℕ) :
    (∑ n ∈ Finset.Ico 1 (2 ^ J), f n) =
      ∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive f (m := 1) (n := 2 ^ J) (k := 2 ^ (J + 1))
      (Nat.succ_le_iff.mpr (by positivity : 0 < (2 : ℕ) ^ J))
      (Nat.pow_le_pow_right (by decide) (by omega))).symm

/-- The total cost of dyadic shells is geometric rather than logarithmic. -/
theorem norm_sum_dyadic_shells_le {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (J : ℕ) (C : ℝ)
    (hlocal : ∀ j < J,
      ‖∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n‖ ≤ C * (2 : ℝ) ^ j) :
    ‖∑ n ∈ Finset.Ico 1 (2 ^ J), f n‖ ≤ C * ((2 : ℝ) ^ J - 1) := by
  rw [sum_dyadic_shells]
  calc
    ‖∑ j ∈ Finset.range J, ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n‖
        ≤ ∑ j ∈ Finset.range J, ‖∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, C * (2 : ℝ) ^ j :=
      Finset.sum_le_sum (fun j hj => hlocal j (Finset.mem_range.mp hj))
    _ = C * ((2 : ℝ) ^ J - 1) := by
      rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      norm_num

/-- Local bounds on the dyadic pieces of any positive integer interval sum
with constant at most two; useful for off-diagonal reciprocal phase estimates. -/
theorem norm_sum_interval_le_of_dyadic {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (Y X : ℕ) (hY : 1 ≤ Y) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ j : ℕ,
      ‖∑ n ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ Finset.Icc Y X), f n‖
        ≤ C * (2 : ℝ) ^ j) :
    ‖∑ n ∈ Finset.Icc Y X, f n‖ ≤ 2 * C * X := by
  classical
  by_cases hX : X = 0
  · subst X
    have hempty : Finset.Icc Y 0 = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    simp [hempty]
  let J := Nat.log 2 X + 1
  let g : ℕ → E := fun n => if n ∈ Finset.Icc Y X then f n else 0
  have htop : X < 2 ^ J := Nat.lt_pow_succ_log_self (by decide) X
  have hsub : Finset.Icc Y X ⊆ Finset.Ico 1 (2 ^ J) := by
    intro n hn
    obtain ⟨hYn, hnX⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hsum : (∑ n ∈ Finset.Icc Y X, f n) = ∑ n ∈ Finset.Ico 1 (2 ^ J), g n := by
    calc
      (∑ n ∈ Finset.Icc Y X, f n) = ∑ n ∈ Finset.Icc Y X, g n := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [g, ite_eq_left hn]
      _ = ∑ n ∈ Finset.Ico 1 (2 ^ J), g n :=
        Finset.sum_subset hsub (fun n _ hn => by simp only [g, ite_eq_right hn])
  rw [hsum]
  have hblock (j : ℕ) :
      (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), g n) =
        ∑ n ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ Finset.Icc Y X), f n := by
    simp only [g, ← Finset.sum_filter]
    congr 1
  have hbound := norm_sum_dyadic_shells_le g J C (fun j _ => by
    rw [hblock]
    exact hlocal j)
  have hpow : (2 : ℝ) ^ J ≤ 2 * (X : ℝ) := by
    have hh := Nat.pow_log_le_self 2 hX
    have hn : 2 ^ J ≤ 2 * X := by
      dsimp [J]
      rw [pow_succ]
      omega
    exact_mod_cast hn
  apply hbound.trans
  nlinarith

/-- Only dyadic intervals intersecting the target interval need local estimates.
Their base points lie between half the lower endpoint and the upper endpoint. -/
theorem norm_sum_interval_le_of_local_intervals {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (Y X : ℕ) (hY : 1 ≤ Y) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ U : ℕ, 0 < U → Y ≤ 2 * U → U ≤ X →
      ‖∑ n ∈ (Finset.Ico U (2 * U) ∩ Finset.Icc Y X), f n‖ ≤ C * U) :
    ‖∑ n ∈ Finset.Icc Y X, f n‖ ≤ 2 * C * X := by
  apply norm_sum_interval_le_of_dyadic f Y X hY C hC
  intro j
  by_cases hempty : Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ Finset.Icc Y X = ∅
  · rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    positivity
  · obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hd, hi⟩ := Finset.mem_inter.mp hn
    obtain ⟨hUn, hnU⟩ := Finset.mem_Ico.mp hd
    obtain ⟨hYn, hnX⟩ := Finset.mem_Icc.mp hi
    have hYbound : Y ≤ 2 * 2 ^ j := by
      rw [pow_succ] at hnU
      omega
    have hupper : 2 ^ j ≤ X := hUn.trans hnX
    have hh := hlocal (2 ^ j) (by positivity) hYbound hupper
    simpa [pow_succ, Nat.mul_comm] using hh

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DeterministicPhaseWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The dyadic pieces of a high residue level lie in the range where the
uniform reciprocal-phase estimate applies. -/
theorem deterministic_phase_window (S m D X U Z : ℝ)
    (hS : 0 ≤ S) (hSlarge : 10 * Real.log 2 ≤ S)
    (hm : m ≤ S) (hD : 255 ≤ D)
    (hXlower : Real.exp S ≤ X) (hXupper : X ≤ Real.exp (D * S / 4))
    (hUlower : Real.exp (-m / 10000) * X / 2 ≤ U) (hUupper : U ≤ X)
    (hZlower : Real.exp (D * S) ≤ |Z|)
    (hZupper : |Z| ≤ Real.exp ((2 * D + 102) * S)) :
    Real.exp (4 * S / 5) ≤ U ∧ U ^ 4 ≤ |Z| ∧ |Z| ≤ U ^ (3 * D) := by
  have hUexp : Real.exp (4 * S / 5) ≤ U := by
    calc
      Real.exp (4 * S / 5) ≤ Real.exp (S - m / 10000 - Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = Real.exp (-m / 10000) * Real.exp S / 2 := by
        rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          show -m / 10000 = -(m / 10000) by ring, Real.exp_neg]
        ring
      _ ≤ Real.exp (-m / 10000) * X / 2 := by
        gcongr
      _ ≤ U := hUlower
  have hUpos : 0 < U := (Real.exp_pos _).trans_le hUexp
  have hlogU : 4 * S / 5 ≤ Real.log U := by
    calc
      4 * S / 5 = Real.log (Real.exp (4 * S / 5)) := (Real.log_exp _).symm
      _ ≤ Real.log U := Real.log_le_log (Real.exp_pos _) hUexp
  refine ⟨hUexp, ?_, ?_⟩
  · calc
      U ^ 4 ≤ (Real.exp (D * S / 4)) ^ 4 := by
        gcongr
        exact hUupper.trans hXupper
      _ = Real.exp (D * S) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ |Z| := hZlower
  · apply hZupper.trans
    rw [Real.rpow_def_of_pos hUpos]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogU (show 0 ≤ 3 * D by linarith),
      mul_nonneg (show 0 ≤ D - 255 by linarith) hS]

/-- A local power saving becomes a uniform exponential saving throughout the
high-level dyadic window. -/
theorem power_saving_le_exponential (S U A δ : ℝ)
    (hU : Real.exp (4 * S / 5) ≤ U) (hA : 0 ≤ A) (hδ : 0 ≤ δ) :
    A * U ^ (1 - δ) ≤ A * U * Real.exp (-(4 * δ * S / 5)) := by
  have hUpos : 0 < U := (Real.exp_pos _).trans_le hU
  have hlogU : 4 * S / 5 ≤ Real.log U := by
    calc
      4 * S / 5 = Real.log (Real.exp (4 * S / 5)) := (Real.log_exp _).symm
      _ ≤ Real.log U := Real.log_le_log (Real.exp_pos _) hU
  have hdecay : U ^ (-δ) ≤ Real.exp (-(4 * δ * S / 5)) := by
    rw [Real.rpow_def_of_pos hUpos]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogU hδ]
  calc
    A * U ^ (1 - δ) = A * U * U ^ (-δ) := by
      rw [sub_eq_add_neg, Real.rpow_add hUpos, Real.rpow_one]
      ring
    _ ≤ A * U * Real.exp (-(4 * δ * S / 5)) :=
      mul_le_mul_of_nonneg_left hdecay (mul_nonneg hA hUpos.le)

/-- The frequency occurring in an off-diagonal prime-subset pair has the
required exponential bounds. Distinctness, not primality, is needed here. -/
theorem deterministic_frequency_bounds (S m D C l : ℝ) (t t' : ℕ)
    (hS : 0 ≤ S) (hm : m ≤ S) (hlower : 1 ≤ l)
    (hlupper : l ≤ Real.exp (m / 2500))
    (hClower : Real.exp (D * S) ≤ C) (hCupper : C ≤ Real.exp (2 * D * S))
    (ht : (t : ℝ) ≤ Real.exp (101 * S))
    (ht' : (t' : ℝ) ≤ Real.exp (101 * S)) (hne : t ≠ t') :
    Real.exp (D * S) ≤ |l * C * ((t : ℝ) - t')| ∧
      |l * C * ((t : ℝ) - t')| ≤ Real.exp ((2 * D + 102) * S) := by
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hClower
  have hlpos : 0 < l := by linarith
  have hdiff : (1 : ℝ) ≤ |(t : ℝ) - t'| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (t : ℝ) + 1 ≤ t' := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith : (t : ℝ) - t' ≤ 0)]
      linarith
    · have hh : (t' : ℝ) + 1 ≤ t := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith : 0 ≤ (t : ℝ) - t')]
      linarith
  have hdiffupper : |(t : ℝ) - t'| ≤ Real.exp (101 * S) := by
    apply abs_le.mpr
    constructor <;> linarith [show (0 : ℝ) ≤ t by positivity,
      show (0 : ℝ) ≤ t' by positivity]
  have hlupper' : l ≤ Real.exp S := hlupper.trans (Real.exp_le_exp.mpr (by linarith))
  rw [abs_mul, abs_of_pos (mul_pos hlpos hCpos)]
  constructor
  · calc
      Real.exp (D * S) ≤ C := hClower
      _ = 1 * C * 1 := by ring
      _ ≤ l * C * |(t : ℝ) - t'| := by gcongr
  · calc
      l * C * |(t : ℝ) - t'| ≤
          Real.exp S * Real.exp (2 * D * S) * Real.exp (101 * S) := by gcongr
      _ = Real.exp ((2 * D + 102) * S) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Summation over dyadic pieces preserves the uniform exponential saving. -/
theorem deterministic_phase_sum_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (Y X : ℕ) (S A δ : ℝ) (hY : 1 ≤ Y)
    (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hYlarge : Real.exp (4 * S / 5) ≤ (Y : ℝ) / 2)
    (hlocal : ∀ U : ℕ, 0 < U → Y ≤ 2 * U → U ≤ X →
      ‖∑ n ∈ (Finset.Ico U (2 * U) ∩ Finset.Icc Y X), f n‖ ≤
        A * (U : ℝ) ^ (1 - δ)) :
    ‖∑ n ∈ Finset.Icc Y X, f n‖ ≤
      2 * A * (X : ℝ) * Real.exp (-(4 * δ * S / 5)) := by
  have hh := norm_sum_interval_le_of_local_intervals f Y X hY
    (A * Real.exp (-(4 * δ * S / 5))) (by positivity) (fun U hU hYU hUX => by
      have hYUr : (Y : ℝ) ≤ 2 * U := by exact_mod_cast hYU
      have hUexp : Real.exp (4 * S / 5) ≤ (U : ℝ) :=
        hYlarge.trans (by linarith)
      apply (hlocal U hU hYU hUX).trans
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (power_saving_le_exponential S U A δ hUexp hA hδ))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FinitePowerSaving
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace Problem337

/-- A finite collection of eventual power-saving estimates admits a single
positive saving, coefficient, and threshold. Auxiliary parameters are left
arbitrary, so an interval and a reciprocal-phase numerator can be included. -/
theorem finite_uniform_rpow_saving {ι α : Type*} (s : Finset ι)
    (f : ι → ℝ → α → ℝ) (P : ι → ℝ → α → Prop) (p : ℝ)
    (h : ∀ i ∈ s, ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ,
      ∀ U : ℝ, T ≤ U → ∀ z : α, P i U z → f i U z ≤ A * U ^ (p - δ)) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ, 1 ≤ T ∧
      ∀ i ∈ s, ∀ U : ℝ, T ≤ U → ∀ z : α,
        P i U z → f i U z ≤ A * U ^ (p - δ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, 1, by norm_num, by norm_num, 1, le_rfl, ?_⟩
    simp
  | @insert a s ha ih =>
    obtain ⟨A, δ, hA, hδ, T, hbound⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨B, ε, hB, hε, V, hV, hrest⟩ :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨max A B, min δ ε, lt_of_lt_of_le hA (le_max_left _ _),
      lt_min hδ hε, max T V, le_trans hV (le_max_right _ _), ?_⟩
    intro i hi U hU z hz
    have hUT : T ≤ U := le_trans (le_max_left _ _) hU
    have hUV : V ≤ U := le_trans (le_max_right _ _) hU
    have hU1 : 1 ≤ U := le_trans hV hUV
    have hpow : 0 ≤ U ^ (p - min δ ε) := Real.rpow_nonneg (by linarith) _
    rcases Finset.mem_insert.mp hi with hia | hi
    · subst i
      calc
        f a U z ≤ A * U ^ (p - δ) := hbound U hUT z hz
        _ ≤ A * U ^ (p - min δ ε) := by
          apply mul_le_mul_of_nonneg_left _ hA.le
          apply Real.rpow_le_rpow_of_exponent_le hU1
          exact sub_le_sub_left (min_le_left δ ε) p
        _ ≤ max A B * U ^ (p - min δ ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
    · calc
        f i U z ≤ B * U ^ (p - ε) := hrest i hi U hUV z hz
        _ ≤ B * U ^ (p - min δ ε) := by
          apply mul_le_mul_of_nonneg_left _ hB.le
          apply Real.rpow_le_rpow_of_exponent_le hU1
          exact sub_le_sub_left (min_le_right δ ε) p
        _ ≤ max A B * U ^ (p - min δ ε) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow

/-- Uniformisation over the bounded collection of derivative orders used for
reciprocal phases. This also covers an empty order interval. -/
theorem finite_derivative_order_power_saving {α : Type*} (Q : ℕ)
    (f : ℕ → ℝ → α → ℝ) (P : ℕ → ℝ → α → Prop)
    (h : ∀ k : ℕ, 4 ≤ k → k ≤ Q →
      ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ,
        ∀ U : ℝ, T ≤ U → ∀ z : α, P k U z → f k U z ≤ A * U ^ (1 - δ)) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ, 1 ≤ T ∧
      ∀ k : ℕ, 4 ≤ k → k ≤ Q → ∀ U : ℝ, T ≤ U → ∀ z : α,
        P k U z → f k U z ≤ A * U ^ (1 - δ) := by
  obtain ⟨A, δ, hA, hδ, T, hT, hb⟩ :=
    finite_uniform_rpow_saving (Finset.Icc 4 Q) f P 1
      (fun k hk => h k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
  exact ⟨A, δ, hA, hδ, T, hT, fun k hk hQ => hb k (Finset.mem_Icc.mpr ⟨hk, hQ⟩)⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalDifferencingBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter

namespace Problem337

/-- The natural cutoff in van der Corput differencing preserves a power saving.
All size conditions here are scalar and hold eventually for fixed parameters. -/
theorem reciprocal_differencing_budget (r N : ℕ) (U α C : ℝ)
    (hU : 1 ≤ U) (_hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hcut : 4 ≤ U ^ α)
    (herror : C * U ^ (-(1 : ℝ) / 5) ≤ 4 * U ^ (-α))
    (hUN : U ≤ (N : ℝ)) (hNU : (N : ℝ) ≤ 3 * U)
    (a : ℤ → ℂ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hterminal : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ α) : ℤ)) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ ≤
        C * U ^ ((4 : ℝ) / 5)) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ≤
      36 * U ^ (1 - α / (2 : ℝ) ^ r) := by
  let H : ℕ := Nat.floor (U ^ α)
  have hUpos : 0 < U := by linarith
  have hNpos : 0 < (N : ℝ) := hUpos.trans_le hUN
  have hp : 0 < U ^ α := Real.rpow_pos_of_pos hUpos α
  have hH : 1 ≤ H := (Nat.le_floor_iff hp.le).2 (by norm_num; linarith)
  have hHR : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hHle : (H : ℝ) ≤ U ^ α := Nat.floor_le hp.le
  have hHN : H ≤ N := by
    have hpU : U ^ α ≤ U := by
      simpa using Real.rpow_le_rpow_of_exponent_le hU hα1
    exact_mod_cast hHle.trans (hpU.trans hUN)
  have hhalf : U ^ α ≤ 2 * (H : ℝ) := by
    have hfloor : U ^ α < (H : ℝ) + 1 := Nat.lt_floor_add_one _
    have hone : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hinv : U ^ (-α) = 1 / U ^ α := by rw [Real.rpow_neg hUpos.le, one_div]
  have hHerror : 2 / (H : ℝ) ≤ 4 * U ^ (-α) := by
    rw [hinv, mul_one_div]
    apply (div_le_div_iff₀ hHR hp).2
    nlinarith
  have heps : 0 < 4 * U ^ (-α) := by positivity
  have heps1 : 4 * U ^ (-α) ≤ 1 := by
    rw [hinv, mul_one_div]
    exact (div_le_one hp).2 hcut
  have hterminal' : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ / (N : ℝ) ≤
        4 * U ^ (-α) := by
    intro hs hlen hsteps
    calc
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ / (N : ℝ) ≤
          (C * U ^ ((4 : ℝ) / 5)) / (N : ℝ) :=
        div_le_div_of_nonneg_right (hterminal hs hlen hsteps) hNpos.le
      _ ≤ (C * U ^ ((4 : ℝ) / 5)) / U :=
        div_le_div_of_nonneg_left (by positivity) hUpos hUN
      _ = C * U ^ (-(1 : ℝ) / 5) := by
        have heq : U ^ ((4 : ℝ) / 5) / U = U ^ (-(1 : ℝ) / 5) := by
          calc
            U ^ ((4 : ℝ) / 5) / U = U ^ ((4 : ℝ) / 5) / U ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = U ^ ((4 : ℝ) / 5 - 1) := (Real.rpow_sub hUpos _ _).symm
            _ = U ^ (-(1 : ℝ) / 5) := by norm_num
        rw [mul_div_assoc, heq]
      _ ≤ 4 * U ^ (-α) := herror
  have hnormsum := iterated_differencing_power_bound r N H hH hHN
    (4 * U ^ (-α)) heps heps1 hHerror a hsupport hnorm hterminal'
  have hexp : 0 < 1 / (2 : ℝ) ^ r := by positivity
  have hexp1 : 1 / (2 : ℝ) ^ r ≤ 1 := by
    exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hfour : (4 : ℝ) ^ (1 / (2 : ℝ) ^ r) ≤ 4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hexp1
  have hpower : (4 * U ^ (-α)) ^ (1 / (2 : ℝ) ^ r) ≤
      4 * U ^ (-α / (2 : ℝ) ^ r) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hUpos.le]
    have heq : -α * (1 / (2 : ℝ) ^ r) = -α / (2 : ℝ) ^ r := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hfour (by positivity)
  have hraw := (div_le_iff₀ hNpos).1 hnormsum
  calc
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ≤
        (3 * (4 * U ^ (-α)) ^ (1 / (2 : ℝ) ^ r)) * (N : ℝ) := hraw
    _ ≤ (3 * (4 * U ^ (-α / (2 : ℝ) ^ r))) * (3 * U) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpower (by norm_num))
        hNU hNpos.le (by positivity)
    _ = 36 * U ^ (1 - α / (2 : ℝ) ^ r) := by
      rw [sub_eq_add_neg, Real.rpow_add hUpos, Real.rpow_one]
      simp only [neg_div]
      ring

/-- For fixed parameters the scalar cutoff conditions are automatic. -/
theorem reciprocal_differencing_budget_eventually (r : ℕ) (α C : ℝ)
    (hα : 0 < α) (hαsmall : α < (1 : ℝ) / 5) (hC : 0 ≤ C) :
    ∀ᶠ (U : ℝ) in atTop, ∀ N : ℕ,
      U ≤ (N : ℝ) → (N : ℝ) ≤ 3 * U → ∀ a : ℤ → ℂ,
      (∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0) →
      (∀ n : ℤ, ‖a n‖ ≤ 1) →
      (∀ hs : List ℤ, hs.length = r →
        (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ α) : ℤ)) →
        ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ ≤
          C * U ^ ((4 : ℝ) / 5)) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ≤
        36 * U ^ (1 - α / (2 : ℝ) ^ r) := by
  have hcut := (tendsto_rpow_atTop hα).eventually_ge_atTop (4 : ℝ)
  have hconst := (tendsto_rpow_atTop
    (show 0 < (1 : ℝ) / 5 - α by linarith)).eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop (1 : ℝ), hcut, hconst] with U hU hcut hconst
  have hUpos : 0 < U := by linarith
  have herror : C * U ^ (-(1 : ℝ) / 5) ≤ 4 * U ^ (-α) := by
    calc
      C * U ^ (-(1 : ℝ) / 5) ≤
          U ^ ((1 : ℝ) / 5 - α) * U ^ (-(1 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = U ^ (-α) := by
        rw [← Real.rpow_add hUpos]
        congr 1
        ring
      _ ≤ 4 * U ^ (-α) := by
        have : 0 ≤ U ^ (-α) := Real.rpow_nonneg hUpos.le _
        linarith
  intro N hUN hNU a hsupport hnorm hterminal
  exact reciprocal_differencing_budget r N U α C hU hα (by linarith)
    hC hcut herror hUN hNU a hsupport hnorm hterminal

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalPhaseScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Choose a bounded derivative order placing the reciprocal phase in the
second-derivative scale after differencing. -/
theorem reciprocal_phase_order {U Z B : ℝ} (hU : 1 < U) (_hB : 4 ≤ B)
    (hlower : U ^ (4 : ℕ) ≤ |Z|) (hupper : |Z| ≤ U ^ B) :
    ∃ k : ℕ, 4 ≤ k ∧ k ≤ Nat.ceil B + 1 ∧
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) ∧
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) := by
  have hU0 : 0 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hZ0 : 0 < |Z| := (pow_pos hU0 4).trans_le hlower
  let a : ℝ := Real.log |Z| / Real.log U
  have ha4 : 4 ≤ a := by
    apply (le_div_iff₀ hlogU).2
    have h := Real.log_le_log (pow_pos hU0 4) hlower
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have haB : a ≤ B := by
    apply (div_le_iff₀ hlogU).2
    have h := Real.log_le_log hZ0 hupper
    rwa [Real.log_rpow hU0] at h
  let k : ℕ := Nat.floor (a + 1 / 2)
  have ha0 : 0 ≤ a + 1 / 2 := by linarith
  have hklo : (k : ℝ) ≤ a + 1 / 2 := Nat.floor_le ha0
  have hkhi : a + 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk4 : 4 ≤ k := (Nat.le_floor_iff ha0).2 (by norm_num; linarith)
  have hkB : k ≤ Nat.ceil B + 1 := by
    have hceil := Nat.le_ceil B
    have h : (k : ℝ) ≤ (Nat.ceil B : ℝ) + 1 := by linarith
    exact_mod_cast h
  have hZa : |Z| = U ^ a := by
    rw [Real.rpow_def_of_pos hU0]
    have heq : Real.log U * a = Real.log |Z| := by
      dsimp [a]
      field_simp
    rw [heq, Real.exp_log hZ0]
  refine ⟨k, hk4, hkB, ?_, ?_⟩ <;>
    rw [hZa, ← Real.rpow_add hU0]
  · exact Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)

/-- The product of a bounded number of short shifts costs at most `U^(1/10)`. -/
theorem reciprocal_shift_product {U : ℝ} (hU : 1 < U) {k : ℕ} (hk : 1 ≤ k)
    (hs : List ℝ) (hlen : hs.length ≤ k)
    (hhs : ∀ h ∈ hs, 1 ≤ h ∧ h ≤ U ^ (1 / (10 * (k : ℝ)))) :
    1 ≤ hs.prod ∧ hs.prod ≤ U ^ ((1 : ℝ) / 10) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hU0 : 0 < U := by linarith
  refine ⟨List.one_le_prod (fun h hh => (hhs h hh).1), ?_⟩
  have hp : hs.prod ≤ (U ^ (1 / (10 * (k : ℝ)))) ^ hs.length := by
    have h := List.prod_map_le_prod_map₀ (s := hs) (fun x : ℝ => x)
      (fun _ => U ^ (1 / (10 * (k : ℝ))))
      (fun h hh => le_trans (by norm_num) (hhs h hh).1)
      (fun h hh => (hhs h hh).2)
    simpa [List.map_const, List.prod_replicate] using h
  rw [← Real.rpow_mul_natCast hU0.le] at hp
  apply hp.trans
  apply Real.rpow_le_rpow_of_exponent_le hU.le
  have hlenR : (hs.length : ℝ) ≤ k := by exact_mod_cast hlen
  calc
    1 / (10 * (k : ℝ)) * (hs.length : ℝ) = (hs.length : ℝ) / (10 * (k : ℝ)) := by ring
    _ ≤ 1 / 10 := (div_le_iff₀ (by positivity)).2 (by nlinarith)

/-- The derivative scale after the short shifts is uniformly a small negative power. -/
theorem reciprocal_phase_shift_scale {U Z : ℝ} (hU : 1 < U) {k : ℕ} (hk : 1 ≤ k)
    (hlower : U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)))
    (hupper : |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2))
    (hs : List ℝ) (hlen : hs.length ≤ k)
    (hhs : ∀ h ∈ hs, 1 ≤ h ∧ h ≤ U ^ (1 / (10 * (k : ℝ)))) :
    U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ∧
    |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ≤ U ^ (-(2 : ℝ) / 5) := by
  have hU0 : 0 < U := by linarith
  obtain ⟨hplo, hphi⟩ := reciprocal_shift_product hU hk hs hlen hhs
  have hbase0 : 0 ≤ |Z| * U ^ (-((k : ℝ) + 1)) := by positivity
  constructor
  · exact hlower.trans (le_mul_of_one_le_right hbase0 hplo)
  · calc
      |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ≤
          U ^ (-(1 : ℝ) / 2) * U ^ ((1 : ℝ) / 10) :=
        mul_le_mul hupper hphi (by linarith) (by positivity)
      _ = U ^ (-(2 : ℝ) / 5) := by rw [← Real.rpow_add hU0]; norm_num

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalPhasePreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Scalar terminal estimate for a second-derivative bound. -/
theorem reciprocal_terminal_error_bound {U a b Λ : ℝ} (hU : 1 ≤ U)
    (ha : 0 < a) (hb : 0 ≤ b)
    (hlower : a * U ^ (-(3 : ℝ) / 2) ≤ Λ)
    (hupper : Λ ≤ b * U ^ (-(2 : ℝ) / 5)) :
    U * Λ ^ ((1 : ℝ) / 2) + Λ ^ (-(1 : ℝ) / 2) + 1 ≤
      (b ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1) * U ^ ((4 : ℝ) / 5) := by
  have hU0 : 0 < U := by linarith
  have hΛ : 0 < Λ := (mul_pos ha (Real.rpow_pos_of_pos hU0 _)).trans_le hlower
  have hroot := Real.rpow_le_rpow hΛ.le hupper (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Real.mul_rpow hb (by positivity), ← Real.rpow_mul hU0.le] at hroot
  norm_num at hroot
  have hfirst : U * Λ ^ ((1 : ℝ) / 2) ≤ b ^ ((1 : ℝ) / 2) * U ^ ((4 : ℝ) / 5) := by
    calc
      U * Λ ^ ((1 : ℝ) / 2) ≤ U * (b ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left (by simpa only [neg_div] using hroot) hU0.le
      _ = b ^ ((1 : ℝ) / 2) * U ^ ((4 : ℝ) / 5) := by
        rw [mul_left_comm]
        congr 1
        calc
          U * U ^ (-(1 : ℝ) / 5) = U ^ (1 : ℝ) * U ^ (-(1 : ℝ) / 5) := by rw [Real.rpow_one]
          _ = U ^ ((1 : ℝ) + -(1 : ℝ) / 5) := (Real.rpow_add hU0 _ _).symm
          _ = U ^ ((4 : ℝ) / 5) := by norm_num
  have hinv := Real.rpow_le_rpow_of_nonpos
    (mul_pos ha (Real.rpow_pos_of_pos hU0 _)) hlower
    (by norm_num : (-(1 : ℝ) / 2) ≤ 0)
  rw [Real.mul_rpow ha.le (by positivity), ← Real.rpow_mul hU0.le] at hinv
  norm_num at hinv
  have hsecond : Λ ^ (-(1 : ℝ) / 2) ≤ a ^ (-(1 : ℝ) / 2) * U ^ ((4 : ℝ) / 5) := by
    simpa only [neg_div] using hinv.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU (by norm_num : (3 : ℝ) / 4 ≤ 4 / 5)) (by positivity))
  have hone : 1 ≤ U ^ ((4 : ℝ) / 5) := Real.one_le_rpow hU (by norm_num)
  nlinarith

/-- Flexible range factor in the normalized second-derivative comparison.
Taking `C=3` or `C=4` accommodates endpoint samples without dropping terms. -/
theorem reciprocal_second_derivative_comparison_general (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (Z C : ℝ) {U x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxend : x + hs.sum ≤ C * U) :
    let k := hs.length + 2
    let Λ := |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod
    (k.factorial : ℝ) / C ^ (k + 1) * Λ ≤
      |iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)) x| ∧
    |iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)) x| ≤
      (k.factorial : ℝ) * Λ := by
  dsimp only
  have hpow : U ^ (-(((hs.length + 2 : ℕ) : ℝ) + 1)) = 1 / U ^ (hs.length + 2 + 1) := by
    rw [Real.rpow_neg hU.le]
    norm_cast
    simp only [one_div]
  rw [hpow]
  obtain ⟨hl, hu⟩ := reciprocal_forwardDifference_derivative_bounds_interval 2 hs hhs Z hU hx hxend
  constructor
  · convert hl using 1
    all_goals try with_reducible_and_instances rfl
    rw [mul_pow]
    ring
  · convert hu using 1
    all_goals try with_reducible_and_instances rfl
    ring

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalPhaseCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Problem337

/-- Ambient normalization converts a terminal forward-difference estimate
on every shortened subinterval into cancellation on the original interval. -/
theorem reciprocal_interval_budget_eventually (r : ℕ) (α C : ℝ)
    (hα : 0 < α) (hαsmall : α < (1 : ℝ) / 5) (hC : 0 ≤ C) :
    ∀ᶠ (U : ℝ) in atTop, ∀ (L R : ℤ), U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ∀ f : ℝ → ℝ,
      (∀ hs : List ℤ, hs.length = r →
        (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ α) : ℤ)) →
        ‖∑ n ∈ Finset.Icc L (R - hs.sum),
          differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ))) f n)‖ ≤
          C * U ^ ((4 : ℝ) / 5)) →
      ‖∑ n ∈ Finset.Icc L R, differencingPhase (f n)‖ ≤
        36 * U ^ (1 - α / (2 : ℝ) ^ r) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    reciprocal_differencing_budget_eventually r α C hα hαsmall hC] with U hU hbudget
  intro L R hUL hRU f hterminal
  let N : ℕ := Nat.ceil (2 * U)
  have hUN : U ≤ (N : ℝ) := by
    have hceil : 2 * U ≤ (N : ℝ) := Nat.le_ceil _
    linarith
  have hNU : (N : ℝ) ≤ 3 * U := by
    have hceil : (N : ℝ) < 2 * U + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hL : (1 : ℤ) ≤ L := by exact_mod_cast hU.trans hUL
  have hR : R ≤ (N : ℤ) := by
    have hceil : 2 * U ≤ (N : ℝ) := Nat.le_ceil _
    exact_mod_cast hRU.trans hceil
  have hsupp : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → intervalPhase f L R n = 0 := by
    intro n hn
    have hout : ¬ (L ≤ n ∧ n ≤ R) := by
      simp only [Finset.mem_Icc] at hn
      omega
    simp [intervalPhase, hout]
  have hnrm : ∀ n : ℤ, ‖intervalPhase f L R n‖ ≤ 1 := by
    intro n
    unfold intervalPhase
    split_ifs <;> simp
  have hb := hbudget N hUN hNU (intervalPhase f L R) hsupp hnrm (by
    intro hs hlen hsteps
    have hnonneg : ∀ h ∈ hs, 0 ≤ h := fun h hh => (hsteps h hh).1.le
    rw [iteratedCorrelation_intervalPhase hs f L R hnonneg]
    have hsum : 0 ≤ hs.sum := List.sum_nonneg hnonneg
    rw [intervalPhase_sum _ L (R - hs.sum) 1 N hL (by omega)]
    exact hterminal hs hlen hsteps)
  rwa [intervalPhase_sum f L R 1 N hL hR] at hb

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalPhaseUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Problem337

/-- For a bounded range of reciprocal-phase numerators, fixed-order terminal
estimates give one positive power saving uniformly in the numerator and interval.
All analytic hypotheses are confined to the explicit terminal estimate. -/
theorem reciprocal_phase_uniform_of_terminal
    (hterminal : ∀ k : ℕ, 4 ≤ k → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ U : ℝ in atTop, ReciprocalTerminalPowerBound k C U)
    (B : ℝ) (hB : 4 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (Z : ℝ) (L R : ℤ),
        U ^ (4 : ℕ) ≤ |Z| → |Z| ≤ U ^ B →
        U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
        ‖∑ n ∈ Finset.Icc L R, differencingPhase (Z / (n : ℝ))‖ ≤
          A * U ^ (1 - δ) := by
  let F : ℕ → ℝ → (ℝ × ℤ × ℤ) → ℝ := fun _ _ z =>
    ‖∑ n ∈ Finset.Icc z.2.1 z.2.2, differencingPhase (z.1 / (n : ℝ))‖
  let P : ℕ → ℝ → (ℝ × ℤ × ℤ) → Prop := fun k U z =>
    U ^ (-(3 : ℝ) / 2) ≤ |z.1| * U ^ (-((k : ℝ) + 1)) ∧
    |z.1| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) ∧
    U ≤ (z.2.1 : ℝ) ∧ (z.2.2 : ℝ) ≤ 2 * U
  have horders : ∀ k : ℕ, 4 ≤ k → k ≤ Nat.ceil B + 1 →
      ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ,
        ∀ U : ℝ, T ≤ U → ∀ z : ℝ × ℤ × ℤ,
          P k U z → F k U z ≤ A * U ^ (1 - δ) := by
    intro k hk _
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkfour : (4 : ℝ) ≤ k := by exact_mod_cast hk
    let α : ℝ := 1 / (10 * (k : ℝ))
    have hα : 0 < α := by dsimp [α]; positivity
    have hαsmall : α < (1 : ℝ) / 5 := by
      dsimp [α]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 10 * k)).2
      nlinarith
    obtain ⟨C, hC, hterm⟩ := hterminal k hk
    have hb := reciprocal_interval_budget_eventually (k - 2) α C hα hαsmall hC
    obtain ⟨T, hT⟩ := eventually_atTop.mp (hterm.and hb)
    refine ⟨36, α / (2 : ℝ) ^ (k - 2), by norm_num, by positivity, T, ?_⟩
    intro U hU z hz
    obtain ⟨ht, hb⟩ := hT U hU
    exact hb z.2.1 z.2.2 hz.2.2.1 hz.2.2.2 (fun x => z.1 / x)
      (ht z.1 hz.1 hz.2.1 z.2.1 z.2.2 hz.2.2.1 hz.2.2.2)
  obtain ⟨A, δ, hA, hδ, T, _, hbound⟩ :=
    finite_derivative_order_power_saving (Nat.ceil B + 1) F P horders
  refine ⟨A, δ, hA, hδ, ?_⟩
  filter_upwards [eventually_ge_atTop T, eventually_gt_atTop (1 : ℝ)] with U hU hUone
  intro Z L R hlo hhi hL hR
  obtain ⟨k, hk, hkB, hklo, hkhi⟩ := reciprocal_phase_order hUone hB hlo hhi
  exact hbound k hk hkB U hU (Z, L, R) ⟨hklo, hkhi, hL, hR⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalPhaseRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Set
open scoped ContDiff

namespace Problem337

/-- Every derivative of a smooth forward difference stays smooth on the
positive half-line. -/
theorem forwardDifference_iteratedDeriv_contDiffOn (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) :
    ContDiffOn ℝ ∞ (iteratedDeriv k (forwardDifference hs f)) (Ioi 0) := by
  induction k with
  | zero => simpa using forwardDifference_contDiffOn hs hhs hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

/-- Local regularity in the exact pointwise form used by a second derivative
test. No global smoothness at zero is asserted. -/
theorem forwardDifference_iteratedDeriv_hasDerivAt (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedDeriv k (forwardDifference hs f))
      (iteratedDeriv (k + 1) (forwardDifference hs f) x) x := by
  rw [iteratedDeriv_succ]
  exact ((forwardDifference_iteratedDeriv_contDiffOn k hs hhs hf).contDiffAt
    (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp) |>.hasDerivAt

/-- Pointwise derivatives of every order of a differenced reciprocal phase. -/
theorem reciprocal_forwardDifference_hasDerivAt (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedDeriv k (forwardDifference hs (fun y => Z / y)))
      (iteratedDeriv (k + 1) (forwardDifference hs (fun y => Z / y)) x) x := by
  apply forwardDifference_iteratedDeriv_hasDerivAt k hs hhs _ hx
  exact contDiffOn_const.div contDiffOn_id (fun y hy => ne_of_gt hy)

/-- Paired first and second derivatives for the continuous second derivative test. -/
theorem reciprocal_forwardDifference_second_derivative_data (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (forwardDifference hs (fun y => Z / y))
      (iteratedDeriv 1 (forwardDifference hs (fun y => Z / y)) x) x ∧
    HasDerivAt (iteratedDeriv 1 (forwardDifference hs (fun y => Z / y)))
      (iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)) x) x := by
  constructor
  · simpa using reciprocal_forwardDifference_hasDerivAt 0 hs hhs Z hx
  · exact reciprocal_forwardDifference_hasDerivAt 1 hs hhs Z hx

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DiscreteFirstDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.ExponentialSum

lemma phase_norm (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cot_antitone_unit {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    Real.cot (Real.pi * y) ≤ Real.cot (Real.pi * x) := by
  have hpi := Real.pi_pos
  have hxpi : 0 < Real.pi * x := mul_pos hpi hx
  have hypi : 0 < Real.pi * y := by nlinarith
  have hxpi' : Real.pi * x < Real.pi := by nlinarith
  have hypi' : Real.pi * y < Real.pi := by nlinarith
  have hsx := Real.sin_pos_of_pos_of_lt_pi hxpi hxpi'
  have hsy := Real.sin_pos_of_pos_of_lt_pi hypi hypi'
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ hsy hsx).2
  have hs : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> nlinarith
  rw [Real.sin_sub] at hs
  nlinarith

lemma sin_pi_lower {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    2 * β ≤ Real.sin (Real.pi * x) := by
  have hp := Real.pi_pos
  by_cases hx : x ≤ 1 / 2
  · have h := Real.mul_le_sin (x := Real.pi * x) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at h
    linarith
  · have h := Real.mul_le_sin (x := Real.pi * (1 - x)) (by nlinarith) (by nlinarith)
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq] at h
    have harg : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
    rw [harg, Real.sin_pi_sub] at h
    linarith

lemma abs_cot_pi_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    |Real.cot (Real.pi * x)| ≤ 1 / (2 * β) := by
  have hs := sin_pi_lower hβ hlo hhi
  have hsp : 0 < Real.sin (Real.pi * x) := by linarith
  rw [Real.cot_eq_cos_div_sin, abs_div, abs_of_pos hsp]
  exact (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hsp.le).trans
    (one_div_le_one_div_of_le (by positivity) hs)

lemma phaseWeight_identity {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (phase x - 1) * phaseWeight x = 1 := by
  have hs : Real.sin (Real.pi * x) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos]))
  unfold phase phaseWeight
  rw [Complex.exp_ofReal_mul_I]
  rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
  rw [Real.sin_two_mul, Real.cos_two_mul, Real.cot_eq_cos_div_sin]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_div]
  have hsc : (Real.sin (Real.pi * x) : ℂ) ^ 2 + (Real.cos (Real.pi * x) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (Real.pi * x)
  have hsC : (Real.sin (Real.pi * x) : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp
  ring_nf
  norm_num only [Complex.ofReal_one, Complex.I_sq]
  linear_combination -2 * (Real.cos (Real.pi * x) : ℂ) * Complex.I * hsc

lemma phaseWeight_norm_le {β x : ℝ} (hβ : 0 < β) (hlo : β ≤ x) (hhi : x ≤ 1 - β) :
    ‖phaseWeight x‖ ≤ 1 / 2 + 1 / (4 * β) := by
  have hc := abs_cot_pi_le hβ hlo hhi
  have hn2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  calc
    ‖phaseWeight x‖ ≤ ‖-(1 : ℂ) / 2‖ + ‖(Real.cot (Real.pi * x) : ℂ) * Complex.I / 2‖ :=
      norm_sub_le _ _
    _ = 1 / 2 + |Real.cot (Real.pi * x)| / 2 := by
      simp only [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, hn2, mul_one]
    _ ≤ 1 / 2 + (1 / (2 * β)) / 2 := by gcongr
    _ = 1 / 2 + 1 / (4 * β) := by ring

lemma phaseWeight_difference_norm {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) :
    ‖phaseWeight x - phaseWeight y‖ =
      (Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 := by
  have hc := cot_antitone_unit hx hxy hy
  have heq : phaseWeight x - phaseWeight y =
      (((Real.cot (Real.pi * x) - Real.cot (Real.pi * y)) / 2 : ℝ) : ℂ) * (-Complex.I) := by
    unfold phaseWeight
    push_cast
    ring
  rw [heq, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

lemma phase_step_weight (f : ℕ → ℝ) (i : ℕ)
    (hlo : 0 < f (i + 1) - f i) (hhi : f (i + 1) - f i < 1) :
    (phase (f (i + 1)) - phase (f i)) * phaseWeight (f (i + 1) - f i) = phase (f i) := by
  have heq : phase (f (i + 1)) = phase (f i) * phase (f (i + 1) - f i) := by
    rw [← phase_add]
    congr 1
    ring
  rw [heq]
  calc
    (phase (f i) * phase (f (i + 1) - f i) - phase (f i)) *
        phaseWeight (f (i + 1) - f i) =
      phase (f i) * ((phase (f (i + 1) - f i) - 1) * phaseWeight (f (i + 1) - f i)) := by ring
    _ = phase (f i) := by rw [phaseWeight_identity hlo hhi, mul_one]

/-- Summation by parts for a sequence whose differences have a reciprocal weight. -/
lemma weighted_telescope (z w : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ i < N, (z (i + 1) - z i) * w i = z i) :
    (∑ i ∈ Finset.range N, z i) = z N * w N - z 0 * w 0 +
      ∑ i ∈ Finset.range N, z (i + 1) * (w i - w (i + 1)) := by
  calc
    (∑ i ∈ Finset.range N, z i) =
        ∑ i ∈ Finset.range N,
          ((z (i + 1) * w (i + 1) - z i * w i) + z (i + 1) * (w i - w (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hstep i (Finset.mem_range.mp hi)
      linear_combination -h
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun i => z i * w i)]

/-- A discrete first-derivative estimate (Kusmin--Landau): monotone consecutive
phase increments, uniformly separated from the integers, force cancellation.
The last increment is included to make the endpoint formula uniform, including `N=0`. -/
theorem first_derivative_sum_bound (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (hlo : ∀ i ≤ N, β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range N, phase (f i)‖ ≤ 2 / β := by
  let d : ℕ → ℝ := fun i => f (i + 1) - f i
  let w : ℕ → ℂ := fun i => phaseWeight (d i)
  have hdlo : ∀ i ≤ N, 0 < d i := fun i hi => lt_of_lt_of_le hβ (hlo i hi)
  have hdhi : ∀ i ≤ N, d i < 1 := by intro i hi; have := hhi i hi; dsimp [d]; linarith
  have htel := weighted_telescope (fun i => phase (f i)) w N (by
    intro i hi
    exact phase_step_weight f i (hdlo i hi.le) (hdhi i hi.le))
  have hvariation : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
      (Real.cot (Real.pi * d 0) - Real.cot (Real.pi * d N)) / 2 := by
    calc
      (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) =
          ∑ i ∈ Finset.range N,
            (Real.cot (Real.pi * d i) - Real.cot (Real.pi * d (i + 1))) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i < N := Finset.mem_range.mp hi
        exact phaseWeight_difference_norm (hdlo i hiN.le)
          (hmono (show i ≤ N from hiN.le) (show i + 1 ≤ N by omega) (by omega)) (hdhi (i + 1) (by omega))
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_sub']
  have hc0 := abs_cot_pi_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hcN := abs_cot_pi_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hvbound : (∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖) ≤ 1 / (2 * β) := by
    rw [hvariation]
    have h0 := (abs_le.mp hc0).2
    have hN := (abs_le.mp hcN).1
    change Real.cot (Real.pi * d 0) ≤ _ at h0
    change _ ≤ Real.cot (Real.pi * d N) at hN
    linarith
  have hw0 := phaseWeight_norm_le hβ (hlo 0 (Nat.zero_le N)) (hhi 0 (Nat.zero_le N))
  have hwN := phaseWeight_norm_le hβ (hlo N le_rfl) (hhi N le_rfl)
  have hsum : ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ ≤
      ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, ‖phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, phase_norm, one_mul]
  have hβle : β ≤ 1 := by have := hlo 0 (Nat.zero_le N); have := hhi 0 (Nat.zero_le N); linarith
  have hinv : 1 ≤ 1 / β := (le_div_iff₀ hβ).2 (by simpa using hβle)
  rw [htel]
  calc
    _ ≤ ‖phase (f N) * w N - phase (f 0) * w 0‖ +
        ‖∑ i ∈ Finset.range N, phase (f (i + 1)) * (w i - w (i + 1))‖ := norm_add_le _ _
    _ ≤ (‖phase (f N) * w N‖ + ‖phase (f 0) * w 0‖) +
        ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := add_le_add (norm_sub_le _ _) hsum
    _ = (‖w N‖ + ‖w 0‖) + ∑ i ∈ Finset.range N, ‖w i - w (i + 1)‖ := by
      simp only [norm_mul, phase_norm, one_mul]
    _ ≤ (1 / 2 + 1 / (4 * β)) + (1 / 2 + 1 / (4 * β)) + 1 / (2 * β) := by
      exact add_le_add (add_le_add hwN hw0) hvbound
    _ = 1 + 1 / β := by ring
    _ ≤ 1 / β + 1 / β := by simpa [add_comm] using add_le_add_right hinv (1 / β)
    _ = 2 / β := by ring

lemma phase_int (q : ℤ) : phase (q : ℝ) = 1 := by
  unfold phase
  convert Complex.exp_int_mul_two_pi_mul_I q using 2
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

lemma phase_neg (x : ℝ) : phase (-x) = (starRingEnd ℂ) (phase x) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma phase_sub_int_mul (x : ℝ) (q : ℤ) (n : ℕ) :
    phase (x - (q : ℝ) * n) = phase x := by
  have heq : x - (q : ℝ) * n = x + ((-(q * (n : ℤ)) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [heq, phase_add, phase_int, mul_one]

/-- Integer translations of the increment strip do not affect the estimate. -/
theorem first_derivative_sum_bound_strip (f : ℕ → ℝ) (N : ℕ) (β : ℝ) (q : ℤ)
    (hβ : 0 < β)
    (hlo : ∀ i ≤ N, (q : ℝ) + β ≤ f (i + 1) - f i)
    (hhi : ∀ i ≤ N, f (i + 1) - f i ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun i => f (i + 1) - f i) (Set.Iic N)) :
    ‖∑ i ∈ Finset.range N, phase (f i)‖ ≤ 2 / β := by
  let g : ℕ → ℝ := fun i => f i - (q : ℝ) * i
  have hg : ∀ i, g (i + 1) - g i = (f (i + 1) - f i) - q := by
    intro i
    dsimp [g]
    push_cast
    ring
  have H := first_derivative_sum_bound g N β hβ
    (by intro i hi; rw [hg]; have := hlo i hi; linarith)
    (by intro i hi; rw [hg]; have := hhi i hi; linarith)
    (by
      intro i hi j hj hij
      dsimp only
      rw [hg, hg]
      exact sub_le_sub_right (hmono hi hj hij) _)
  simpa only [g, phase_sub_int_mul] using H

end Problem337.ExponentialSum

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MonotoneBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- The indices of a monotone sequence lying in a closed interval form one
possibly empty interval of indices. -/
theorem monotone_filter_range_eq_Ico {α : Type*} [LinearOrder α]
    (d : ℕ → α) (hd : Monotone d) (N : ℕ) (L R : α) :
    ∃ a b : ℕ, a ≤ b ∧ b ≤ N ∧
      (Finset.range N).filter (fun j => L ≤ d j ∧ d j ≤ R) = Finset.Ico a b := by
  classical
  let s := (Finset.range N).filter (fun j => L ≤ d j ∧ d j ≤ R)
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := Finset.min'_mem _ hs
    have hb : b ∈ s := Finset.max'_mem _ hs
    have hab : a ≤ b := Finset.min'_le _ _ hb
    have hbN : b < N := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    refine ⟨a, b + 1, by omega, by omega, ?_⟩
    change s = Finset.Ico a (b + 1)
    ext j
    constructor
    · intro hj
      exact Finset.mem_Ico.mpr ⟨Finset.min'_le _ _ hj, Nat.lt_succ_iff.mpr (Finset.le_max' _ _ hj)⟩
    · intro hj
      rcases Finset.mem_Ico.mp hj with ⟨haj, hjb⟩
      have hjb' : j ≤ b := Nat.lt_succ_iff.mp hjb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hjb' hbN), ?_⟩
      exact ⟨(Finset.mem_filter.mp ha).2.1.trans (hd haj),
        (hd hjb').trans (Finset.mem_filter.mp hb).2.2⟩
  · refine ⟨0, 0, le_rfl, Nat.zero_le _, ?_⟩
    simpa only [Finset.Ico_self] using Finset.not_nonempty_iff_eq_empty.mp hs

/-- Cancellation on every interval transfers to one interval cut out by a
monotone increment sequence, without paying an extra term count. -/
theorem norm_sum_monotone_block_le {α : Type*} [LinearOrder α]
    (d : ℕ → α) (hd : Monotone d) (N : ℕ) (L R : α)
    (z : ℕ → ℂ) (C : ℝ)
    (hcancel : ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, L ≤ d j ∧ d j ≤ R) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ (Finset.range N).filter (fun j => L ≤ d j ∧ d j ≤ R), z j‖ ≤ C := by
  classical
  obtain ⟨a, b, hab, hbN, heq⟩ := monotone_filter_range_eq_Ico d hd N L R
  rw [heq]
  apply hcancel a b hab hbN
  intro j hj
  rw [← heq] at hj
  exact (Finset.mem_filter.mp hj).2

lemma phaseGoodBlock_pairwise_disjoint (d : ℕ → ℝ) (N : ℕ)
    (β : ℝ) (hβ : 0 < β) : Pairwise (fun k l : ℤ =>
      Disjoint (phaseGoodBlock d N β k) (phaseGoodBlock d N β l)) := by
  classical
  intro k l hkl
  apply Finset.disjoint_left.mpr
  intro j hjk hjl
  have hk := (Finset.mem_filter.mp hjk).2
  have hl := (Finset.mem_filter.mp hjl).2
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hgap : (k : ℝ) + 1 ≤ (l : ℝ) := by
      exact_mod_cast (show k + 1 ≤ l by omega)
    linarith
  · have hgap : (l : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (show l + 1 ≤ k by omega)
    linarith

/-- Partition a sum into good monotone derivative blocks and exceptional
indices. Each good integer cell pays just one cancellation bound. -/
theorem norm_sum_le_bad_card_add_good_blocks
    (d : ℕ → ℝ) (hd : Monotone d) (N : ℕ) (β : ℝ) (hβ : 0 < β)
    (K : Finset ℤ) (z : ℕ → ℂ) (C : ℝ)
    (hz : ∀ j < N, ‖z j‖ ≤ 1)
    (hcancel : ∀ k ∈ K, ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤
      ((Finset.range N \ K.biUnion (phaseGoodBlock d N β)).card : ℝ) +
        (K.card : ℝ) * C := by
  classical
  let G := K.biUnion (phaseGoodBlock d N β)
  have hsub : G ⊆ Finset.range N := by
    intro j hj
    obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hjk).1
  have hdisj : (K : Set ℤ).PairwiseDisjoint (phaseGoodBlock d N β) := by
    intro k hk l hl hkl
    exact phaseGoodBlock_pairwise_disjoint d N β hβ hkl
  have hgood : ‖∑ j ∈ G, z j‖ ≤ (K.card : ℝ) * C := by
    change ‖∑ j ∈ K.biUnion (phaseGoodBlock d N β), z j‖ ≤ _
    rw [Finset.sum_biUnion hdisj]
    calc
      _ ≤ ∑ k ∈ K, ‖∑ j ∈ phaseGoodBlock d N β k, z j‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ K, C := by
        apply Finset.sum_le_sum
        intro k hk
        exact norm_sum_monotone_block_le d hd N ((k : ℝ) + β) ((k : ℝ) + 1 - β)
          z C (hcancel k hk)
      _ = _ := by simp
  have hbad : ‖∑ j ∈ Finset.range N \ G, z j‖ ≤ ((Finset.range N \ G).card : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N \ G, ‖z j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range N \ G, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hz j (Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1)
      _ = _ := by simp
  rw [← Finset.sum_sdiff hsub]
  exact (norm_add_le _ _).trans (add_le_add hbad hgood)

/-- The number of integer cells intersecting a real interval has the usual
length-plus-two bound. -/
theorem floor_interval_card_le (L U : ℝ) (hLU : L ≤ U) :
    ((Finset.Icc ⌊L⌋ ⌊U⌋).card : ℝ) ≤ U - L + 2 := by
  have hfloor : ⌊L⌋ ≤ ⌊U⌋ := Int.floor_le_floor hLU
  have hcardZ := Int.card_Icc_of_le ⌊L⌋ ⌊U⌋ (show ⌊L⌋ ≤ ⌊U⌋ + 1 by omega)
  have hcard : ((Finset.Icc ⌊L⌋ ⌊U⌋).card : ℝ) = (⌊U⌋ : ℝ) + 1 - (⌊L⌋ : ℝ) := by
    exact_mod_cast hcardZ
  rw [hcard]
  have hU := Int.floor_le U
  have hL := Int.lt_floor_add_one L
  linarith

/-- Outside the good integer cells, an increment is close to an integer. -/
theorem phase_bad_near_integer (d : ℕ → ℝ) (N : ℕ) (β L U : ℝ)
    (hrange : ∀ j < N, L ≤ d j ∧ d j ≤ U) (j : ℕ)
    (hj : j ∈ Finset.range N \ (Finset.Icc ⌊L⌋ ⌊U⌋).biUnion (phaseGoodBlock d N β)) :
    ∃ k : ℤ, |d j - (k : ℝ)| < β := by
  classical
  have hjN : j < N := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
  have hnotmem := (Finset.mem_sdiff.mp hj).2
  let k : ℤ := ⌊d j⌋
  have hk : k ∈ Finset.Icc ⌊L⌋ ⌊U⌋ :=
    Finset.mem_Icc.mpr ⟨Int.floor_le_floor (hrange j hjN).1,
      Int.floor_le_floor (hrange j hjN).2⟩
  have hnot : ¬((k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) := by
    intro hgood
    apply hnotmem
    exact Finset.mem_biUnion.mpr ⟨k, hk,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjN, hgood⟩⟩
  have hklo : (k : ℝ) ≤ d j := Int.floor_le _
  have hkhi : d j < (k : ℝ) + 1 := Int.lt_floor_add_one _
  by_cases hleft : d j - (k : ℝ) < β
  · refine ⟨k, ?_⟩
    rwa [abs_of_nonneg (sub_nonneg.mpr hklo)]
  · have hleft' : β ≤ d j - (k : ℝ) := le_of_not_gt hleft
    have hright : (k : ℝ) + 1 - β < d j := by
      apply lt_of_not_ge
      intro hupper
      exact hnot ⟨by linarith, hupper⟩
    refine ⟨k + 1, ?_⟩
    simp only [Int.cast_add, Int.cast_one]
    rw [abs_of_nonpos (by linarith : d j - ((k : ℝ) + 1) ≤ 0)]
    linarith

/-- A second-derivative partition estimate, separating the packing estimate
for bad points from the cancellation estimate on good intervals. -/
theorem norm_sum_le_near_integer_bound
    (d : ℕ → ℝ) (hd : Monotone d) (N : ℕ) (β L U : ℝ) (hβ : 0 < β)
    (hLU : L ≤ U) (hrange : ∀ j < N, L ≤ d j ∧ d j ≤ U)
    (z : ℕ → ℂ) (B C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ j < N, ‖z j‖ ≤ 1)
    (hbad : ((nearIntegerIndices d N β).card : ℝ) ≤ B)
    (hcancel : ∀ k ∈ Finset.Icc ⌊L⌋ ⌊U⌋, ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤ B + (U - L + 2) * C := by
  classical
  have hsub : Finset.range N \ (Finset.Icc ⌊L⌋ ⌊U⌋).biUnion (phaseGoodBlock d N β) ⊆
      (Finset.range N).filter (fun j => ∃ k : ℤ, |d j - (k : ℝ)| < β) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1,
      phase_bad_near_integer d N β L U hrange j hj⟩
  have hcard : ((Finset.range N \ (Finset.Icc ⌊L⌋ ⌊U⌋).biUnion (phaseGoodBlock d N β)).card : ℝ) ≤
      ((nearIntegerIndices d N β).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbad' := hcard.trans hbad
  have hmain := norm_sum_le_bad_card_add_good_blocks d hd N β hβ
    (Finset.Icc ⌊L⌋ ⌊U⌋) z C hz hcancel
  exact hmain.trans (add_le_add hbad' (mul_le_mul_of_nonneg_right (floor_interval_card_le L U hLU) hC))

/-- Local monotonicity on the sampled range suffices for the partition bound;
extend by a constant after the last sampled increment. -/
theorem norm_sum_le_near_integer_bound_local
    (d : ℕ → ℝ) (N : ℕ) (hd : MonotoneOn d (Set.Iio N))
    (β L U : ℝ) (hβ : 0 < β) (hLU : L ≤ U)
    (hrange : ∀ j < N, L ≤ d j ∧ d j ≤ U)
    (z : ℕ → ℂ) (B C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ j < N, ‖z j‖ ≤ 1)
    (hbad : ((nearIntegerIndices d N β).card : ℝ) ≤ B)
    (hcancel : ∀ k ∈ Finset.Icc ⌊L⌋ ⌊U⌋, ∀ a b : ℕ, a ≤ b → b ≤ N →
      (∀ j ∈ Finset.Ico a b, (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β) →
      ‖∑ j ∈ Finset.Ico a b, z j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, z j‖ ≤ B + (U - L + 2) * C := by
  classical
  let e : ℕ → ℝ := fun j => d (min j (N - 1))
  have heq (j : ℕ) (hj : j < N) : e j = d j := by
    dsimp [e]
    rw [min_eq_left (by omega)]
  have hem : Monotone e := by
    intro i j hij
    by_cases hN : N = 0
    · simp [e, hN]
    · apply hd
      · change min i (N - 1) < N
        have := min_le_right i (N - 1)
        omega
      · change min j (N - 1) < N
        have := min_le_right j (N - 1)
        omega
      · exact min_le_min_right _ hij
  have hindices : nearIntegerIndices e N β = nearIntegerIndices d N β := by
    ext j
    by_cases hj : j < N
    · simp only [nearIntegerIndices, Finset.mem_filter, Finset.mem_range, hj, true_and, heq j hj]
    · simp only [nearIntegerIndices, Finset.mem_filter, Finset.mem_range, hj, false_and]
  apply norm_sum_le_near_integer_bound e hem N β L U hβ hLU
    (fun j hj => by simpa only [heq j hj] using hrange j hj) z B C hC hz
  · simpa only [hindices] using hbad
  · intro k hk a b hab hbN hstrip
    apply hcancel k hk a b hab hbN
    intro j hj
    have hjN : j < N := lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 hbN
    simpa only [heq j hjN] using hstrip j hj

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SecondDerivativeBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337

/-- The elementary square-root optimization of bad-point counting and
first-derivative cancellation, with explicit harmless constants. -/
theorem second_derivative_partition_sqrt_budget (A T lam : ℝ)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hlam : 0 < lam) (hlamone : lam ≤ 1) :
    (A * lam * T + 2 * Real.sqrt lam + 1) * (2 * Real.sqrt lam / lam + 1) +
      (A * lam * T + 2) * (2 / Real.sqrt lam + 1) ≤
        6 * A * T * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsq : (Real.sqrt lam)^2 = lam := Real.sq_sqrt hlam.le
  have hsone : Real.sqrt lam ≤ 1 := by
    nlinarith
  have hlams : lam ≤ Real.sqrt lam := by nlinarith
  have hat : 0 ≤ A * T := mul_nonneg hA hT
  have hprod : A * T * lam ≤ A * T * Real.sqrt lam := mul_le_mul_of_nonneg_left hlams hat
  have hratio : Real.sqrt lam / lam = 1 / Real.sqrt lam := by
    apply (div_eq_div_iff hlam.ne' hs.ne').mpr
    nlinarith
  rw [mul_div_assoc, hratio]
  have heq :
      (A * lam * T + 2 * Real.sqrt lam + 1) * (2 * (1 / Real.sqrt lam) + 1) +
        (A * lam * T + 2) * (2 / Real.sqrt lam + 1) =
      4 * A * T * Real.sqrt lam + 2 * A * T * lam +
        2 * Real.sqrt lam + 6 / Real.sqrt lam + 7 := by
    field_simp
    nlinarith [mul_nonneg hat (sq_nonneg (Real.sqrt lam))]
  convert heq.le.trans (show 4 * A * T * Real.sqrt lam + 2 * A * T * lam +
      2 * Real.sqrt lam + 6 / Real.sqrt lam + 7 ≤
      6 * A * T * Real.sqrt lam + 6 / Real.sqrt lam + 9 by nlinarith) using 1
  all_goals try with_reducible_and_instances rfl

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SeparatedIntervalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Classical
namespace Problem337

/-- Packing bound for integer-indexed values separated at a positive linear rate. -/
theorem separated_interval_card (s : Finset ℤ) (f : ℤ → ℝ)
    (lam u v : ℝ) (hlam : 0 < lam) (huv : u ≤ v)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → lam * ((j : ℝ) - i) ≤ f j - f i)
    (hrange : ∀ i ∈ s, u ≤ f i ∧ f i ≤ v) :
    (s.card : ℝ) ≤ (v - u) / lam + 1 := by
  classical
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have ha : a ∈ s := s.min'_mem hs
    have hb : b ∈ s := s.max'_mem hs
    have hab : a ≤ b := s.min'_le b hb
    have hsub : s ⊆ Finset.Icc a b := by
      intro i hi
      exact Finset.mem_Icc.mpr ⟨s.min'_le i hi, s.le_max' i hi⟩
    have hcard : (s.card : ℝ) ≤ (b : ℝ) - a + 1 := by
      calc
        (s.card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        _ = (b : ℝ) - a + 1 := by
          have h := Int.card_Icc_of_le a b (by omega)
          exact_mod_cast (show ((Finset.Icc a b).card : ℤ) = b - a + 1 by omega)
    have hg := hsep a ha b hb hab
    have ha' := (hrange a ha).1
    have hb' := (hrange b hb).2
    have hdiff : (b : ℝ) - a ≤ (v - u) / lam := by
      apply (le_div_iff₀ hlam).mpr
      nlinarith
    linarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The number of separated samples near integers is controlled by the number
of integer centers and the packing bound in each short interval. -/
theorem separated_near_integer_card (s : Finset ℤ) (f : ℤ → ℝ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hLU : L ≤ U)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → lam * ((j : ℝ) - i) ≤ f j - f i)
    (hrange : ∀ i ∈ s, L ≤ f i ∧ f i ≤ U) :
    ((s.filter fun i => ∃ q : ℤ, |f i - q| ≤ β).card : ℝ) ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) := by
  classical
  let centers : Finset ℤ := Finset.Icc ⌈L - β⌉ ⌊U + β⌋
  let fiber (q : ℤ) : Finset ℤ := s.filter fun i => |f i - q| ≤ β
  have hcover : (s.filter fun i => ∃ q : ℤ, |f i - q| ≤ β) ⊆ centers.biUnion fiber := by
    intro i hi
    obtain ⟨his, q, hq⟩ := Finset.mem_filter.mp hi
    have hq' := abs_le.mp hq
    have hi' := hrange i his
    apply Finset.mem_biUnion.mpr
    refine ⟨q, ?_, Finset.mem_filter.mpr ⟨his, hq⟩⟩
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      linarith
    · apply Int.le_floor.mpr
      linarith
  have hfiber (q : ℤ) : ((fiber q).card : ℝ) ≤ 2 * β / lam + 1 := by
    have h := separated_interval_card (fiber q) f lam ((q : ℝ) - β) ((q : ℝ) + β)
      hlam (by linarith)
      (fun i hi j hj hij => hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
      (fun i hi => by
        have h := abs_le.mp (Finset.mem_filter.mp hi).2
        constructor <;> linarith)
    convert h using 1 <;> first | rfl | ring
  have hcenters : (centers.card : ℝ) ≤ U - L + 2 * β + 1 := by
    have h := separated_interval_card centers (fun q => (q : ℝ)) 1 (L - β) (U + β)
      (by norm_num) (by linarith) (fun i _ j _ _ => by ring_nf; exact le_rfl)
      (fun q hq => by
        have hq' := Finset.mem_Icc.mp hq
        exact ⟨Int.ceil_le.mp hq'.1, Int.le_floor.mp hq'.2⟩)
    convert h using 1 <;> first | rfl | ring
  calc
    ((s.filter fun i => ∃ q : ℤ, |f i - q| ≤ β).card : ℝ) ≤
        ((centers.biUnion fiber).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ q ∈ centers, ((fiber q).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := centers) (t := fiber))
    _ ≤ ∑ _q ∈ centers, (2 * β / lam + 1) :=
      Finset.sum_le_sum (fun q _ => hfiber q)
    _ = (centers.card : ℝ) * (2 * β / lam + 1) := by
      simp
      ring
    _ ≤ (U - L + 2 * β + 1) * (2 * β / lam + 1) :=
      mul_le_mul_of_nonneg_right hcenters (by positivity)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DiscreteSecondDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Natural-indexed strict-neighborhood version of the separated sample bound. -/
theorem nat_separated_near_integer_card (d : ℕ → ℝ) (N : ℕ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β) (hLU : L ≤ U)
    (hsep : ∀ i < N, ∀ j < N, i ≤ j → lam * ((j : ℝ) - i) ≤ d j - d i)
    (hrange : ∀ i < N, L ≤ d i ∧ d i ≤ U) :
    ((nearIntegerIndices d N β).card : ℝ) ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) := by
  classical
  have h := separated_near_integer_card ((Finset.range N).image Int.ofNat)
    (fun i : ℤ => d i.toNat) lam β L U hlam hβ hLU
    (by
      intro i hi j hj hij
      rcases Finset.mem_image.mp hi with ⟨ii, hii, rfl⟩
      rcases Finset.mem_image.mp hj with ⟨jj, hjj, rfl⟩
      simpa only [Int.ofNat_eq_natCast, Int.toNat_natCast, Int.cast_natCast] using
        hsep ii (Finset.mem_range.mp hii) jj (Finset.mem_range.mp hjj)
          (Int.ofNat_le.mp (by simpa only [Int.ofNat_eq_natCast] using hij)))
    (by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨ii, hii, rfl⟩
      exact hrange ii (Finset.mem_range.mp hii))
  simp only [Finset.filter_image, Int.ofNat_eq_natCast, Int.toNat_natCast] at h
  rw [Finset.card_image_of_injective _ Int.ofNat_injective] at h
  have hsub : nearIntegerIndices d N β ⊆
      (Finset.range N).filter (fun i => ∃ q : ℤ, |d i - (q : ℝ)| ≤ β) := by
    intro i hi
    obtain ⟨hiN, q, hq⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiN, q, hq.le⟩
  exact (show ((nearIntegerIndices d N β).card : ℝ) ≤
      (((Finset.range N).filter (fun i => ∃ q : ℤ, |d i - (q : ℝ)| ≤ β)).card : ℝ) by
    exact_mod_cast Finset.card_le_card hsub).trans h

namespace ExponentialSum

/-- A strip cancellation bound needing increment information only for the
indices being summed; the final endpoint costs at most one. -/
theorem first_derivative_Ico_bound (f : ℕ → ℝ) (a b : ℕ) (β : ℝ) (q : ℤ)
    (hab : a ≤ b) (hβ : 0 < β)
    (hlo : ∀ j ∈ Finset.Ico a b, (q : ℝ) + β ≤ f (j + 1) - f j)
    (hhi : ∀ j ∈ Finset.Ico a b, f (j + 1) - f j ≤ (q : ℝ) + 1 - β)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio b)) :
    ‖∑ j ∈ Finset.Ico a b, phase (f j)‖ ≤ 2 / β + 1 := by
  by_cases heq : a = b
  · subst b
    simp only [Finset.Ico_self, Finset.sum_empty, norm_zero]
    positivity
  have hab' : a < b := lt_of_le_of_ne hab heq
  let n := b - a - 1
  have hn : n + 1 = b - a := by dsimp [n]; omega
  let g : ℕ → ℝ := fun i => f (a + i)
  have hinc (i : ℕ) : g (i + 1) - g i = f (a + i + 1) - f (a + i) := by
    simp only [g, Nat.add_assoc]
  have hbound := first_derivative_sum_bound_strip g n β q hβ
    (by
      intro i hi
      rw [hinc]
      apply hlo
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    (by
      intro i hi
      rw [hinc]
      apply hhi
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    (by
      intro i hi j hj hij
      change g (i + 1) - g i ≤ g (j + 1) - g j
      rw [hinc, hinc]
      have hi' : i ≤ n := hi
      have hj' : j ≤ n := hj
      exact hmono (by change a + i < b; omega) (by change a + j < b; omega) (Nat.add_le_add_left hij a))
  rw [Finset.sum_Ico_eq_sum_range, ← hn, Finset.sum_range_succ]
  exact (norm_add_le _ _).trans (add_le_add hbound (le_of_eq (phase_norm _)))

/-- A fully discrete second-derivative estimate from monotone separated phase
increments. The only analytic input is the proved first-derivative test. -/
theorem discrete_second_derivative_partition_bound (f : ℕ → ℝ) (N : ℕ)
    (lam β L U : ℝ) (hlam : 0 < lam) (hβ : 0 < β) (hLU : L ≤ U)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i))
    (hrange : ∀ j < N, L ≤ f (j + 1) - f j ∧ f (j + 1) - f j ≤ U) :
    ‖∑ j ∈ Finset.range N, phase (f j)‖ ≤
      (U - L + 2 * β + 1) * (2 * β / lam + 1) + (U - L + 2) * (2 / β + 1) := by
  apply norm_sum_le_near_integer_bound_local (fun j => f (j + 1) - f j) N hmono β L U hβ hLU hrange
    (fun j => phase (f j)) _ (2 / β + 1) (by positivity)
  · intro j hj
    exact le_of_eq (phase_norm _)
  · exact nat_separated_near_integer_card _ N lam β L U hlam hβ.le hLU hsep hrange
  · intro q hq a b hab hbN hstrip
    exact first_derivative_Ico_bound f a b β q hab hβ
      (fun j hj => (hstrip j hj).1) (fun j hj => (hstrip j hj).2)
      (by
        intro i hi j hj hij
        exact hmono (lt_of_lt_of_le hi hbN) (lt_of_lt_of_le hj hbN) hij)

/-- The square-root form used in the reciprocal-phase differencing argument. -/
theorem discrete_second_derivative_sqrt_bound (f : ℕ → ℝ) (N : ℕ)
    (lam A L : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i))
    (hrange : ∀ j < N, L ≤ f (j + 1) - f j ∧ f (j + 1) - f j ≤ L + A * lam * N) :
    ‖∑ j ∈ Finset.range N, phase (f j)‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  have h := discrete_second_derivative_partition_bound f N lam (Real.sqrt lam) L (L + A * lam * N)
    hlam (Real.sqrt_pos.mpr hlam) (le_add_of_nonneg_right (by positivity)) hmono hsep hrange
  have hb := second_derivative_partition_sqrt_budget A (N : ℝ) lam hA (Nat.cast_nonneg _) hlam hlam1
  exact h.trans (by simpa only [add_sub_cancel_left] using hb)

end ExponentialSum
end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PhaseExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

theorem affineTailPhase_increment (f : ℕ → ℝ) (N n : ℕ) :
    affineTailPhase f N (n + 1) - affineTailPhase f N n =
      f (min n (N - 1) + 1) - f (min n (N - 1)) := by
  simp only [affineTailPhase, Finset.sum_range_succ]
  ring

theorem affineTailPhase_eq (f : ℕ → ℝ) (N : ℕ) :
    ∀ n : ℕ, n ≤ N → affineTailPhase f N n = f n := by
  intro n
  induction n with
  | zero => simp [affineTailPhase]
  | succ n ih =>
    intro hn
    have hprev := ih (by omega)
    have hmin : min n (N - 1) = n := Nat.min_eq_left (by omega)
    have hinc := affineTailPhase_increment f N n
    rw [hmin] at hinc
    linarith

theorem affineTailPhase_increment_monotone (f : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N)) :
    Monotone (fun j => affineTailPhase f N (j + 1) - affineTailPhase f N j) := by
  intro i j hij
  dsimp only
  rw [affineTailPhase_increment, affineTailPhase_increment]
  apply hmono
  · change min i (N - 1) < N
    omega
  · change min j (N - 1) < N
    omega
  · omega

theorem affineTailPhase_increment_eq (f : ℕ → ℝ) (N j : ℕ) (hj : j < N) :
    affineTailPhase f N (j + 1) - affineTailPhase f N j = f (j + 1) - f j := by
  rw [affineTailPhase_increment, Nat.min_eq_left (by omega : j ≤ N - 1)]

/-- Local interval monotonicity is enough whenever a phase-sum theorem assumes
globally monotone increments: this extension preserves every sample used. -/
theorem exists_monotone_increment_extension (f : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N)) :
    ∃ g : ℕ → ℝ, (∀ j, j ≤ N → g j = f j) ∧
      Monotone (fun j => g (j + 1) - g j) ∧
      (∀ j, j < N → g (j + 1) - g j = f (j + 1) - f j) := by
  exact ⟨affineTailPhase f N, affineTailPhase_eq f N,
    affineTailPhase_increment_monotone f N hN hmono,
    affineTailPhase_increment_eq f N⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SecondDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Set

namespace Problem337

/-- A second finite difference is a second derivative value times the squared
step. Only pointwise derivative data on the relevant closed interval is used. -/
theorem second_difference_eq_deriv (f f' f'' : ℝ → ℝ) (x h : ℝ) (hh : 0 < h)
    (hf : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f' (f'' y) y) :
    ∃ c ∈ Ioo x (x + 2 * h),
      f (x + 2 * h) - 2 * f (x + h) + f x = h ^ 2 * f'' c := by
  let g : ℝ → ℝ := fun y => f (y + h) - f y
  let g' : ℝ → ℝ := fun y => f' (y + h) - f' y
  have hg : ∀ y ∈ Icc x (x + h), HasDerivAt g (g' y) y := by
    intro y hy
    have hy1 : y ∈ Icc x (x + 2 * h) := ⟨hy.1, by linarith [hy.2]⟩
    have hy2 : y + h ∈ Icc x (x + 2 * h) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have htrans := (hf (y + h) hy2).comp_add_const y h
    exact htrans.fun_sub (hf y hy1)
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : x < x + h)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt)
    (fun y hy => hg y ⟨hy.1.le, hy.2.le⟩)
  have hinterval : Icc c (c + h) ⊆ Icc x (x + 2 * h) := by
    intro y hy
    constructor <;> linarith [hc.1, hc.2, hy.1, hy.2]
  obtain ⟨d, hd, hdeq⟩ := exists_hasDerivAt_eq_slope f' f'' (by linarith : c < c + h)
    (fun y hy => (hf' y (hinterval hy)).continuousAt.continuousWithinAt)
    (fun y hy => hf' y (hinterval ⟨hy.1.le, hy.2.le⟩))
  refine ⟨d, ⟨by linarith [hc.1, hd.1], by linarith [hc.2, hd.2]⟩, ?_⟩
  have heq' : g (x + h) - g x = h * g' c := by
    have : x + h - x = h := by ring
    rw [this] at heq
    exact (eq_div_iff (ne_of_gt hh)).mp heq |> (fun H => by nlinarith [H])
  have hdeq' : f' (c + h) - f' c = h * f'' d := by
    have : c + h - c = h := by ring
    rw [this] at hdeq
    have := (eq_div_iff (ne_of_gt hh)).mp hdeq
    nlinarith
  dsimp [g, g'] at heq'
  have hx : x + h + h = x + 2 * h := by ring
  rw [hx, hdeq'] at heq'
  nlinarith

/-- Bounds for the second derivative give bounds for each second difference. -/
theorem second_difference_bounds (f f' f'' : ℝ → ℝ) (x h L U : ℝ) (hh : 0 < h)
    (hf : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc x (x + 2 * h), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Icc x (x + 2 * h), L ≤ f'' y ∧ f'' y ≤ U) :
    h ^ 2 * L ≤ f (x + 2 * h) - 2 * f (x + h) + f x ∧
      f (x + 2 * h) - 2 * f (x + h) + f x ≤ h ^ 2 * U := by
  obtain ⟨c, hc, heq⟩ := second_difference_eq_deriv f f' f'' x h hh hf hf'
  rw [heq]
  have hb := hbound c ⟨hc.1.le, hc.2.le⟩
  exact ⟨mul_le_mul_of_nonneg_left hb.1 (sq_nonneg h),
    mul_le_mul_of_nonneg_left hb.2 (sq_nonneg h)⟩

/-- Telescoping a two-sided bound for adjacent increments. -/
theorem discrete_increment_bounds (d : ℕ → ℝ) (a b : ℕ) (L U : ℝ)
    (hab : a ≤ b)
    (hstep : ∀ j ∈ Finset.Ico a b, L ≤ d (j + 1) - d j ∧ d (j + 1) - d j ≤ U) :
    L * ((b : ℝ) - a) ≤ d b - d a ∧ d b - d a ≤ U * ((b : ℝ) - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hprev : ∀ j ∈ Finset.Ico a b, L ≤ d (j + 1) - d j ∧ d (j + 1) - d j ≤ U := by
      intro j hj
      exact hstep j (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
        (Finset.mem_Ico.mp hj).2.trans (Nat.lt_succ_self b)⟩)
    have hlast := hstep b (Finset.mem_Ico.mpr ⟨hab, by omega⟩)
    have hprior := ih hprev
    push_cast
    constructor <;> nlinarith [hprior.1, hprior.2, hlast.1, hlast.2]

/-- Continuous second-derivative bounds imply the separation hypotheses for
sampled first differences used by the discrete second-derivative test. -/
theorem sampled_increment_bounds (f f' f'' : ℝ → ℝ) (a b : ℕ) (L U : ℝ)
    (hab : a ≤ b)
    (hf : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Icc (a : ℝ) ((b : ℝ) + 1), L ≤ f'' y ∧ f'' y ≤ U) :
    L * ((b : ℝ) - a) ≤
        (f ((b : ℝ) + 1) - f b) - (f ((a : ℝ) + 1) - f a) ∧
      (f ((b : ℝ) + 1) - f b) - (f ((a : ℝ) + 1) - f a) ≤ U * ((b : ℝ) - a) := by
  apply discrete_increment_bounds (fun n => f ((n : ℝ) + 1) - f n) a b L U hab
  intro n hn
  have hna : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
  have hnb : (n : ℝ) + 1 ≤ b := by exact_mod_cast (Finset.mem_Ico.mp hn).2
  have hsub : Icc (n : ℝ) ((n : ℝ) + 2 * 1) ⊆ Icc (a : ℝ) ((b : ℝ) + 1) := by
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hh := second_difference_bounds f f' f'' (n : ℝ) 1 L U (by norm_num)
    (fun y hy => hf y (hsub hy)) (fun y hy => hf' y (hsub hy))
    (fun y hy => hbound y (hsub hy))
  norm_num only [one_pow, one_mul, mul_one] at hh
  push_cast
  have heq : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
  rw [heq]
  constructor <;> linarith [hh.1, hh.2]

/-- Darboux's theorem makes the sign of a nonvanishing second derivative
constant. Absolute derivative bounds therefore give one uniform signed strip. -/
theorem second_derivative_signed_bounds (f' f'' : ℝ → ℝ) (s : Set ℝ)
    (hs : Convex ℝ s) (L U : ℝ) (hL : 0 < L)
    (hf' : ∀ x ∈ s, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ s, L ≤ |f'' x| ∧ |f'' x| ≤ U) :
    (∀ x ∈ s, L ≤ f'' x ∧ f'' x ≤ U) ∨
      (∀ x ∈ s, -U ≤ f'' x ∧ f'' x ≤ -L) := by
  have hn : ∀ x ∈ s, f'' x ≠ 0 := by
    intro x hx heq
    have := (hbound x hx).1
    rw [heq, abs_zero] at this
    linarith
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hs
      (fun x hx => (hf' x hx).hasDerivWithinAt) hn with hneg | hpos
  · right
    intro x hx
    have hb := hbound x hx
    rw [abs_of_neg (hneg x hx)] at hb
    constructor <;> linarith [hb.1, hb.2]
  · left
    intro x hx
    simpa only [abs_of_pos (hpos x hx)] using hbound x hx

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SecondDerivativeTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.ExponentialSum

/-- The discrete test needs monotonicity only at the sampled increments. -/
theorem discrete_second_derivative_sqrt_bound_local (f : ℕ → ℝ) (N : ℕ)
    (lam A L : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hmono : MonotoneOn (fun j => f (j + 1) - f j) (Set.Iio N))
    (hsep : ∀ i < N, ∀ j < N, i ≤ j →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i))
    (hrange : ∀ j < N, L ≤ f (j + 1) - f j ∧
      f (j + 1) - f j ≤ L + A * lam * N) :
    ‖∑ j ∈ Finset.range N, phase (f j)‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero, mul_zero,
      zero_mul, zero_add]
    positivity
  obtain ⟨g, hgf, hgm, hgd⟩ := exists_monotone_increment_extension f N
    (Nat.pos_of_ne_zero hN) hmono
  have h := discrete_second_derivative_sqrt_bound g N lam A L hlam hlam1 hA (hgm.monotoneOn _)
    (by
      intro i hi j hj hij
      rw [hgd i hi, hgd j hj]
      exact hsep i hi j hj hij)
    (by
      intro j hj
      rw [hgd j hj]
      exact hrange j hj)
  have heq : (∑ j ∈ Finset.range N, phase (g j)) =
      ∑ j ∈ Finset.range N, phase (f j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hgf j (Finset.mem_range.mp hj).le]
  rwa [heq] at h

/-- Sampled differences on a translated real interval. The closed support ends
at the last needed phase value, not one integer beyond it. -/
theorem translated_sampled_increment_bounds (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N i j : ℕ) (L U : ℝ) (_hi : i < N) (hj : j < N) (hij : i ≤ j)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), L ≤ f'' y ∧ f'' y ≤ U) :
    L * ((j : ℝ) - i) ≤
        (f (((j + 1 : ℕ) : ℝ) + x) - f ((j : ℝ) + x)) -
        (f (((i + 1 : ℕ) : ℝ) + x) - f ((i : ℝ) + x)) ∧
      (f (((j + 1 : ℕ) : ℝ) + x) - f ((j : ℝ) + x)) -
        (f (((i + 1 : ℕ) : ℝ) + x) - f ((i : ℝ) + x)) ≤ U * ((j : ℝ) - i) := by
  have hsupport (y : ℝ) (hy : y ∈ Set.Icc (i : ℝ) ((j : ℝ) + 1)) :
      y + x ∈ Set.Icc x (x + N) := by
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    constructor <;> linarith [hy.1, hy.2]
  have h := sampled_increment_bounds
    (fun y => f (y + x)) (fun y => f' (y + x)) (fun y => f'' (y + x))
    i j L U hij
    (fun y hy => (hf (y + x) (hsupport y hy)).comp_add_const y x)
    (fun y hy => (hf' (y + x) (hsupport y hy)).comp_add_const y x)
    (fun y hy => hbound (y + x) (hsupport y hy))
  simpa only [Nat.cast_add, Nat.cast_one] using h

/-- The second-derivative test for a positive second derivative on precisely
the closed interval supporting the finite sum. -/
theorem second_derivative_sqrt_bound_positive (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N : ℕ) (lam A : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), lam ≤ f'' y ∧ f'' y ≤ A * lam) :
    ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero, mul_zero,
      zero_mul, zero_add]
    positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let g : ℕ → ℝ := fun j => f ((j : ℝ) + x)
  have hb (i : ℕ) (hi : i < N) (j : ℕ) (hj : j < N) (hij : i ≤ j) :=
    translated_sampled_increment_bounds f f' f'' x N i j lam (A * lam)
      hi hj hij hf hf' hbound
  apply discrete_second_derivative_sqrt_bound_local g N lam A (g 1 - g 0)
    hlam hlam1 hA
  · intro i hi j hj hij
    have hh := (hb i hi j hj hij).1
    have hd : (0 : ℝ) ≤ (j : ℝ) - i := sub_nonneg.mpr (by exact_mod_cast hij)
    have hp : 0 ≤ lam * ((j : ℝ) - i) := mul_nonneg hlam.le hd
    dsimp [g]
    linarith
  · intro i hi j hj hij
    exact (hb i hi j hj hij).1
  · intro j hj
    have hh := hb 0 hNpos j hj (Nat.zero_le j)
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj.le
    have hp : 0 ≤ A * lam := mul_nonneg hA hlam.le
    have ht := mul_le_mul_of_nonneg_left hjN hp
    have hj0 := Nat.cast_nonneg (α := ℝ) j
    have hl := mul_nonneg hlam.le hj0
    dsimp [g]
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_add] at hh ⊢
    constructor <;> linarith [hh.1, hh.2]

/-- The usual absolute second-derivative test. Darboux gives a uniform sign;
negative phases are handled by complex conjugation. -/
theorem second_derivative_sqrt_bound (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N : ℕ) (lam A : ℝ)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), lam ≤ |f'' y| ∧ |f'' y| ≤ A * lam) :
    ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤
      6 * A * N * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  rcases second_derivative_signed_bounds f' f'' _ (convex_Icc _ _) lam (A * lam)
      hlam hf' hbound with hpos | hneg
  · exact second_derivative_sqrt_bound_positive f f' f'' x N lam A
      hlam hlam1 hA hf hf' hpos
  · have h := second_derivative_sqrt_bound_positive
      (fun y => -f y) (fun y => -f' y) (fun y => -f'' y) x N lam A
      hlam hlam1 hA
      (fun y hy => (hf y hy).neg) (fun y hy => (hf' y hy).neg)
      (by
        intro y hy
        have hh := hneg y hy
        constructor <;> linarith [hh.1, hh.2])
    simpa only [phase_neg, ← map_sum, Complex.norm_conj] using h

/-- A uniform second-derivative estimate for every positive scale, without a
smallness hypothesis on that scale or an additive endpoint error. -/
theorem second_derivative_test (f f' f'' : ℝ → ℝ)
    (x : ℝ) (N : ℕ) (lam A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A)
    (hf : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Set.Icc x (x + N), HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Icc x (x + N), lam ≤ |f'' y| ∧ |f'' y| ≤ A * lam) :
    ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤
      (6 * A + 15) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hNs : 0 ≤ (N : ℝ) * Real.sqrt lam := mul_nonneg (Nat.cast_nonneg _) hs.le
  have hinv : 0 ≤ 1 / Real.sqrt lam := by positivity
  by_cases hl1 : lam ≤ 1
  · have h := second_derivative_sqrt_bound f f' f'' x N lam A hlam hl1 hA hf hf' hbound
    have hs1 : Real.sqrt lam ≤ 1 := by nlinarith [Real.sq_sqrt hlam.le]
    have hi1 : 1 ≤ 1 / Real.sqrt lam := (le_div_iff₀ hs).2 (by simpa using hs1)
    have ha := mul_nonneg hA hinv
    apply h.trans
    have heq : 6 * A * N * Real.sqrt lam = 6 * A * ((N : ℝ) * Real.sqrt lam) := by ring
    rw [heq]
    simp only [div_eq_mul_inv, one_mul] at hi1 ha ⊢
    nlinarith
  · have hs1 : 1 ≤ Real.sqrt lam := by nlinarith [Real.sq_sqrt hlam.le]
    have hnorm : ‖∑ j ∈ Finset.range N, phase (f ((j : ℝ) + x))‖ ≤ (N : ℝ) := by
      calc
        _ ≤ ∑ j ∈ Finset.range N, ‖phase (f ((j : ℝ) + x))‖ := norm_sum_le _ _
        _ = (N : ℝ) := by simp only [phase_norm, Finset.sum_const, Finset.card_range,
                            nsmul_eq_mul, mul_one]
    apply hnorm.trans
    have hN := mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have ha := mul_nonneg hA (add_nonneg hNs hinv)
    nlinarith

end Problem337.ExponentialSum

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalTerminalSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Absorb the square-root expression in the second derivative test. -/
theorem reciprocal_terminal_sqrt_budget {U a lam T : ℝ} (hU : 1 ≤ U)
    (ha : 0 < a) (hT : T ≤ 3 * U)
    (hlower : a * U ^ (-(3 : ℝ) / 2) ≤ lam)
    (hupper : lam ≤ a * U ^ (-(2 : ℝ) / 5)) :
    T * Real.sqrt lam + 1 / Real.sqrt lam ≤
      3 * (a ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1) * U ^ ((4 : ℝ) / 5) := by
  have hlam : 0 < lam := (mul_pos ha (Real.rpow_pos_of_pos (by linarith) _)).trans_le hlower
  have h := reciprocal_terminal_error_bound hU ha ha.le hlower hupper
  have hinv : lam ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt lam := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hlam.le, ← Real.sqrt_eq_rpow, one_div]
  rw [← Real.sqrt_eq_rpow, hinv] at h
  have hs := mul_le_mul_of_nonneg_right hT (Real.sqrt_nonneg lam)
  have hi : 0 ≤ 1 / Real.sqrt lam := by positivity
  nlinarith

/-- Once a fixed reciprocal derivative order has been chosen, every short
forward difference satisfies a uniform terminal cancellation estimate. -/
theorem reciprocal_terminal_range_bound (k : ℕ) (hk : 4 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U Z x : ℝ) (N : ℕ) (hs : List ℝ),
      2 ≤ U → hs.length + 2 = k →
      (∀ h ∈ hs, 1 ≤ h ∧ h ≤ U ^ (1 / (10 * (k : ℝ)))) →
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
      U ≤ x → x + N + hs.sum ≤ 3 * U → (N : ℝ) ≤ 3 * U →
      ‖∑ j ∈ Finset.range N,
        ExponentialSum.phase (forwardDifference hs (fun y => Z / y) ((j : ℝ) + x))‖ ≤
        C * U ^ ((4 : ℝ) / 5) := by
  let a : ℝ := (k.factorial : ℝ) / (3 : ℝ) ^ (k + 1)
  let A : ℝ := (3 : ℝ) ^ (k + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(6 * A + 15) * (3 * (a ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1)),
    by positivity, ?_⟩
  intro U Z x N hs hU hlen hhs hlo hhi hx hend hN
  have hU0 : 0 < U := by linarith
  have hhs0 : ∀ h ∈ hs, 0 ≤ h := fun h hh => by linarith [(hhs h hh).1]
  have hhspos : ∀ h ∈ hs, 0 < h := fun h hh => by linarith [(hhs h hh).1]
  let Λ := |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod
  obtain ⟨hΛlo, hΛhi⟩ := reciprocal_phase_shift_scale (by linarith : 1 < U)
    (show 1 ≤ k by omega) hlo hhi hs (by omega) hhs
  have hΛpos : 0 < Λ := (Real.rpow_pos_of_pos hU0 _).trans_le hΛlo
  let lam := a * Λ
  have hlam : 0 < lam := mul_pos ha hΛpos
  have hbounds (y : ℝ) (hy : y ∈ Set.Icc x (x + N)) :
      lam ≤ |iteratedDeriv 2 (forwardDifference hs (fun z => Z / z)) y| ∧
      |iteratedDeriv 2 (forwardDifference hs (fun z => Z / z)) y| ≤ A * lam := by
    have hb := reciprocal_second_derivative_comparison_general hs hhspos Z 3 hU0
      (hx.trans hy.1) (show y + hs.sum ≤ 3 * U by linarith [hy.2])
    dsimp only at hb
    rw [hlen] at hb
    change a * Λ ≤ _ ∧ _ ≤ (k.factorial : ℝ) * Λ at hb
    have heq : A * lam = (k.factorial : ℝ) * Λ := by
      dsimp [A, lam, a]
      field_simp
    rwa [heq]
  have hh := ExponentialSum.second_derivative_test
    (forwardDifference hs (fun y => Z / y))
    (iteratedDeriv 1 (forwardDifference hs (fun y => Z / y)))
    (iteratedDeriv 2 (forwardDifference hs (fun y => Z / y)))
    x N lam A hlam hA.le
    (fun y hy => (reciprocal_forwardDifference_second_derivative_data hs hhs0 Z
      (hU0.trans_le (hx.trans hy.1))).1)
    (fun y hy => (reciprocal_forwardDifference_second_derivative_data hs hhs0 Z
      (hU0.trans_le (hx.trans hy.1))).2)
    hbounds
  have hb := reciprocal_terminal_sqrt_budget (by linarith : 1 ≤ U) ha hN
    (mul_le_mul_of_nonneg_left hΛlo ha.le)
    (mul_le_mul_of_nonneg_left hΛhi ha.le)
  exact hh.trans (by
    calc
      (6 * A + 15) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) ≤
          (6 * A + 15) * (3 * (a ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1) * U ^ ((4 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring)

/-- Integer interval terminal estimate, in the exact form used by iterated
correlations. The endpoint extension is absorbed by the enlarged interval. -/
theorem reciprocal_terminal_interval_bound (k : ℕ) (hk : 4 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U Z : ℝ) (L R : ℤ) (hs : List ℤ),
      2 ≤ U → hs.length = k - 2 →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℤ)) →
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
      U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ‖∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => Z / y) n)‖ ≤ C * U ^ ((4 : ℝ) / 5) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_terminal_range_bound k hk
  refine ⟨C, hC, ?_⟩
  intro U Z L R hs hU hlen hhs hlo hhi hL hR
  have hU0 : 0 < U := by linarith
  have hsum : 0 ≤ hs.sum := List.sum_nonneg (fun h hh => (hhs h hh).1.le)
  by_cases hempty : R - hs.sum < L
  · rw [Finset.Icc_eq_empty (not_le_of_gt hempty), Finset.sum_empty, norm_zero]
    positivity
  have hne : L ≤ R - hs.sum := by omega
  let N := (R - hs.sum + 1 - L).toNat
  have hNi : (N : ℤ) = R - hs.sum + 1 - L := Int.toNat_of_nonneg (by omega)
  have hNr := congrArg (fun n : ℤ => (n : ℝ)) hNi
  push_cast at hNr
  have hsumR : ((hs.map (fun h : ℤ => (h : ℝ))).sum) = (hs.sum : ℝ) := by
    simp
  have hspos : (0 : ℝ) ≤ (hs.sum : ℝ) := by exact_mod_cast hsum
  have hh := hbound U Z L N (hs.map (fun h : ℤ => (h : ℝ))) hU
    (by simp only [List.length_map, hlen]; omega)
    (by
      intro h hh
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hh
      constructor
      · exact_mod_cast (show (1 : ℤ) ≤ j by have := (hhs j hj).1; omega)
      · have hh : (j : ℝ) < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℝ) := by
          exact_mod_cast (hhs j hj).2
        exact hh.le.trans (Nat.floor_le (Real.rpow_nonneg hU0.le _)))
    hlo hhi hL
    (by rw [hsumR]; linarith)
    (by linarith)
  have heq : (∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => Z / y) n)) =
      ∑ j ∈ Finset.range N,
        ExponentialSum.phase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => Z / y) ((j : ℝ) + L)) := by
    rw [Int.Icc_eq_finset_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast]
    rw [add_comm]
    rfl
  rwa [heq]

/-- Eventual interface for finite-order uniformization of reciprocal phases. -/
theorem reciprocal_terminal_bound_eventually (k : ℕ) (hk : 4 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ U : ℝ in Filter.atTop, ∀ Z : ℝ,
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
      ∀ L R : ℤ, U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ∀ hs : List ℤ, hs.length = k - 2 →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℤ)) →
      ‖∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => Z / y) n)‖ ≤ C * U ^ ((4 : ℝ) / 5) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_terminal_interval_bound k hk
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with U hU
  intro Z hlo hhi L R hL hR hs hlen hhs
  exact hbound U Z L R hs hU hlen hhs hlo hhi hL hR

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Problem337

/-- Uniform local power cancellation for reciprocal phases, with no analytic
hypotheses beyond the indicated numerator range. -/
theorem reciprocal_phase_local_power_saving (B : ℝ) (hB : 4 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (Z : ℝ) (L R : ℤ),
        U ^ (4 : ℕ) ≤ |Z| → |Z| ≤ U ^ B →
        U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
        ‖∑ n ∈ Finset.Icc L R, differencingPhase (Z / (n : ℝ))‖ ≤
          A * U ^ (1 - δ) := by
  exact reciprocal_phase_uniform_of_terminal reciprocal_terminal_bound_eventually B hB

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DeterministicReciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter
namespace Problem337

/-- The natural and integer closed interval sums agree under the canonical cast. -/
lemma sum_nat_interval_eq_int (f : ℤ → ℂ) (L R : ℕ) :
    (∑ n ∈ Finset.Icc L R, f n) = ∑ n ∈ Finset.Icc (L : ℤ) (R : ℤ), f n := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    obtain ⟨hL, hR⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hL, by exact_mod_cast hR⟩
  · intro n hn m hm h
    exact_mod_cast h
  · intro n hn
    obtain ⟨hL, hR⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := (Int.natCast_nonneg L).trans hL
    refine ⟨n.toNat, ?_, Int.toNat_of_nonneg hn0⟩
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro n hn
    rfl

/-- Integer-interval reciprocal cancellation in a natural dyadic piece. -/
lemma reciprocal_sum_dyadic_piece (A δ U Z : ℝ) (u L R : ℕ)
    (hu : 0 < u) (hU : U = (u : ℝ))
    (hlocal : ∀ L R : ℤ, U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ‖∑ n ∈ Finset.Icc L R, differencingPhase (Z / (n : ℝ))‖ ≤ A * U ^ (1 - δ)) :
    ‖∑ n ∈ (Finset.Ico u (2 * u) ∩ Finset.Icc L R),
      differencingPhase (Z / (n : ℝ))‖ ≤ A * U ^ (1 - δ) := by
  have heq : Finset.Ico u (2 * u) ∩ Finset.Icc L R =
      Finset.Icc (max u L) (min (2 * u - 1) R) := by
    ext n
    simp only [Finset.mem_inter, Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [heq]
  have hs := sum_nat_interval_eq_int
    (fun n => differencingPhase (Z / (n : ℝ))) (max u L) (min (2 * u - 1) R)
  simp only [Int.cast_natCast] at hs
  rw [hs]
  apply hlocal
  · subst U
    exact_mod_cast (le_max_left u L)
  · subst U
    have hh : min (2 * u - 1) R ≤ 2 * u := (min_le_left _ _).trans (Nat.sub_le _ _)
    exact_mod_cast hh

/-- The local reciprocal-phase theorem gives a uniform exponential saving over
an entire high residue level. The denominator range and local frequency range
are explicit, and no cancellation hypothesis remains. -/
theorem deterministic_reciprocal_sum_bound (D : ℝ) (hD : 255 ≤ D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ᶠ S : ℝ in atTop, ∀ (m X Z : ℝ) (L R : ℕ),
        m ≤ S → Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
        Real.exp (-m / 10000) * X ≤ (L : ℝ) → (R : ℝ) ≤ X →
        Real.exp (D * S) ≤ |Z| → |Z| ≤ Real.exp ((2 * D + 102) * S) →
        ‖∑ n ∈ Finset.Icc L R, differencingPhase (Z / (n : ℝ))‖ ≤
          A * X * Real.exp (-c * S) := by
  obtain ⟨A, δ, hA, hδ, hlocal⟩ := reciprocal_phase_local_power_saving (3 * D) (by linarith)
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hlocal
  refine ⟨2 * A, 4 * δ / 5, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    eventually_ge_atTop (10 * Real.log 2), eventually_ge_atTop (5 * U₀ / 4)] with S hS hSlarge hSU
  intro m X Z L R hm hXlo hXhi hL hR hZlo hZhi
  have hX : 0 < X := (Real.exp_pos S).trans_le hXlo
  have hUlarge : U₀ ≤ Real.exp (4 * S / 5) := by
    have he := Real.add_one_le_exp (4 * S / 5)
    linarith
  by_cases hempty : R < L
  · rw [Finset.Icc_eq_empty_of_lt hempty, Finset.sum_empty, norm_zero]
    positivity
  have hLR : L ≤ R := by omega
  have hLpos : 1 ≤ L := by
    have hh : (0 : ℝ) < L := (mul_pos (Real.exp_pos _) hX).trans_le hL
    exact_mod_cast (show 0 < L by exact_mod_cast hh)
  have hLupper : (L : ℝ) ≤ X := (Nat.cast_le.mpr hLR).trans hR
  have hhalf : Real.exp (4 * S / 5) ≤ (L : ℝ) / 2 :=
    (deterministic_phase_window S m D X ((L : ℝ) / 2) Z hS hSlarge hm hD
      hXlo hXhi (by linarith) (by linarith) hZlo hZhi).1
  have hsum := deterministic_phase_sum_bound (fun n => differencingPhase (Z / (n : ℝ)))
    L R S A δ hLpos hA.le hδ.le hhalf (by
      intro u hu hLu huR
      have hLu' : (L : ℝ) ≤ 2 * (u : ℝ) := by exact_mod_cast hLu
      have huX : (u : ℝ) ≤ X := (Nat.cast_le.mpr huR).trans hR
      obtain ⟨huexp, huZlo, huZhi⟩ := deterministic_phase_window S m D X u Z
        hS hSlarge hm hD hXlo hXhi (by linarith) huX hZlo hZhi
      apply reciprocal_sum_dyadic_piece A δ (u : ℝ) Z u L R hu rfl
      intro L' R'
      exact hU₀ u (hUlarge.trans huexp) Z L' R' huZlo huZhi)
  calc
    _ ≤ 2 * A * (R : ℝ) * Real.exp (-(4 * δ * S / 5)) := hsum
    _ ≤ (2 * A) * X * Real.exp (-(4 * δ / 5) * S) := by
      rw [show -(4 * δ / 5) * S = -(4 * δ * S / 5) by ring]
      gcongr

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DeterministicMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter ComplexConjugate
namespace Problem337

/-- A version of the finite second moment normalized by an arbitrary upper
cutoff, valid also when the ambient integer interval is empty. -/
theorem finite_second_moment_cutoff {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) (X E : ℝ)
    (hT : T.Nonempty) (hX : 0 ≤ X) (hE : 0 ≤ E) (hU : (U.card : ℝ) ≤ X)
    (hunit : ∀ u ∈ U, ∀ t ∈ T, ‖z u t‖ = 1)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * conj (z u s)‖ ≤ X * E) :
    (∑ u ∈ U, ‖(∑ t ∈ T, z u t) / (T.card : ℂ)‖ ^ 2) ≤
      X * (1 / (T.card : ℝ) + E) := by
  have ht : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hraw := finite_complex_second_moment_bound U T z (X * E) hunit hcorr
  have hweak : (∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2) ≤
      X * T.card + (T.card : ℝ) ^ 2 * (X * E) := by
    apply hraw.trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hU ht.le
    · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hX hE)
      nlinarith
  simp only [norm_div, Complex.norm_natCast, div_pow]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
  have heq : X * (1 / (T.card : ℝ) + E) * (T.card : ℝ) ^ 2 =
      X * T.card + (T.card : ℝ) ^ 2 * (X * E) := by
    field_simp
  rw [heq]
  exact hweak

/-- The full deterministic high-level second moment, with its two explicit
error terms. Distinctness of the indexed natural entries is the only arithmetic
property used in the off-diagonal estimate. -/
theorem deterministic_mean_two_errors_oai (D : ℝ) (hD : 255 ≤ D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ᶠ S : ℝ in atTop, ∀ (m X C ell : ℝ),
        m ≤ S → Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
        Real.exp (D * S) ≤ C → C ≤ Real.exp (2 * D * S) →
        1 ≤ ell → ell ≤ Real.exp (m / 2500) →
        ∀ {β : Type*} (T : Finset β) (t : β → ℕ),
          Set.InjOn t (T : Set β) →
          Real.exp (Real.log 2 * m) ≤ (T.card : ℝ) →
          (∀ i ∈ T, (t i : ℝ) ≤ Real.exp (101 * S)) →
          (∑ u ∈ Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊,
            ‖(∑ i ∈ T, differencingPhase (ell * C * (t i : ℝ) / (u : ℝ))) /
              (T.card : ℂ)‖ ^ 2) ≤
            X * (Real.exp (-Real.log 2 * m) + A * Real.exp (-c * S)) := by
  obtain ⟨A, c, hA, hc, hglobal⟩ := deterministic_reciprocal_sum_bound D hD
  refine ⟨A, c, hA, hc, ?_⟩
  filter_upwards [hglobal, eventually_ge_atTop (0 : ℝ)] with S hglobal hS
  intro m X C ell hm hXlo hXhi hClo hChi hell hellhi β T t ht hcard hsize
  have hX : 0 < X := (Real.exp_pos S).trans_le hXlo
  have hTpos : (0 : ℝ) < T.card := (Real.exp_pos _).trans_le hcard
  have hT : T.Nonempty := Finset.card_pos.mp (by exact_mod_cast hTpos)
  let U := Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊
  let z : ℕ → β → ℂ := fun u i => differencingPhase (ell * C * (t i : ℝ) / (u : ℝ))
  have hUcard : (U.card : ℝ) ≤ X := by
    have hh : U.card ≤ ⌊X⌋₊ := by
      dsimp [U]
      rw [Nat.card_Icc]
      omega
    exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hX.le)
  have hbound := finite_second_moment_cutoff U T z X (A * Real.exp (-c * S))
    hT hX.le (by positivity) hUcard (by intros; exact differencingPhase_norm _)
    (by
      intro i hi j hj hij
      have hne : t i ≠ t j := fun heq => hij (ht hi hj heq)
      obtain ⟨hZlo, hZhi⟩ := deterministic_frequency_bounds S m D C ell (t i) (t j)
        hS hm hell hellhi hClo hChi (hsize i hi) (hsize j hj) hne
      have hsum := hglobal m X (ell * C * ((t i : ℝ) - t j))
        (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊ hm hXlo hXhi
        (by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (Nat.lt_floor_add_one (Real.exp (-m / 10000) * X)).le) (Nat.floor_le hX.le) hZlo hZhi
      have heq : (∑ u ∈ U, z u i * conj (z u j)) =
          ∑ u ∈ U, differencingPhase (ell * C * ((t i : ℝ) - t j) / (u : ℝ)) := by
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [z]
        rw [← differencingPhase_sub]
        congr 1
        ring
      rw [heq]
      simpa only [U, mul_assoc, mul_comm, mul_left_comm] using hsum)
  have hinv : 1 / (T.card : ℝ) ≤ Real.exp (-Real.log 2 * m) := by
    calc
      1 / (T.card : ℝ) ≤ 1 / Real.exp (Real.log 2 * m) :=
        one_div_le_one_div_of_le (Real.exp_pos _) hcard
      _ = Real.exp (-Real.log 2 * m) := by rw [one_div, ← Real.exp_neg]; congr 1; ring
  apply hbound.trans
  exact mul_le_mul_of_nonneg_left (add_le_add hinv le_rfl) hX.le

end Problem337

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Problem337.deterministic_mean_two_errors_oai.{u_1} := @OAI.Problem337.deterministic_mean_two_errors_oai.{u_1}
