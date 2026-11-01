-- Prove2me | solution 1 for OAI.JointDickman.prime_agreement_distance_polynomial_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:54:42.566349+00:00
-- url     : https://prove2.me/submissions/d647c364-99b1-4165-9a94-d6bac52f5f28

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J000
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

section
-- module Solutions.OAIQ083_JD.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_ReciprocalDerivatives
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_ForwardDifference
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
        (hcont.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      have hdiff' : DifferentiableAt ℝ (fun y => forwardDifference hs f (y + h)) x := by
        exact ((hcont.contDiffAt (isOpen_Ioi.mem_nhds hx')).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp x
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
        hf.deriv_of_isOpen isOpen_Ioi (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
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
      rw [ih (hf.deriv_of_isOpen isOpen_Ioi (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
      rw [iteratedDeriv_succ']

private theorem smooth_iteratedDeriv_Ioi (k : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0)) : ContDiffOn ℝ ∞ (iteratedDeriv k f) (Ioi 0) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv_of_isOpen isOpen_Ioi (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)

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

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_FourierSecondMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

end Problem337

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_VanDerCorput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
        Complex.normSq_eq_norm_sq, ite_true, if_true, add_sub_cancel]
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_IteratedDifferencing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_CorrelationPhase
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_DiscreteFirstDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
  have hdhi : ∀ i ≤ N, d i < 1 := by intro i hi; have := hhi i hi; dsimp [d] <;> linarith
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_MonotoneBlocks
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_SecondDerivativeBudget
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_SeparatedIntervalCount
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_DiscreteSecondDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_FinitePowerSaving
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.EgyptianFractions_PhaseExtension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_SecondDifference
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.EgyptianFractions_SecondDerivativeTest
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
-- module Solutions.OAIQ083_JD.Erdos970_MertensClassical
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology

private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  ·                                                             
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  ·                                                         
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
                    
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
                            
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
                                                                                  
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
                                              
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
                                                                                   
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
                                                                                 
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
                            
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
            
  have hf1 : f 1 = 0 := by simp [hf_def]
                           
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
                          
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
                                                      
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
                                          
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
                                                         
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
                                                         
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
                                                     
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
                                                         
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
                            
    have hinj : InjOn f (Ici 1) := hmono.injOn
                                                                  
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
                                        
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
                               
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
                                                       
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
                                                                                  
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
                                                      
      rw [Real.log_mul hs1ne hlogne]
                                              
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
                                                  
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all <;> linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp <;> linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all <;> linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    all_goals try with_reducible_and_instances rfl
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast <;> ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all <;> linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast <;> linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    all_goals try with_reducible_and_instances rfl
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    all_goals try with_reducible_and_instances rfl
    simp

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply log_pos; norm_num
        linarith [E₁.nonneg]

end Mertens

end Erdos970
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditivePhaseBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relating real exponential notation to residue characters -/

namespace JointDickman

theorem additivePhase_add (s t : ℝ) :
    additivePhase (s + t) = additivePhase s * additivePhase t := by
  unfold additivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MonotonePartialSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite partial summation with decreasing nonnegative weights -/
namespace JointDickman
open Finset

lemma monotone_weighted_sum_range_bound (g : ℕ → ℂ) (w : ℕ → ℝ)
    {N : ℕ} {D : ℝ} (hD : 0 ≤ D) (hw : ∀ i, 0 ≤ w i)
    (hanti : Antitone w)
    (hpartial : ∀ k ≤ N, ‖∑ i ∈ range k, g i‖ ≤ D) :
    ‖∑ i ∈ range N, w i • g i‖ ≤ D * w 0 := by
  have htel (M : ℕ) : (∑ i ∈ range M, (w i-w (i+1))) = w 0-w M := by
    induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ, ih]; ring
  cases N with
  | zero => simpa using mul_nonneg hD (hw 0)
  | succ N =>
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel]
    have hterm : ‖w N • (∑ i ∈ range (N+1), g i)‖ ≤ w N * D := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw N)]
      exact mul_le_mul_of_nonneg_left (hpartial _ le_rfl) (hw N)
    have hsum : ‖∑ i ∈ range N, (w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ ≤
        (∑ i ∈ range N, (w i-w (i+1))) * D := by
      calc
        _ ≤ ∑ i ∈ range N, ‖(w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ range N, (w i-w (i+1))*D := by
          apply sum_le_sum
          intro i hi
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hanti (by omega)))]
          have hiN : i < N := mem_range.mp hi
          nlinarith [hpartial (i+1) (by omega), hanti (show i ≤ i+1 by omega)]
        _ = _ := (sum_mul ..).symm
    calc
      _ ≤ ‖w N • (∑ i ∈ range (N+1), g i)‖ +
          ‖∑ i ∈ range N, (w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ := norm_sub_le _ _
      _ ≤ w N*D+(∑ i ∈ range N, (w i-w (i+1)))*D := add_le_add hterm hsum
      _ = D*w 0 := by rw [htel]; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IntegerPartialSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decreasing weights on integer intervals -/
namespace JointDickman
open Finset

lemma sum_Icc_int_translate {E : Type*} [AddCommMonoid E] (g : ℤ → E)
    (L : ℤ) (N : ℕ) :
    ∑ n ∈ Icc L (L+(N:ℤ)-1), g n = ∑ i ∈ range N, g (L+i) := by
  rw [Int.Icc_eq_finset_map, sum_map]
  simp only [sub_add_cancel, add_sub_cancel_left, Int.toNat_natCast]
  rfl

lemma monotone_weighted_sum_Icc_bound (g : ℤ → ℂ) (w : ℤ → ℝ)
    (L R : ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ n, L ≤ n → 0 ≤ w n)
    (hanti : AntitoneOn w (Set.Ici L))
    (hpartial : ∀ V, L ≤ V → V ≤ R → ‖∑ n ∈ Icc L V, g n‖ ≤ D) :
    ‖∑ n ∈ Icc L R, w n • g n‖ ≤ D*w L := by
  by_cases hLR : L ≤ R
  · let N := (R+1-L).toNat
    have hN : (N:ℤ) = R+1-L := Int.toNat_of_nonneg (by omega)
    have hR : R = L+(N:ℤ)-1 := by omega
    rw [hR, sum_Icc_int_translate]
    have hh := monotone_weighted_sum_range_bound (fun i => g (L+i))
      (fun i => w (L+i)) hD (fun i => hw _ (by omega))
      (fun i j hij => hanti (by simp) (by simp) (by omega))
      (N := N) (by
        intro k hk
        by_cases hk0 : k = 0
        · simpa [hk0] using hD
        · rw [←sum_Icc_int_translate]
          exact hpartial _ (by omega) (by omega))
    simpa only [Nat.cast_zero, add_zero] using hh
  · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hLR), sum_empty, norm_zero]
    exact mul_nonneg hD (hw L le_rfl)

lemma rpow_weighted_sum_Icc_bound (g : ℤ → ℂ) (L R : ℤ)
    {D σ : ℝ} (hL : 0 < L) (hD : 0 ≤ D) (hσ : 0 ≤ σ)
    (hpartial : ∀ V, L ≤ V → V ≤ R → ‖∑ n ∈ Icc L V, g n‖ ≤ D) :
    ‖∑ n ∈ Icc L R, (((n:ℝ)^(-σ):ℝ):ℂ)*g n‖ ≤ D*(L:ℝ)^(-σ) := by
  have hh := monotone_weighted_sum_Icc_bound g (fun n => (n:ℝ)^(-σ)) L R hD
    (fun n hn => Real.rpow_nonneg (by exact_mod_cast (hL.le.trans hn)) _)
    (by
      intro i hi j hj hij
      apply Real.rpow_le_rpow_of_nonpos
      · exact_mod_cast hL.trans_le hi
      · exact_mod_cast hij
      · linarith) hpartial
  simpa only [Complex.real_smul] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaPoleFactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the simple pole of zeta at one -/
namespace JointDickman
open Filter
open scoped Topology

 theorem zetaPoleFactor_eq {s : ℂ} (hs : s ≠ 1) : zetaPoleFactor s = (s-1)*riemannZeta s := by
  simp only [zetaPoleFactor,hs,ite_false, if_false]

 theorem zetaPoleFactor_continuousAt_one : ContinuousAt zetaPoleFactor 1 := by
  rw [← continuousWithinAt_compl_self,ContinuousWithinAt,zetaPoleFactor_one]
  apply riemannZeta_residue_one.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (zetaPoleFactor_eq hs).symm

 theorem zetaPoleFactor_differentiableAt {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ zetaPoleFactor s := by
  have heq : zetaPoleFactor =ᶠ[𝓝 s] (fun t => (t-1)*riemannZeta t) := by
    filter_upwards [eventually_ne_nhds hs] with t ht
    exact zetaPoleFactor_eq ht
  exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq heq

 theorem zetaPoleFactor_analyticAt_one : AnalyticAt ℂ zetaPoleFactor 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ zetaPoleFactor_continuousAt_one
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact zetaPoleFactor_differentiableAt hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaPoleBranch
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A normalized analytic power of the pole-removed zeta function -/
namespace JointDickman
open Set

theorem zetaPoleFactor_differentiable : Differentiable ℂ zetaPoleFactor := by
  intro s
  by_cases hs : s = 1
  · subst s
    exact zetaPoleFactor_analyticAt_one.differentiableAt
  · exact zetaPoleFactor_differentiableAt hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaContourBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for zeta on the finite Perron contour -/
namespace JointDickman
open Set Complex

theorem zetaPole_compact_bound : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, ‖s‖ ≤ 6 → s ≠ 1 → ‖riemannZeta s‖ ≤ C/‖s-1‖ := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) 6).exists_bound_of_continuousOn
    zetaPoleFactor_differentiable.continuous.continuousOn
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),fun s hs hs1 => ?_⟩
  have hbound := hC s (by simpa only [Metric.mem_closedBall,dist_zero_right] using hs)
  rw [zetaPoleFactor_eq hs1,norm_mul] at hbound
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr
  calc
    _ = ‖s-1‖*‖riemannZeta s‖ := mul_comm _ _
    _ ≤ C := hbound
    _ ≤ max C 1 := le_max_left _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterDistanceInput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published Dirichlet-character distance estimate

Only the fixed-modulus consequence of Klurman--Mangerel--Teräväinen,
*Multiplicative functions in short arithmetic progressions*, Proc. London
Math. Soc. 127 (2023), 366--446, Lemma 7.8, is assumed here. That lemma
bounds the infimum over `|t| ≤ 10X` by
`(1/4) log (log X / log (2 conductor χ)) + O(1)`.
For a fixed character the conductor term is absorbed in the constant.
The primes dividing the modulus only add nonnegative terms to our distance.
No modified character, bin label, or short average occurs in this input.
Source: https://doi.org/10.1112/plms.12546, arXiv:1909.12280, Lemma 7.8.
-/
namespace JointDickman
open Classical

theorem characterArithmetic_prime {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    characterArithmetic χ p = χ (p : ZMod q) := by
  simp only [characterArithmetic,ArithmeticFunction.coe_mk,hp.ne_zero,ite_false, if_false]

theorem characterArithmetic_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖characterArithmetic χ n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · simpa only [characterArithmetic,ArithmeticFunction.coe_mk,hn,ite_false, if_false] using χ.norm_le_one (n : ZMod q)

open Filter PublishedInputs
open scoped Topology


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal primes on fixed logarithmic intervals

Mertens' second theorem supplies the fixed-power interval limit. Together
with Chebyshev's estimate, it bounds the error in the marginal tuple count.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primesLE_eq_filter (N : ℕ) :
    Nat.primesLE N = (Icc 2 N).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨⟨hp.two_le, hle⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨hle, hp⟩

/-- The Mertens remainder tends to its additive constant. -/
theorem primeReciprocalSum_remainder_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ M : ℝ, Tendsto (fun x : ℝ => primeReciprocalSum x - Real.log (Real.log x))
      atTop (𝓝 M) := by
  obtain ⟨M, C, _, hC⟩ := hM
  refine ⟨M, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hlim : Tendsto (fun x : ℝ => C / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa [Real.norm_eq_abs, primeReciprocalSum, primesLE_eq_filter] using hC x hx

theorem largePrimeSet_eq_sdiff {N y : ℝ} (hy : 0 ≤ y) :
    largePrimeSet N y = Nat.primesLE ⌊N⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
  apply Finset.ext
  intro p
  rw [Finset.mem_sdiff]
  simp only [largePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpy⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    rintro ⟨hpy', _⟩
    exact (not_le_of_gt hpy) ((Nat.le_floor_iff hy).mp hpy')
  · rintro ⟨⟨hpN, hp⟩, hnot⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    by_contra h
    exact hnot ⟨Nat.le_floor (le_of_not_gt h), hp⟩

theorem largePrimeSet_reciprocal_eq {N y : ℝ} (hy : 0 ≤ y) (hyN : y ≤ N) :
    (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) = primeReciprocalSum N - primeReciprocalSum y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊N⌋₊ := by
    intro p hp
    obtain ⟨hpy, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy.trans (Nat.floor_mono hyN), hp⟩
  rw [largePrimeSet_eq_sdiff hy]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

/-- Mertens' logarithmic interval mass, at the exact powers used in the
smooth-number inclusion-exclusion. -/
theorem largePrimeSet_reciprocal_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℝ => ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ))
      atTop (𝓝 (-Real.log c)) := by
  obtain ⟨M, hrem⟩ := primeReciprocalSum_remainder_tendsto hM
  have hpower : Tendsto (fun N : ℝ => N ^ c) atTop atTop := tendsto_rpow_atTop hc
  have hlim := (hrem.sub (hrem.comp hpower)).sub_const (Real.log c)
  have heq : (fun N : ℝ =>
      (primeReciprocalSum N - Real.log (Real.log N)) -
      (primeReciprocalSum (N ^ c) - Real.log (Real.log (N ^ c))) - Real.log c) =ᶠ[atTop]
      (fun N : ℝ => ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := lt_trans zero_lt_one hN
    have hlog : 0 < Real.log N := Real.log_pos hN
    have hpN : N ^ c ≤ N := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN.le hc1
    rw [largePrimeSet_reciprocal_eq (Real.rpow_nonneg hN0.le c) hpN,
      Real.log_rpow hN0, Real.log_mul hc.ne' hlog.ne']
    ring
  simpa using hlim.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic cancellation in the squarefree Euler logarithm -/
namespace JointDickman

 theorem complex_log_error_bound {v : ℂ} {r : ℝ} (hr : r < 1) (hv : ‖v‖ ≤ r) :
    ‖Complex.log (1+v)-v‖ ≤ ‖v‖^2/(1-r) := by
  have hv1 : ‖v‖ < 1 := hv.trans_lt hr
  have hinv : (1-‖v‖)⁻¹ ≤ (1-r)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  calc
    _ ≤ ‖v‖^2*(1-‖v‖)⁻¹/2 := Complex.norm_log_one_add_sub_self_le hv1
    _ ≤ ‖v‖^2*(1-‖v‖)⁻¹ := div_le_self (by positivity) (by norm_num)
    _ ≤ ‖v‖^2*(1-r)⁻¹ := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    _ = _ := rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterEuler
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The absolutely convergent Euler correction for squarefree character sums -/
namespace JointDickman

theorem characterPrimePower_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (p : Nat.Primes) :
    ‖characterPrimePower χ s p‖ ≤ ‖(p.val:ℂ)^(-s)‖ := by
  rw [characterPrimePower, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeCharacterFactorization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic factorization of the twisted squarefree Dirichlet series -/
namespace JointDickman

theorem primeCharacterLog_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => -Complex.log (1-characterPrimePower χ s p)) := by
  convert! (summable_dirichletSummand χ hs).of_norm.clog_one_sub.neg.subtype Nat.Prime using 1
  all_goals try with_reducible_and_instances rfl

theorem primeCharacterLog_exp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : Complex.exp (primeCharacterLog χ s) = χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  exact χ.LSeries_eulerProduct_exp_log hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterEulerRemainder
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear prime sum in a character Euler logarithm

The nonlinear Euler terms have one absolute summable majorant throughout
Re(s) > 1, independent of both the character and its modulus.
-/
namespace JointDickman
open Complex

theorem primeCharacterLinearSum_summable {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => characterPrimePower χ s p) := by
  apply Summable.of_norm
  convert! (summable_dirichletSummand χ hs).subtype Nat.Prime using 1
  all_goals try with_reducible_and_instances rfl

theorem primeCharacterLog_linear_error {q : ℕ}
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖primeCharacterLog χ s - primeCharacterLinearSum χ s‖ ≤
      primeEulerRemainderConstant := by
  have hsum : Summable (fun p : Nat.Primes => 2*(p.val:ℝ)^(-2:ℝ)) :=
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ) < -1)).subtype Nat.Prime).mul_left 2
  have hpoint (p : Nat.Primes) :
      ‖-Complex.log (1-characterPrimePower χ s p)-characterPrimePower χ s p‖ ≤
        2*(p.val:ℝ)^(-2:ℝ) := by
    have hhalf : ‖characterPrimePower χ s p‖ ≤ 1/2 :=
      (characterPrimePower_norm_le χ p).trans (Complex.norm_prime_cpow_le_one_half p hs)
    have hnorm : ‖characterPrimePower χ s p‖ ≤ (p.val:ℝ)^(-1:ℝ) := by
      calc
        _ ≤ ‖(p.val:ℂ)^(-s)‖ := characterPrimePower_norm_le χ p
        _ = (p.val:ℝ)^(-s.re) := by
          rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast p.property.one_le) (by linarith)
    have hlog := complex_log_error_bound (by norm_num : (1/2:ℝ) < 1)
      (show ‖-characterPrimePower χ s p‖ ≤ 1/2 by simpa using hhalf)
    have he : -Complex.log (1-characterPrimePower χ s p)-characterPrimePower χ s p =
        -(Complex.log (1+(-characterPrimePower χ s p))-(-characterPrimePower χ s p)) := by
      simp only [sub_eq_add_neg] <;> ring
    rw [he, norm_neg]
    calc
      _ ≤ ‖characterPrimePower χ s p‖^2/(1-(1/2:ℝ)) := by simpa using hlog
      _ ≤ ((p.val:ℝ)^(-1:ℝ))^2/(1-(1/2:ℝ)) := by gcongr
      _ = 2*(p.val:ℝ)^(-2:ℝ) := by
        rw [←Real.rpow_mul_natCast (by positivity)]
        norm_num
        ring
  rw [primeCharacterLog, primeCharacterLinearSum,
    ←Summable.tsum_sub (primeCharacterLog_summable χ hs)
      (primeCharacterLinearSum_summable χ hs)]
  have herror := hsum.of_norm_bounded hpoint
  exact (norm_tsum_le_tsum_norm herror.norm).trans
    (herror.norm.tsum_le_tsum hpoint hsum)

theorem primeCharacterLog_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    (primeCharacterLog χ s).re = Real.log ‖χ.LFunction s‖ := by
  rw [←primeCharacterLog_exp χ hs, Complex.norm_exp, Real.log_exp]

theorem primeCharacterLinearSum_re_error {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    |(primeCharacterLinearSum χ s).re - Real.log ‖χ.LFunction s‖| ≤
      primeEulerRemainderConstant := by
  rw [←primeCharacterLog_re χ hs, abs_sub_comm]
  exact (Complex.abs_re_le_norm (primeCharacterLog χ s-primeCharacterLinearSum χ s)).trans
    (primeCharacterLog_linear_error χ hs)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MertensDischarge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Classical Mertens estimates

The reciprocal-prime sum and prime-product estimates use the same indexing
convention: the intervals `(0, floor x]` and `[2, floor x]` contain the same
primes.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem prime_filter_Icc_eq_Ioc (N : ℕ) :
    (Icc 2 N).filter Nat.Prime = (Ioc 0 N).filter Nat.Prime := by
  ext p
  simp only [mem_filter,mem_Icc,mem_Ioc]
  constructor
  · rintro ⟨⟨hp,hN⟩,hprime⟩
    exact ⟨⟨by omega,hN⟩,hprime⟩
  · rintro ⟨⟨_,hN⟩,hprime⟩
    exact ⟨⟨hprime.two_le,hN⟩,hprime⟩

theorem primeReciprocalMertensInput : PublishedInputs.PrimeReciprocalMertensInput := by
  refine ⟨Erdos970.Mertens.M,Real.log 4 + 6 + Erdos970.Mertens.E₁,?_,?_⟩
  · have hE := Erdos970.Mertens.E₁.nonneg
    positivity
  · intro x hx
    rw [prime_filter_Icc_eq_Ioc]
    exact Erdos970.Mertens.E₂p.abs_le hx

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterPrimeCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing finite character distances with damped prime sums -/
namespace JointDickman
open Complex Finset
open scoped BigOperators

/-- A finite distance dominates the absolutely convergent damped distance,
with the missing mass accounted for explicitly. -/
theorem finite_distance_lower {ι : Type*} (S : Finset ι) (a b v : ι → ℝ)
    (hb : Summable b) (hb0 : ∀ i, 0 ≤ b i)
    (hv : ∀ i, |v i| ≤ 1) (hba : ∀ i ∈ S, b i ≤ a i) :
    2*(∑ i ∈ S, b i) - ∑' i, b i - ∑' i, v i*b i ≤
      ∑ i ∈ S, (1-v i)*a i := by
  have hprod : Summable (fun i => v i*b i) := hb.of_norm_bounded
    (fun i => by rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hb0 i)]
                 exact mul_le_of_le_one_left (hb0 i) (hv i))
  have hp : ∀ i, 0 ≤ b i+v i*b i := by
    intro i
    have h := (abs_le.mp (hv i)).1
    nlinarith [hb0 i]
  have hsum := (hb.add hprod).sum_le_tsum S (fun i _ => hp i)
  rw [Summable.tsum_add hb hprod, sum_add_distrib] at hsum
  have hlocal : (∑ i ∈ S, b i) - (∑ i ∈ S, v i*b i) ≤
      ∑ i ∈ S, (1-v i)*a i := by
    rw [←sum_sub_distrib]
    apply sum_le_sum
    intro i hi
    have h := (abs_le.mp (hv i)).2
    nlinarith [hba i hi]
  linarith

theorem characterPrimePhase_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (p : Nat.Primes) : ‖characterPrimePhase χ t p‖ ≤ 1 := by
  rw [characterPrimePhase, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_im,Complex.ofReal_im,
    Complex.I_re,Complex.I_im, mul_zero, zero_sub, neg_zero, Real.exp_zero, mul_one]
  exact χ.norm_le_one (p.val:ZMod q)

theorem characterPrimePower_eq_phase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (p : Nat.Primes) :
    characterPrimePower χ ((σ:ℂ)+(t:ℂ)*I) p =
      characterPrimePhase χ t p*((p.val:ℝ)^(-σ):ℝ) := by
  have hp : (0:ℝ) < p.val := by exact_mod_cast p.property.pos
  have hpC : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [characterPrimePower, Complex.cpow_def_of_ne_zero hpC]
  rw [show (p.val:ℂ) = ((p.val:ℝ):ℂ) by simp,
    ←Complex.ofReal_log hp.le]
  have he : (Real.log (p.val:ℝ):ℂ)*(-((σ:ℂ)+(t:ℂ)*I)) =
      -((t*Real.log p.val:ℝ):ℂ)*I + ((Real.log p.val*(-σ):ℝ):ℂ) := by
    push_cast <;> ring
  rw [he,Complex.exp_add,←Complex.ofReal_exp,←Real.rpow_def_of_pos hp]
  simp only [characterPrimePhase]
  ring

theorem primeCutoff_sum (f : ℕ → ℝ) (X : ℝ) :
    (∑ p ∈ primeCutoff X, f p.val) = ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime, f p := by
  exact sum_subtype_eq_sum_filter f

theorem characterDistance_primeCutoff {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X t : ℝ) :
    PublishedInputs.primeDistanceSquared (characterArithmetic χ) X t =
      ∑ p ∈ primeCutoff X, (1-(characterPrimePhase χ t p).re)/(p.val:ℝ) := by
  unfold PublishedInputs.primeDistanceSquared
  rw [←primeCutoff_sum]
  apply sum_congr rfl
  intro p _
  rw [characterArithmetic_prime χ p.property]
  rfl

/-- The prime cutoff can be replaced by the Euler half-plane without hiding
any arithmetic cancellation in an assumption. -/
theorem characterDistance_damped_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    2*(∑ p ∈ primeCutoff X, (p.val:ℝ)^(-σ)) -
      (∑' p : Nat.Primes, (p.val:ℝ)^(-σ)) -
      (primeCharacterLinearSum χ ((σ:ℂ)+(t:ℂ)*I)).re ≤
      PublishedInputs.primeDistanceSquared (characterArithmetic χ) X t := by
  have hs : 1 < ((σ:ℂ)+(t:ℂ)*I).re := by simpa using hσ
  have hb : Summable (fun p : Nat.Primes => (p.val:ℝ)^(-σ)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).subtype Nat.Prime
  have hlin : (∑' p : Nat.Primes, (characterPrimePhase χ t p).re*(p.val:ℝ)^(-σ)) =
      (primeCharacterLinearSum χ ((σ:ℂ)+(t:ℂ)*I)).re := by
    rw [primeCharacterLinearSum,Complex.re_tsum (primeCharacterLinearSum_summable χ hs)]
    apply tsum_congr
    intro p
    rw [characterPrimePower_eq_phase,Complex.mul_re]
    simp
  rw [characterDistance_primeCutoff]
  simp_rw [div_eq_mul_inv]
  rw [←hlin]
  apply finite_distance_lower (primeCutoff X)
    (fun p => (p.val:ℝ)⁻¹) (fun p => (p.val:ℝ)^(-σ))
    (fun p => (characterPrimePhase χ t p).re) hb
    (fun _ => by positivity)
    (fun p => (Complex.abs_re_le_norm _).trans (characterPrimePhase_norm_le χ t p))
  intro p _
  rw [←Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast p.property.one_le) (by linarith)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDamping
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform error from damping prime reciprocal weights -/
namespace JointDickman
open Finset

lemma prime_reciprocal_damping {p δ : ℝ} (hp : 1 ≤ p) (_hδ : 0 ≤ δ) :
    p⁻¹ - p^(-(1+δ)) ≤ δ*(Real.log p/p) := by
  have hp0 : 0 < p := by linarith
  have he := Real.add_one_le_exp (-(δ*Real.log p))
  have hr : p^(-(1+δ)) = p⁻¹*Real.exp (-(δ*Real.log p)) := by
    rw [show -(1+δ) = -1 + -δ by ring,Real.rpow_add hp0,Real.rpow_neg_one,
      Real.rpow_def_of_pos hp0]
    congr 2
    ring
  rw [hr]
  have hm := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp0.le)
  change p⁻¹ * (-(δ*Real.log p)+1) ≤ p⁻¹ * Real.exp (-(δ*Real.log p)) at hm
  rw [div_eq_mul_inv]
  nlinarith

lemma primeCutoff_log_reciprocal_bound {X : ℝ} (hX : 1 ≤ X) :
    (∑ p ∈ primeCutoff X, Real.log p.val/(p.val:ℝ)) ≤
      Real.log X + (Real.log 4+4) := by
  rw [primeCutoff_sum (fun p : ℕ => Real.log (p:ℝ)/(p:ℝ)),prime_filter_Icc_eq_Ioc,
    Erdos970.Mertens.sum_log_prime_div_eq]
  linarith [Erdos970.Mertens.E₁p.le hX]

lemma primeCutoff_damping_bound {X δ : ℝ} (hX : 1 ≤ X) (hδ : 0 ≤ δ) :
    (∑ p ∈ primeCutoff X, (p.val:ℝ)⁻¹) -
      (∑ p ∈ primeCutoff X, (p.val:ℝ)^(-(1+δ))) ≤
      δ*(Real.log X+(Real.log 4+4)) := by
  calc
    _ = ∑ p ∈ primeCutoff X, ((p.val:ℝ)⁻¹-(p.val:ℝ)^(-(1+δ))) := by
      rw [sum_sub_distrib]
    _ ≤ ∑ p ∈ primeCutoff X, δ*(Real.log p.val/(p.val:ℝ)) := by
      apply sum_le_sum
      intro p _
      exact prime_reciprocal_damping (by exact_mod_cast p.property.one_le) hδ
    _ = δ*∑ p ∈ primeCutoff X, Real.log p.val/(p.val:ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeCutoff_log_reciprocal_bound hX) hδ

lemma primeCutoff_log_scale_damping {X : ℝ} (hX : 2 ≤ X) :
    (∑ p ∈ primeCutoff X, (p.val:ℝ)⁻¹) -
      (∑ p ∈ primeCutoff X, (p.val:ℝ)^(-(1+1/Real.log X))) ≤
      1+(Real.log 4+4)/Real.log 2 := by
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ Real.log 4+4 := by positivity
  calc
    _ ≤ (1/Real.log X)*(Real.log X+(Real.log 4+4)) :=
      primeCutoff_damping_bound (by linarith) (by positivity)
    _ = 1+(Real.log 4+4)/Real.log X := by field_simp
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_left hC hlog2
      (Real.log_le_log (by norm_num) hX)) _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DampedPrimeMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The total mass of damped prime reciprocals -/
namespace JointDickman
open Complex Finset

lemma dampedPrimeMass_le_log_zeta {σ : ℝ} (hσ : 1 < σ) :
    (∑' p : Nat.Primes, (p.val:ℝ)^(-σ)) ≤
      Real.log ‖riemannZeta (σ:ℂ)‖+primeEulerRemainderConstant := by
  let χ : DirichletCharacter ℂ 1 := 1
  have hs : 1 < (σ:ℂ).re := hσ
  have hlin : (primeCharacterLinearSum χ (σ:ℂ)).re =
      ∑' p : Nat.Primes, (p.val:ℝ)^(-σ) := by
    rw [primeCharacterLinearSum,Complex.re_tsum (primeCharacterLinearSum_summable χ hs)]
    apply tsum_congr
    intro p
    have hp := characterPrimePower_eq_phase χ σ 0 p
    have hpone : (p.val:ZMod 1) = 1 := Subsingleton.elim _ _
    simpa [characterPrimePhase,χ,hpone] using congrArg Complex.re hp
  have h := (abs_le.mp (primeCharacterLinearSum_re_error χ hs)).2
  rw [hlin] at h
  simpa using (show (∑' p : Nat.Primes, (p.val:ℝ)^(-σ)) ≤
    Real.log ‖χ.LFunction (σ:ℂ)‖+primeEulerRemainderConstant by linarith)

lemma dampedPrimeMass_log_bound : ∃ C : ℝ, ∀ X : ℝ, Real.exp 1 ≤ X →
    (∑' p : Nat.Primes, (p.val:ℝ)^(-(1+1/Real.log X))) ≤
      Real.log (Real.log X)+C := by
  obtain ⟨K,hK,hbound⟩ := zetaPole_compact_bound
  refine ⟨Real.log K+primeEulerRemainderConstant,?_⟩
  intro X hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog1 : 1 ≤ Real.log X := by
    simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlog : 0 < Real.log X := by linarith
  let σ : ℝ := 1+1/Real.log X
  have hσ : 1 < σ := by dsimp [σ] <;> linarith [one_div_pos.mpr hlog]
  have hσ2 : σ ≤ 2 := by
    dsimp [σ]
    have := (div_le_one hlog).mpr hlog1
    linarith
  have hsne : (σ:ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re,Complex.one_re] at this
    linarith
  have hζ := hbound (σ:ℂ) (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0<σ)]; linarith) hsne
  have hnorm : ‖(σ:ℂ)-1‖ = 1/Real.log X := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by dsimp [σ]; positivity : 0<σ-1)]
    dsimp [σ]
    ring
  rw [hnorm] at hζ
  have hζ' : ‖riemannZeta (σ:ℂ)‖ ≤ K*Real.log X := by
    convert hζ using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
  have hz0 : 0 < ‖riemannZeta (σ:ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hσ)
  have hlogbound := Real.log_le_log hz0 hζ'
  rw [Real.log_mul hK.ne' hlog.ne'] at hlogbound
  have h := dampedPrimeMass_le_log_zeta hσ
  dsimp [σ] at h hlogbound
  linarith

lemma primeCutoff_mass_lower : ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
    Real.log (Real.log X)-C ≤ ∑ p ∈ primeCutoff X, (p.val:ℝ)⁻¹ := by
  obtain ⟨C,hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨C,?_⟩
  intro X hX
  have h := (abs_le.mp (hC X hX)).1
  rw [primeCutoff_sum (fun p : ℕ => (p:ℝ)⁻¹),prime_filter_Icc_eq_Ioc]
  simp only [one_div] at h
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterDistanceEuler
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euler logarithm lower bound for character distance -/
namespace JointDickman
open Complex

/-- The error is absolute and independent of the modulus, character and
frequency. This bridge uses only Mertens' estimates and absolute Euler tails. -/
theorem characterDistance_ge_log_sub_L : ∃ C : ℝ,
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (X : ℝ), max 2 (Real.exp 1) ≤ X → ∀ t : ℝ,
      Real.log (Real.log X) -
        Real.log ‖χ.LFunction ((1+1/Real.log X:ℝ)+(t:ℂ)*I)‖ - C ≤
        PublishedInputs.primeDistanceSquared (characterArithmetic χ) X t := by
  obtain ⟨K,hK⟩ := dampedPrimeMass_log_bound
  obtain ⟨M,hM⟩ := primeCutoff_mass_lower
  let E : ℝ := 1+(Real.log 4+4)/Real.log 2
  refine ⟨2*M+2*E+K+primeEulerRemainderConstant,?_⟩
  intro q _ χ X hX t
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hs : 1 < 1+1/Real.log X := by linarith [one_div_pos.mpr hlog]
  have hdist := characterDistance_damped_lower χ X t hs
  have hmass := hM X hX2
  have hdamp := primeCutoff_log_scale_damping hX2
  have htotal := hK X hXe
  have hsC : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by simpa using hs
  have hlinear := (abs_le.mp (primeCharacterLinearSum_re_error χ hsC)).2
  dsimp [E]
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterFourierExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Fourier expansion of character-twisted logarithmic sums -/
namespace JointDickman
open Finset Complex Problem337

lemma characterFourierCoefficient_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ZMod q) :
    ‖characterFourierCoefficient χ k‖ ≤ 1 := by
  have hsum : ‖ZMod.dft (fun n => χ n) k‖ ≤ (q:ℝ) := by
    rw [ZMod.dft_apply]
    calc
      _ ≤ ∑ n : ZMod q, ‖ZMod.stdAddChar (-(n*k)) • χ n‖ := norm_sum_le _ _
      _ ≤ ∑ _n : ZMod q, (1:ℝ) := by
        apply sum_le_sum
        intro n _
        simpa [smul_eq_mul,norm_mul,ZMod.stdAddChar_apply,Circle.norm_coe] using χ.norm_le_one n
      _ = q := by simp
  rw [characterFourierCoefficient,norm_mul,norm_inv,Complex.norm_natCast]
  have hq : 0 < (q:ℝ) := by exact_mod_cast NeZero.pos q
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hq.le)).trans_eq
    (inv_mul_cancel₀ hq.ne')

lemma character_fourier_expansion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ZMod q) :
    χ n = ∑ k : ZMod q, characterFourierCoefficient χ k * ZMod.stdAddChar (k*n) := by
  have h := congrFun ((ZMod.dft (N := q) (E := ℂ)).symm_apply_apply (fun n => χ n)) n
  rw [ZMod.invDFT_apply] at h
  rw [←h,smul_eq_mul,mul_sum]
  apply sum_congr rfl
  intro k _
  simp only [characterFourierCoefficient,smul_eq_mul]
  ring

lemma stdAddChar_mul_int_as_phase {q : ℕ} [NeZero q] (k : ZMod q) (n : ℤ) :
    ZMod.stdAddChar (k*(n:ZMod q)) =
      differencingPhase ((k.val:ℝ)/q*(n:ℝ)) := by
  conv_lhs => rw [←ZMod.natCast_zmod_val k]
  have he : (k.val:ZMod q)*(n:ZMod q) = ((k.val:ℤ)*n:ℤ) := by push_cast; rfl
  rw [he,ZMod.stdAddChar_coe]
  unfold differencingPhase
  congr 1
  push_cast
  ring

lemma differencingPhase_add (x y : ℝ) :
    differencingPhase (x+y) = differencingPhase x*differencingPhase y :=
  additivePhase_add x y

lemma character_log_sum_fourier {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset ℤ) (Z : ℝ) :
    (∑ n ∈ S, χ (n:ZMod q)*differencingPhase (Z*Real.log (n:ℝ))) =
      ∑ k : ZMod q, characterFourierCoefficient χ k *
        ∑ n ∈ S, differencingPhase ((k.val:ℝ)/q*(n:ℝ)+Z*Real.log (n:ℝ)) := by
  conv_lhs => arg 2; ext n; rw [character_fourier_expansion χ (n:ZMod q),sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  rw [stdAddChar_mul_int_as_phase,differencingPhase_add,mul_assoc]

lemma character_log_sum_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset ℤ) (Z K : ℝ) (_hK : 0 ≤ K)
    (hbound : ∀ a : ℝ, ‖∑ n ∈ S,
      differencingPhase (a*(n:ℝ)+Z*Real.log (n:ℝ))‖ ≤ K) :
    ‖∑ n ∈ S, χ (n:ZMod q)*differencingPhase (Z*Real.log (n:ℝ))‖ ≤ (q:ℝ)*K := by
  rw [character_log_sum_fourier]
  calc
    _ ≤ ∑ k : ZMod q, ‖characterFourierCoefficient χ k *
        ∑ n ∈ S, differencingPhase ((k.val:ℝ)/q*(n:ℝ)+Z*Real.log (n:ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _k : ZMod q, K := by
      apply sum_le_sum
      intro k _
      rw [norm_mul]
      exact (mul_le_mul (characterFourierCoefficient_norm_le χ k)
        (hbound _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = (q:ℝ)*K := by simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseDifferencingBudget
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter

namespace JointDickman
open Problem337

/-- The natural cutoff in van der Corput differencing preserves a power saving.
All size conditions here are scalar and hold eventually for fixed parameters. -/
theorem logarithmic_differencing_budget (r N : ℕ) (U α C : ℝ)
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
  have hH : 1 ≤ H := (Nat.le_floor_iff hp.le).2 (by norm_num <;> linarith)
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
theorem logarithmic_differencing_budget_eventually (r : ℕ) (α C : ℝ)
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
  exact logarithmic_differencing_budget r N U α C hU hα (by linarith)
    hC hcut herror hUN hNU a hsupport hnorm hterminal

end JointDickman

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseIntervalBudget
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace JointDickman
open Problem337

/-- Ambient normalization converts a terminal forward-difference estimate
on every shortened subinterval into cancellation on the original interval. -/
theorem logarithmic_interval_budget_eventually (r : ℕ) (α C : ℝ)
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
    logarithmic_differencing_budget_eventually r α C hα hαsmall hC] with U hU hbudget
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

end JointDickman

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseDerivatives
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the logarithmic phases in character sums -/
namespace JointDickman
open Set Filter Problem337
open scoped Topology ContDiff

lemma logarithmic_phase_smooth (Z : ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => Z*Real.log y) (Ioi 0) :=
  contDiffOn_const.mul (Real.contDiffOn_log.mono (fun _ hx => ne_of_gt hx))

lemma logarithmic_phase_iteratedDeriv (k : ℕ) (Z : ℝ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (k+1) (fun y : ℝ => Z*Real.log y) x =
      (-1:ℝ)^k*(k.factorial:ℝ)*Z/x^(k+1) := by
  have he : deriv (fun y : ℝ => Z*Real.log y) =ᶠ[𝓝 x] (fun y => Z/y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    have hd := (Real.hasDerivAt_log (ne_of_gt hy)).const_mul Z
    simpa only [div_eq_mul_inv] using hd.deriv
  rw [iteratedDeriv_succ',he.iteratedDeriv_eq k]
  exact reciprocal_phase_iteratedDeriv k Z x

lemma logarithmic_linear_phase_smooth (a Z : ℝ) :
    ContDiffOn ℝ ∞ (fun y : ℝ => a*y+Z*Real.log y) (Ioi 0) :=
  (contDiffOn_const.mul contDiffOn_id).add (logarithmic_phase_smooth Z)

lemma logarithmic_linear_phase_iteratedDeriv (k : ℕ) (a Z : ℝ)
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (k+2) (fun y : ℝ => a*y+Z*Real.log y) x =
      (-1:ℝ)^(k+1)*((k+1).factorial:ℝ)*Z/x^(k+2) := by
  have hlin : ContDiffAt ℝ (k+2) (fun y : ℝ => a*y) x :=
    (contDiff_const.mul contDiff_id).contDiffAt
  have hlog : ContDiffAt ℝ (k+2) (fun y : ℝ => Z*Real.log y) x :=
    ((logarithmic_phase_smooth Z).contDiffAt (isOpen_Ioi.mem_nhds hx)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [iteratedDeriv_fun_add hlin hlog,iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_fun_id,show k+2 ≠ 0 by omega,show k+2 ≠ 1 by omega,
    ite_false, if_false,mul_zero,zero_add]
  exact logarithmic_phase_iteratedDeriv (k+1) Z hx

lemma abs_logarithmic_linear_phase_iteratedDeriv (k : ℕ) (a Z : ℝ)
    {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv (k+2) (fun y : ℝ => a*y+Z*Real.log y) x| =
      ((k+1).factorial:ℝ)*|Z|/x^(k+2) := by
  rw [logarithmic_linear_phase_iteratedDeriv k a Z hx]
  simp [abs_div,abs_mul,abs_pow,abs_of_pos hx]

lemma logarithmic_linear_forwardDifference_second_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (a Z : ℝ) {U V x : ℝ}
    (hU : 0 < U) (hx : U ≤ x) (hxV : x+hs.sum ≤ V) :
    hs.prod*((hs.length+1).factorial:ℝ)*|Z|/V^(hs.length+2) ≤
      |iteratedDeriv 2 (forwardDifference hs (fun y => a*y+Z*Real.log y)) x| ∧
    |iteratedDeriv 2 (forwardDifference hs (fun y => a*y+Z*Real.log y)) x| ≤
      hs.prod*((hs.length+1).factorial:ℝ)*|Z|/U^(hs.length+2) := by
  obtain ⟨ξ,hxξ,hξ,he⟩ := iteratedDeriv_forwardDifference_eq 2 hs hhs
    (logarithmic_linear_phase_smooth a Z) (hU.trans_le hx)
  have hξ0 : 0 < ξ := hU.trans_le (hx.trans hxξ)
  have hp : 0 ≤ hs.prod := List.prod_nonneg (fun h hh => (hhs h hh).le)
  rw [he,abs_mul,abs_of_nonneg hp,
    abs_logarithmic_linear_phase_iteratedDeriv hs.length a Z hξ0]
  constructor
  · have hpow := pow_le_pow_left₀ hξ0.le (hξ.trans hxV) (hs.length+2)
    have hd := div_le_div_of_nonneg_left (by positivity : 0≤((hs.length+1).factorial:ℝ)*|Z|)
      (pow_pos hξ0 _) hpow
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hd hp
  · have hpow := pow_le_pow_left₀ hU.le (hx.trans hxξ) (hs.length+2)
    have hd := div_le_div_of_nonneg_left (by positivity : 0≤((hs.length+1).factorial:ℝ)*|Z|)
      (pow_pos hU _) hpow
    simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hd hp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseSecondDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second-derivative bound after logarithmic differencing -/
namespace JointDickman
open Set Problem337
open scoped ContDiff

/-- All derivative information is proved for the actual logarithmic phase.
The interval includes the full displacement introduced by differencing. -/
theorem logarithmic_difference_sum_bound (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (a Z U x : ℝ) (N : ℕ)
    (hZ : Z ≠ 0) (hU : 0 < U) (hx : U ≤ x)
    (hend : x+(N:ℝ)+hs.sum ≤ 4*U) :
    let lam : ℝ := hs.prod*((hs.length+1).factorial:ℝ)*|Z|/(4*U)^(hs.length+2)
    ‖∑ j ∈ Finset.range N, ExponentialSum.phase
      (forwardDifference hs (fun y => a*y+Z*Real.log y) ((j:ℝ)+x))‖ ≤
      (6*(4:ℝ)^(hs.length+2)+15)*((N:ℝ)*Real.sqrt lam+1/Real.sqrt lam) := by
  let g : ℝ → ℝ := forwardDifference hs (fun y => a*y+Z*Real.log y)
  let lam : ℝ := hs.prod*((hs.length+1).factorial:ℝ)*|Z|/(4*U)^(hs.length+2)
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos (mul_pos (mul_pos (List.prod_pos hhs)
      (by exact_mod_cast Nat.factorial_pos _)) (abs_pos.mpr hZ)) (by positivity)
  have hg : ContDiffOn ℝ ∞ g (Ioi 0) :=
    forwardDifference_contDiffOn hs (fun h hh => (hhs h hh).le)
      (logarithmic_linear_phase_smooth a Z)
  have hg' : ContDiffOn ℝ ∞ (deriv g) (Ioi 0) :=
    hg.deriv_of_isOpen isOpen_Ioi (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hy0 (y : ℝ) (hy : y ∈ Icc x (x+N)) : 0 < y := hU.trans_le (hx.trans hy.1)
  have hf (y : ℝ) (hy : y ∈ Icc x (x+N)) : HasDerivAt g (deriv g y) y :=
    ((hg.contDiffAt (isOpen_Ioi.mem_nhds (hy0 y hy))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
  have hf' (y : ℝ) (hy : y ∈ Icc x (x+N)) :
      HasDerivAt (deriv g) (iteratedDeriv 2 g y) y := by
    simpa only [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_zero] using
      ((hg'.contDiffAt (isOpen_Ioi.mem_nhds (hy0 y hy))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
  have hb (y : ℝ) (hy : y ∈ Icc x (x+N)) :
      lam ≤ |iteratedDeriv 2 g y| ∧
      |iteratedDeriv 2 g y| ≤ (4:ℝ)^(hs.length+2)*lam := by
    have hh := logarithmic_linear_forwardDifference_second_bounds hs hhs a Z (V := 4*U) hU
      (hx.trans hy.1) (by linarith [hy.2])
    refine ⟨hh.1,hh.2.trans_eq ?_⟩
    dsimp [lam]
    rw [mul_pow]
    field_simp
  exact ExponentialSum.second_derivative_test g (deriv g) (iteratedDeriv 2 g)
    x N lam ((4:ℝ)^(hs.length+2)) hlam (by positivity) hf hf' hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace JointDickman

/-- Choose a bounded derivative order placing the logarithmic phase in the
second-derivative scale after differencing. -/
theorem logarithmic_phase_order {U Z B : ℝ} (hU : 1 < U) (_hB : 1/2 ≤ B)
    (hlower : U ^ (1/2:ℝ) ≤ |Z|) (hupper : |Z| ≤ U ^ B) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ Nat.ceil B + 1 ∧
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) ∧
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) := by
  have hU0 : 0 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hZ0 : 0 < |Z| := (Real.rpow_pos_of_pos hU0 (1/2:ℝ)).trans_le hlower
  let a : ℝ := Real.log |Z| / Real.log U
  have ha4 : 1/2 ≤ a := by
    apply (le_div_iff₀ hlogU).2
    have h := Real.log_le_log (Real.rpow_pos_of_pos hU0 (1/2:ℝ)) hlower
    simpa only [Real.log_rpow hU0] using h
  have haB : a ≤ B := by
    apply (div_le_iff₀ hlogU).2
    have h := Real.log_le_log hZ0 hupper
    rwa [Real.log_rpow hU0] at h
  let k : ℕ := Nat.floor (a + 1 / 2)
  have ha0 : 0 ≤ a + 1 / 2 := by linarith
  have hklo : (k : ℝ) ≤ a + 1 / 2 := Nat.floor_le ha0
  have hkhi : a + 1 / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk4 : 1 ≤ k := (Nat.le_floor_iff ha0).2 (by norm_num <;> linarith)
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
theorem logarithmic_shift_product {U : ℝ} (hU : 1 < U) {k : ℕ} (hk : 1 ≤ k)
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
theorem logarithmic_phase_shift_scale {U Z : ℝ} (hU : 1 < U) {k : ℕ} (hk : 1 ≤ k)
    (hlower : U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)))
    (hupper : |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2))
    (hs : List ℝ) (hlen : hs.length ≤ k)
    (hhs : ∀ h ∈ hs, 1 ≤ h ∧ h ≤ U ^ (1 / (10 * (k : ℝ)))) :
    U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ∧
    |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ≤ U ^ (-(2 : ℝ) / 5) := by
  have hU0 : 0 < U := by linarith
  obtain ⟨hplo, hphi⟩ := logarithmic_shift_product hU hk hs hlen hhs
  have hbase0 : 0 ≤ |Z| * U ^ (-((k : ℝ) + 1)) := by positivity
  constructor
  · exact hlower.trans (le_mul_of_one_le_right hbase0 hplo)
  · calc
      |Z| * U ^ (-((k : ℝ) + 1)) * hs.prod ≤
          U ^ (-(1 : ℝ) / 2) * U ^ ((1 : ℝ) / 10) :=
        mul_le_mul hupper hphi (by linarith) (by positivity)
      _ = U ^ (-(2 : ℝ) / 5) := by rw [← Real.rpow_add hU0]; norm_num

end JointDickman

end

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseTerminalBudget
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar bounds for logarithmic terminal sums

These two elementary real inequalities are reused from the frozen internal
reciprocal-phase proof, with their names changed to the present application.
-/
namespace JointDickman

theorem logarithmic_terminal_error_bound {U a b Λ : ℝ} (hU : 1 ≤ U)
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


theorem logarithmic_terminal_sqrt_budget {U a lam T : ℝ} (hU : 1 ≤ U)
    (ha : 0 < a) (hT : T ≤ 3 * U)
    (hlower : a * U ^ (-(3 : ℝ) / 2) ≤ lam)
    (hupper : lam ≤ a * U ^ (-(2 : ℝ) / 5)) :
    T * Real.sqrt lam + 1 / Real.sqrt lam ≤
      3 * (a ^ ((1 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) + 1) * U ^ ((4 : ℝ) / 5) := by
  have hlam : 0 < lam := (mul_pos ha (Real.rpow_pos_of_pos (by linarith) _)).trans_le hlower
  have h := logarithmic_terminal_error_bound hU ha ha.le hlower hupper
  have hinv : lam ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt lam := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hlam.le, ← Real.sqrt_eq_rpow, one_div]
  rw [← Real.sqrt_eq_rpow, hinv] at h
  have hs := mul_le_mul_of_nonneg_right hT (Real.sqrt_nonneg lam)
  have hi : 0 ≤ 1 / Real.sqrt lam := by positivity
  nlinarith


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseTerminal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform terminal cancellation for logarithmic phases -/
namespace JointDickman
open Problem337

lemma logarithmic_terminal_scale_eq (hs : List ℝ) {k : ℕ}
    (hlen : hs.length+1=k) {U : ℝ} (hU : 0 < U) (Z : ℝ) :
    hs.prod*((hs.length+1).factorial:ℝ)*|Z|/(4*U)^(hs.length+2) =
      ((k.factorial:ℝ)/(4:ℝ)^(k+1))*(|Z| *U^(-((k:ℝ)+1))*hs.prod) := by
  have hpow : U^(-((k:ℝ)+1)) = (U^(k+1))⁻¹ := by
    rw [Real.rpow_neg hU.le]
    congr 1
    norm_cast
  rw [hlen,show hs.length+2=k+1 by omega,mul_pow,hpow]
  ring

/-- The last differenced sums have a fixed power saving. The hypotheses are
only scalar size relations for the actual logarithmic phase. -/
theorem logarithmic_terminal_range_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U Z x : ℝ) (N : ℕ) (hs : List ℝ),
      2 ≤ U → hs.length+1=k →
      (∀ h ∈ hs, 1 ≤ h ∧ h ≤ U^(1/(10*(k:ℝ)))) →
      U^(-(3:ℝ)/2) ≤ |Z| *U^(-((k:ℝ)+1)) →
      |Z| *U^(-((k:ℝ)+1)) ≤ U^(-(1:ℝ)/2) →
      U ≤ x → x+(N:ℝ)+hs.sum ≤ 4*U → (N:ℝ) ≤ 3*U →
      ‖∑ j ∈ Finset.range N, ExponentialSum.phase
        (forwardDifference hs (fun y => a*y+Z*Real.log y) ((j:ℝ)+x))‖ ≤
        C*U^((4:ℝ)/5) := by
  let c : ℝ := (k.factorial:ℝ)/(4:ℝ)^(k+1)
  let A : ℝ := (4:ℝ)^(k+1)
  have hc : 0 < c := by dsimp [c] <;> positivity
  refine ⟨(6*A+15)*(3*(c^((1:ℝ)/2)+c^(-(1:ℝ)/2)+1)),by positivity,?_⟩
  intro a U Z x N hs hU hlen hhs hlo hhi hx hend hN
  have hU0 : 0 < U := by linarith
  have hpos : ∀ h ∈ hs, 0 < h := fun h hh => by linarith [(hhs h hh).1]
  have hZ : Z ≠ 0 := by
    intro h
    rw [h,abs_zero,zero_mul] at hlo
    exact (not_le_of_gt (Real.rpow_pos_of_pos hU0 _)) hlo
  have hraw := logarithmic_difference_sum_bound hs hpos a Z U x N hZ hU0 hx hend
  dsimp only at hraw
  rw [logarithmic_terminal_scale_eq hs hlen hU0 Z,
    show hs.length+2=k+1 by omega] at hraw
  obtain ⟨hlow,hhigh⟩ := logarithmic_phase_shift_scale (by linarith : 1<U) hk
    hlo hhi hs (by omega) hhs
  have hb := logarithmic_terminal_sqrt_budget (by linarith : 1≤U) hc hN
    (mul_le_mul_of_nonneg_left hlow hc.le)
    (mul_le_mul_of_nonneg_left hhigh hc.le)
  apply hraw.trans
  change (6*A+15)*_ ≤ _
  calc
    _ ≤ (6*A+15)*(3*(c^((1:ℝ)/2)+c^(-(1:ℝ)/2)+1)*U^((4:ℝ)/5)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem logarithmic_terminal_interval_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a U Z : ℝ) (L R : ℤ) (hs : List ℤ),
      2 ≤ U → hs.length = k - 1 →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℤ)) →
      U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
      |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
      U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ‖∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => a*y+Z*Real.log y) n)‖ ≤ C * U ^ ((4 : ℝ) / 5) := by
  obtain ⟨C, hC, hbound⟩ := logarithmic_terminal_range_bound k hk
  refine ⟨C, hC, ?_⟩
  intro a U Z L R hs hU hlen hhs hlo hhi hL hR
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
  have hh := hbound a U Z L N (hs.map (fun h : ℤ => (h : ℝ))) hU
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
          (fun y => a*y+Z*Real.log y) n)) =
      ∑ j ∈ Finset.range N,
        ExponentialSum.phase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun y => a*y+Z*Real.log y) ((j : ℝ) + L)) := by
    rw [Int.Icc_eq_finset_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast]
    rw [add_comm]
    rfl
  rwa [heq]


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LogPhaseUniform
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform cancellation for logarithmic exponential sums

Only finitely many derivative orders are required when the frequency is
bounded by a fixed power of the length scale.
-/
namespace JointDickman
open Filter Problem337
open scoped Topology

/-- A fixed power range of frequencies admits a positive power saving,
uniformly in an additional linear phase and in the interval endpoints. -/
theorem logarithmic_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (a Z : ℝ) (L R : ℤ),
        U^(1/2:ℝ) ≤ |Z| → |Z| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Finset.Icc L R, differencingPhase (a*n+Z*Real.log n)‖ ≤
          A*U^(1-δ) := by
  let F : ℕ → ℝ → (ℝ × ℝ × ℤ × ℤ) → ℝ := fun _ _ z =>
    ‖∑ n ∈ Finset.Icc z.2.2.1 z.2.2.2,
      differencingPhase (z.1*n+z.2.1*Real.log n)‖
  let P : ℕ → ℝ → (ℝ × ℝ × ℤ × ℤ) → Prop := fun k U z =>
    U^(-(3:ℝ)/2) ≤ |z.2.1| *U^(-((k:ℝ)+1)) ∧
    |z.2.1| *U^(-((k:ℝ)+1)) ≤ U^(-(1:ℝ)/2) ∧
    U ≤ (z.2.2.1:ℝ) ∧ (z.2.2.2:ℝ) ≤ 2*U
  have horders : ∀ k ∈ Finset.Icc 1 (Nat.ceil B+1),
      ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ,
        ∀ U : ℝ, T ≤ U → ∀ z : ℝ × ℝ × ℤ × ℤ,
          P k U z → F k U z ≤ A*U^(1-δ) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
    have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk1
    let α : ℝ := 1/(10*(k:ℝ))
    have hα : 0 < α := by dsimp [α] <;> positivity
    have hαsmall : α < (1:ℝ)/5 := by
      dsimp [α]
      apply (div_lt_iff₀ (by positivity : (0:ℝ)<10*k)).mpr
      nlinarith
    obtain ⟨C,hC,hterminal⟩ := logarithmic_terminal_interval_bound k hk1
    have hb := logarithmic_interval_budget_eventually (k-1) α C hα hαsmall hC
    obtain ⟨T,hT⟩ := eventually_atTop.mp ((eventually_ge_atTop (2:ℝ)).and hb)
    refine ⟨36,α/(2:ℝ)^(k-1),by norm_num,by positivity,T,?_⟩
    intro U hU z hz
    obtain ⟨hU2,hbudget⟩ := hT U hU
    apply hbudget z.2.2.1 z.2.2.2 hz.2.2.1 hz.2.2.2
      (fun y => z.1*y+z.2.1*Real.log y)
    intro hs hlen hsteps
    exact hterminal z.1 U z.2.1 z.2.2.1 z.2.2.2 hs hU2 hlen hsteps
      hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  obtain ⟨A,δ,hA,hδ,T,_,hbound⟩ :=
    finite_uniform_rpow_saving (Finset.Icc 1 (Nat.ceil B+1)) F P 1 horders
  refine ⟨A,δ,hA,hδ,?_⟩
  filter_upwards [eventually_ge_atTop T,eventually_gt_atTop (1:ℝ)] with U hU hU1
  intro a Z L R hlo hhi hL hR
  obtain ⟨k,hk,hkB,hkl,hku⟩ := logarithmic_phase_order hU1 hB hlo hhi
  exact hbound k (Finset.mem_Icc.mpr ⟨hk,hkB⟩) U hU (a,Z,L,R) ⟨hkl,hku,hL,hR⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterLogPhase
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Character twists of logarithmic exponential sums -/
namespace JointDickman
open Complex Filter Problem337
open scoped Topology

lemma imaginary_power_as_log_phase (t : ℝ) {n : ℤ} (hn : 0 < n) :
    (n:ℂ)^(-((t:ℂ)*I)) =
      differencingPhase ((-t/(2*Real.pi))*Real.log (n:ℝ)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hnC]
  rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp,←Complex.ofReal_log hn0.le]
  unfold differencingPhase
  congr 1
  push_cast
  field_simp

/-- A character contributes at most the finite Fourier expansion factor q.
The power saving is uniform in the character. -/
theorem character_log_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (t : ℝ) (L R : ℤ),
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Finset.Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))‖ ≤
          (q:ℝ)*A*U^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hbound⟩ := logarithmic_phase_uniform B hB
  refine ⟨A,δ,hA,hδ,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with U hbound hU
  intro q _ χ t L R hlo hhi hL hR
  have he : (∑ n ∈ Finset.Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))) =
      ∑ n ∈ Finset.Icc L R, χ (n:ZMod q)*
        differencingPhase ((-t/(2*Real.pi))*Real.log (n:ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hLn : (L:ℝ) ≤ (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : (0:ℝ) < n := hU.trans_le (hL.trans hLn)
    rw [imaginary_power_as_log_phase t (by exact_mod_cast hn0)]
  rw [he]
  have hh := character_log_sum_bound χ (Finset.Icc L R) (-t/(2*Real.pi))
    (A*U^(1-δ)) (by positivity) (fun a => hbound a (-t/(2*Real.pi)) L R
      (by simpa only [neg_div,abs_neg] using hlo)
      (by simpa only [neg_div,abs_neg] using hhi) hL hR)
  simpa only [mul_assoc] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterDyadicSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted character sums on a dyadic interval -/
namespace JointDickman
open Complex Filter Finset
open scoped Topology

lemma character_cpow_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) {n : ℤ} (hn : 0 < n) :
    χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)) =
      (((n:ℝ)^(-σ):ℝ):ℂ)*(χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rw [show -((σ:ℂ)+(t:ℂ)*I) = ((-σ:ℝ):ℂ)+(-((t:ℂ)*I)) by push_cast; ring]
  rw [cpow_add _ _ (by exact_mod_cast (ne_of_gt hn))]
  rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp, ←ofReal_cpow hnR.le]
  ring

lemma rpow_weight_dyadic_bound {U L σ δ D : ℝ}
    (hU : 1 ≤ U) (hUL : U ≤ L) (hσ : 1 ≤ σ) (hD : 0 ≤ D) :
    D*U^(1-δ)*L^(-σ) ≤ D*U^(-δ) := by
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (hU.trans hUL)
  have hw : L^(-σ) ≤ U^(-1:ℝ) := by
    exact (Real.rpow_le_rpow_of_exponent_le (hU.trans hUL) (by linarith)).trans
      (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hU) hUL (by norm_num))
  calc
    _ ≤ D*U^(1-δ)*U^(-1:ℝ) := mul_le_mul_of_nonneg_left hw (by positivity)
    _ = D*U^(-δ) := by rw [mul_assoc, ←Real.rpow_add (by linarith)]; congr 2; ring

/-- The logarithmic phase estimate survives the full Dirichlet-series weight,
with a decaying bound for each dyadic interval. -/
theorem character_dyadic_sum_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (σ t : ℝ) (L R : ℤ), 1 ≤ σ →
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤
          (q:ℝ)*A*U^(-δ) := by
  obtain ⟨A,δ,hA,hδ,hh⟩ := character_log_phase_uniform B hB
  refine ⟨A,δ,hA,hδ,?_⟩
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with U hh hU
  intro q _ χ σ t L R hσ hlo hhi hL hR
  have hL0 : 0 < L := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hU.trans hL))
  have he : (∑ n ∈ Icc L R, χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))) =
      ∑ n ∈ Icc L R, (((n:ℝ)^(-σ):ℝ):ℂ)*
        (χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))) := by
    apply sum_congr rfl
    intro n hn
    exact character_cpow_split χ σ t (hL0.trans_le (mem_Icc.mp hn).1)
  rw [he]
  have hb := rpow_weighted_sum_Icc_bound
    (fun n => χ (n:ZMod q)*(n:ℂ)^(-((t:ℂ)*I))) L R hL0
    (D := (q:ℝ)*A*U^(1-δ)) (by positivity) (by linarith : 0 ≤ σ)
    (fun V _ hV => hh q χ t L V hlo hhi hL ((by exact_mod_cast hV : (V:ℝ) ≤ R).trans hR))
  exact hb.trans (rpow_weight_dyadic_bound hU hL hσ (by positivity))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.PrimeGaps_DirichletGrowth
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

lemma discrepancyTail_integrable {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (hD : 0 ≤ D)
    (hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t => A t * (t:ℂ)^(-(s+1))) (Ioi u) := by
  have hp : (-(s+1)).re < -1 := by simp only [neg_re,add_re,one_re] <;> linarith
  have hi := (integrableOn_Ioi_norm_cpow_of_lt hp hu).const_mul D
  have hm := (integrableOn_Ioi_cpow_of_lt hp hu).aestronglyMeasurable
  refine hi.mono (hA.aestronglyMeasurable.restrict.mul hm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)

lemma discrepancyTail_norm_le {A : ℝ → ℂ} {u D : ℝ} (hu : 0 < u) (_hD : 0 ≤ D)
    (_hA : Measurable A) (hbound : ∀ t, u < t → ‖A t‖ ≤ D) {s : ℂ} (hs : 0 < s.re) :
    ‖discrepancyTail A u s‖ ≤ D * u^(-s.re)/s.re := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu).const_mul D
  calc
    _ ≤ ∫ t in Ioi u, D*t^(-s.re-1) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hu.trans ht)]
      simp only [neg_re,add_re,one_re,neg_add_rev]
      have he : -1 + -s.re = -s.re-1 := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (hbound t ht) (Real.rpow_nonneg (hu.trans ht).le _)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : -s.re-1 < -1) hu]
      ring_nf

open Finset

lemma measurable_seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) :
    Measurable (seriesDiscrepancy f c) := by
  exact ((measurable_of_countable (fun N : ℕ => ∑ n ∈ Icc 1 N, f n)).comp
    Nat.measurable_floor).sub (measurable_const.mul Complex.continuous_ofReal.measurable)

lemma regularSeries_eq_LSeries_sub {f : ℕ → ℂ} {c : ℂ} {D : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D) {s : ℂ} (hs : 1 < s.re) :
    regularSeries f c s = LSeries f s - c/(s-1) := by
  have hO : (fun n => ∑ k ∈ Icc 1 n, ‖f k‖) =O[atTop] (fun n => (n:ℝ)^(1:ℝ)) := by
    refine isBigO_iff.mpr ⟨1, .of_forall (fun n => ?_)⟩
    simp only [Real.rpow_one, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))]
    calc
      _ ≤ ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_le_sum (fun n _ => hf n)
      _ ≤ |(n:ℝ)| := by simp
  rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
  have hiA := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb
    (zero_lt_one.trans hs)
  have hi := integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one
  have he (t : ℝ) (ht : 1 < t) :
      (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t:ℂ)^(-(s+1)) =
      seriesDiscrepancy f c t * (t:ℂ)^(-(s+1)) + c*(t:ℂ)^(-s) := by
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    have ht1 : (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
      nth_rw 1 [←Complex.cpow_one (t:ℂ)]
      rw [←Complex.cpow_add _ _ ht0]
      congr 1
      ring
    dsimp [seriesDiscrepancy]
    rw [sub_mul, mul_assoc c, ht1]
    ring
  have hs0 : s-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this <;> linarith
  have hv : ∫ t in Ioi (1:ℝ), (t:ℂ)^(-s) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs : (-s).re < -1) zero_lt_one]
    simp only [ofReal_one, one_cpow]
    have he : -s+1 = -(s-1) := by ring
    rw [he, neg_div_neg_eq]
  rw [setIntegral_congr_fun measurableSet_Ioi he,
    integral_add hiA (hi.const_mul c), integral_const_mul, hv]
  dsimp [regularSeries,discrepancyTail]
  field_simp [hs0]
  ring

lemma sum_Icc_zero_eq {f : ℕ → ℂ} (hf : f 0 = 0) (N : ℕ) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  rw [←Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le N)]
  simp [hf]

lemma weighted_sum_abel {f : ℕ → ℂ} (hf : f 0 = 0) {N : ℕ} (hN : 1 ≤ N)
    {s : ℂ} (hs : 0 < s.re) :
    ∑ n ∈ Icc 1 N, f n * (n:ℂ)^(-s) =
      (∑ n ∈ Icc 1 N, f n)*(N:ℂ)^(-s) +
        s*∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1)) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hd (t:ℝ) (ht : t ∈ Set.Icc 1 (N:ℝ)) :
      HasDerivAt (fun t : ℝ => (t:ℂ)^(-s)) ((-s)*(t:ℂ)^(-(s+1))) t := by
    rw [show -(s+1) = -s-1 by ring]
    exact hasDerivAt_ofReal_cpow_const ((zero_lt_one.trans_le ht.1).ne') (neg_ne_zero.mpr hs0)
  have hcont : ContinuousOn (fun t : ℝ => (-s)*(t:ℂ)^(-(s+1))) (Set.Icc 1 (N:ℝ)) := by
    intro t ht
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (.inr (zero_lt_one.trans_le ht.1).ne'))).continuousWithinAt
  have hi : IntegrableOn (deriv (fun t:ℝ => (t:ℂ)^(-s))) (Set.Icc 1 (N:ℝ)) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul' f hN (fun t ht => (hd t (by simpa using ht)).differentiableAt) (by simpa using hi)
  have he : (insert 1 (Finset.Ioc 1 N) : Finset ℕ) = Finset.Icc 1 N := by
    ext k
    simp only [Finset.mem_insert,Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hint : (∫ t in Set.Ioc (1:ℝ) (N:ℝ),
      deriv (fun t:ℝ => (t:ℂ)^(-s)) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k) =
      (-s)*∫ t in (1:ℝ)..N, (∑ k ∈ Icc 1 ⌊t⌋₊, f k)*(t:ℂ)^(-(s+1)) := by
    rw [intervalIntegral.integral_of_le hNR, ←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hd t ⟨ht.1.le,ht.2⟩).deriv,sum_Icc_zero_eq hf]
    ring
  simp only [Nat.cast_one, Complex.ofReal_natCast, Complex.ofReal_one] at ha
  rw [hint] at ha
  simp only [one_cpow,one_mul,sum_Icc_zero_eq hf,Finset.Icc_self,sum_singleton] at ha
  conv_lhs => rw [←he,sum_insert (by simp)]
  simp only [Nat.cast_one,one_cpow,mul_one]
  simp_rw [mul_comm (f _) ((_:ℂ)^(-s))]
  rw [ha]
  ring

lemma cpow_sub_eq_mul_intervalIntegral {N : ℝ} (hN : 1 ≤ N) (s : ℂ) :
    (N:ℂ)^(1-s)-1 = (1-s)*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  by_cases hs : s = 1
  · subst s
    simp
  · have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
    rw [integral_cpow (.inr ⟨by simpa using hs,hn⟩)]
    simp only [Complex.ofReal_one,one_cpow]
    have he : -s+1 = 1-s := by ring
    rw [he]
    field_simp

lemma regularSeries_cutoff {f : ℕ → ℂ} {c : ℂ} {D : ℝ} (hf : f 0 = 0)
    (hD : 0 ≤ D) (hb : ∀ t, 1 < t → ‖seriesDiscrepancy f c t‖ ≤ D)
    {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    regularSeries f c s = (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) -
      seriesDiscrepancy f c N * (N:ℂ)^(-s) +
      s*discrepancyTail (seriesDiscrepancy f c) N s -
      c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (N:ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN).ne'
  have hi := discrepancyTail_integrable zero_lt_one hD (measurable_seriesDiscrepancy f c) hb hs
  have htail := intervalIntegral.integral_Ioi_sub_Ioi hi hNR
  have hp : ∀ t ∈ Set.Icc (1:ℝ) (N:ℝ),
      (t:ℂ)*(t:ℂ)^(-(s+1)) = (t:ℂ)^(-s) := by
    intro t ht
    have ht0 : (t:ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le ht.1).ne'
    nth_rw 1 [←Complex.cpow_one (t:ℂ)]
    rw [←Complex.cpow_add _ _ ht0]
    congr 1
    ring
  have hip : IntervalIntegrable (fun t:ℝ => (t:ℂ)^(-s)) volume 1 N :=
    intervalIntegral.intervalIntegrable_cpow (.inr (by rw [Set.uIcc_of_le hNR]; simp))
  have hiA : IntervalIntegrable (fun t:ℝ => seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) volume 1 N :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hNR).mpr (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hint : (∫ t in (1:ℝ)..N, (∑ n ∈ Icc 1 ⌊t⌋₊, f n)*(t:ℂ)^(-(s+1))) =
      (∫ t in (1:ℝ)..N, seriesDiscrepancy f c t*(t:ℂ)^(-(s+1))) +
        c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s) := by
    rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_add hiA (hip.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNR] at ht
    dsimp [seriesDiscrepancy]
    rw [sub_mul,mul_assoc c,hp t ht]
    ring
  have hab := weighted_sum_abel hf hN hs
  rw [hint, ←htail] at hab
  have hpow : (N:ℂ)*(N:ℂ)^(-s) = (N:ℂ)^(1-s) := by
    nth_rw 1 [←Complex.cpow_one (N:ℂ)]
    rw [←Complex.cpow_add _ _ hn0]
    congr 1
  have hc := cpow_sub_eq_mul_intervalIntegral hNR s
  simp only [Complex.ofReal_natCast] at hc
  dsimp [regularSeries,discrepancyTail]
  rw [hab]
  simp only [seriesDiscrepancy,Nat.floor_natCast,Complex.ofReal_natCast]
  rw [sub_mul,mul_assoc c,hpow,sub_eq_iff_eq_add.mp hc]
  ring

lemma sum_cpow_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    {s : ℂ} (hs : 1-ε ≤ s.re) {N : ℕ} (_hN : 1 ≤ N) :
    ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ ≤
      (∑' n : ℕ, (n:ℝ)^(-1-ε)) * (N:ℝ)^(2*ε) := by
  have hsumm : Summable (fun n : ℕ => (n:ℝ)^(-1-ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε)*(N:ℝ)^(2*ε) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 := zero_lt_one.trans_le hn1
      rw [norm_mul]
      have hn0C : (n:ℂ) = ((n:ℝ):ℂ) := by simp
      rw [hn0C,Complex.norm_cpow_eq_rpow_re_of_pos hn0,Complex.neg_re]
      calc
        _ ≤ (n:ℝ)^(-s.re) := by
          simpa using mul_le_mul_of_nonneg_right (hf n) (Real.rpow_nonneg hn0.le (-s.re))
        _ ≤ (n:ℝ)^(-1+ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = (n:ℝ)^(-1-ε)*(n:ℝ)^(2*ε) := by rw [←Real.rpow_add hn0]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnN (by positivity))
          (Real.rpow_nonneg hn0.le _)
    _ = (∑ n ∈ Icc 1 N, (n:ℝ)^(-1-ε))*(N:ℝ)^(2*ε) := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hsumm.sum_le_tsum _ (fun n _ => Real.rpow_nonneg n.cast_nonneg _))
      (Real.rpow_nonneg N.cast_nonneg _)

lemma norm_intervalIntegral_cpow_le {ε N : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    {s : ℂ} (hs : 1-ε ≤ s.re) :
    ‖∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ N^ε/ε := by
  have hn : (0:ℝ) ∉ Set.uIcc 1 N := by rw [Set.uIcc_of_le hN]; simp
  calc
    _ ≤ ∫ t in (1:ℝ)..N, t^(-1+ε) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hN
        (.of_forall (fun t ht => ?_)) (intervalIntegral.intervalIntegrable_rpow (.inr hn))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht.1),Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le ht.1.le (by linarith)
    _ = (N^ε-1)/ε := by
      rw [integral_rpow (.inl (by linarith : -1 < -1+ε))]
      have he : -1+ε+1 = ε := by ring
      simp [he]
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hε.le

lemma regularSeries_norm_cutoff {f : ℕ → ℂ} {c : ℂ} {D ε : ℝ}
    (hf0 : f 0 = 0) (hf : ∀ n, ‖f n‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : 0 ≤ D)
    (hb : ∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D)
    (hε : 0 < ε) (hε1 : ε ≤ 1/2) {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : 1-ε ≤ s.re) (hNs : D*(1+‖s‖) ≤ N) :
    ‖regularSeries f c s‖ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε)*(N:ℝ)^(2*ε) := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNP := zero_lt_one.trans_le hNR
  have hs0 : 0 < s.re := by linarith
  have hhalf : 1/2 ≤ s.re := by linarith
  have htail := discrepancyTail_norm_le hNP hD (measurable_seriesDiscrepancy f c)
    (fun t ht => hb t (hNR.trans ht.le)) hs0
  have hboundary : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ ≤ D*(N:ℝ)^(-s.re) := by
    rw [norm_mul, ←Complex.ofReal_natCast N, Complex.norm_cpow_eq_rpow_re_of_pos hNP,Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hb _ hNR) (Real.rpow_nonneg hNP.le _)
  have hsmall : ‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
      ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖ ≤ 2*(N:ℝ)^ε := by
    have ht : D*(N:ℝ)^(-s.re)/s.re ≤ 2*D*(N:ℝ)^(-s.re) := by
      apply (div_le_iff₀ hs0).mpr
      have hn := Real.rpow_nonneg hNP.le (-s.re)
      nlinarith [mul_nonneg hD hn,mul_nonneg (mul_nonneg hD hn) (sub_nonneg.mpr hhalf)]
    have he : (N:ℝ)*(N:ℝ)^(-s.re) ≤ (N:ℝ)^ε := by
      nth_rw 1 [←Real.rpow_one (N:ℝ)]
      rw [←Real.rpow_add hNP]
      apply Real.rpow_le_rpow_of_exponent_le hNR
      linarith
    calc
      _ ≤ D*(N:ℝ)^(-s.re) + ‖s‖*(2*D*(N:ℝ)^(-s.re)) := by
        nth_rw 2 [norm_mul]
        exact add_le_add hboundary (mul_le_mul_of_nonneg_left (htail.trans ht) (norm_nonneg s))
      _ ≤ 2*(N:ℝ)*(N:ℝ)^(-s.re) := by
        have hcoeff : D+2*‖s‖*D ≤ 2*(N:ℝ) := by nlinarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) (Real.rpow_nonneg hNP.le (-s.re))]
      _ ≤ _ := by nlinarith [he]
  have hi : ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ ≤ (N:ℝ)^ε/ε := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by
      simpa using norm_intervalIntegral_cpow_le hε hNR hs)
  have hp : (N:ℝ)^ε ≤ (N:ℝ)^(2*ε) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  rw [regularSeries_cutoff hf0 hD (fun t ht => hb t ht.le) hN hs0]
  calc
    _ ≤ ‖∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)‖ +
        (‖seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
        ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
        ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := by
      calc
        _ ≤ ‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s) +
             s*discrepancyTail (seriesDiscrepancy f c) N s‖ +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := norm_sub_le _ _
        _ ≤ (‖(∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) - seriesDiscrepancy f c N * (N:ℂ)^(-s)‖ +
             ‖s*discrepancyTail (seriesDiscrepancy f c) N s‖) +
             ‖c*∫ t in (1:ℝ)..N, (t:ℂ)^(-s)‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have htri := norm_sub_le (∑ n ∈ Icc 1 N, f n*(n:ℂ)^(-s)) (seriesDiscrepancy f c N * (N:ℂ)^(-s))
          linarith
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^ε+(N:ℝ)^ε/ε := add_le_add (add_le_add (sum_cpow_norm_le hf hε hs hN) hsmall) hi
    _ ≤ ((∑' n : ℕ, (n:ℝ)^(-1-ε)))*(N:ℝ)^(2*ε) +
      2*(N:ℝ)^(2*ε)+(N:ℝ)^(2*ε)/ε := by
        linarith [div_le_div_of_nonneg_right hp hε.le]
    _ = _ := by ring

lemma regularSeries_norm_small_power {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℂ) (c : ℂ) (D : ℝ),
      f 0 = 0 → (∀ n, ‖f n‖ ≤ 1) → ‖c‖ ≤ 1 → 0 ≤ D →
      (∀ t, 1 ≤ t → ‖seriesDiscrepancy f c t‖ ≤ D) →
      ∀ s : ℂ, 1-ε ≤ s.re →
      ‖regularSeries f c s‖ ≤ K*((D+1)*(‖s‖+2))^(2*ε) := by
  let K₀ := (∑' n : ℕ, (n:ℝ)^(-1-ε))+2+1/ε
  have hK₀ : 0 < K₀ := by
    have ht : 0 ≤ ∑' n : ℕ, (n:ℝ)^(-1-ε) := tsum_nonneg (fun n => Real.rpow_nonneg n.cast_nonneg _)
    dsimp [K₀]
    positivity
  refine ⟨K₀*2^(2*ε), by positivity, ?_⟩
  intro f c D hf0 hf hc hD hb s hs
  let B := (D+1)*(‖s‖+2)
  have hB : 1 ≤ B := by dsimp [B] <;> nlinarith [norm_nonneg s]
  let N := ⌈B⌉₊
  have hBN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hN : 1 ≤ N := by exact_mod_cast (hB.trans hBN)
  have hN2 : (N:ℝ) ≤ 2*B := by
    have := Nat.ceil_lt_add_one (zero_lt_one.trans_le hB).le
    change (N:ℝ) < B+1 at this
    linarith
  have hcut := regularSeries_norm_cutoff hf0 hf hc hD hb hε hε1 hN hs
    (show D*(1+‖s‖) ≤ (N:ℝ) from (by dsimp [B] at hBN <;> nlinarith [norm_nonneg s]))
  calc
    _ ≤ K₀*(N:ℝ)^(2*ε) := hcut
    _ ≤ K₀*(2*B)^(2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow N.cast_nonneg hN2 (by positivity)) hK₀.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ B)]; ring

lemma positiveCoefficients_zero (f : ℕ → ℂ) : positiveCoefficients f 0 = 0 := by simp [positiveCoefficients]

lemma positiveCoefficients_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖positiveCoefficients f n‖ ≤ 1 := by
  by_cases hn : n=0 <;> simp [positiveCoefficients,hn,hf]

lemma sum_positiveCoefficients (f : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, positiveCoefficients f n = ∑ n ∈ Icc 1 N, f n := by
  apply sum_congr rfl
  intro n hn
  simp [positiveCoefficients,show n ≠ 0 from Nat.ne_of_gt (mem_Icc.mp hn).1]

lemma LSeries_positiveCoefficients (f : ℕ → ℂ) (s : ℂ) :
    LSeries (positiveCoefficients f) s = LSeries f s := by
  apply LSeries_congr
  intro n hn
  simp [positiveCoefficients,hn]

lemma discrepancy_constant_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1 t‖ ≤ 1 := by
  simp only [seriesDiscrepancy,sum_positiveCoefficients,Finset.sum_const,nsmul_eq_mul,
    mul_one,Nat.card_Icc,Nat.add_sub_cancel,one_mul]
  rw [←Complex.ofReal_natCast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have ht0 := (show (0:ℝ) ≤ t by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le ht0))]
  have := Nat.lt_floor_add_one t
  linarith

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_DyadicDirichletSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the decaying Dirichlet bounds over dyadic intervals -/
namespace JointDickman
open Finset

lemma sum_int_Ioc_consecutive (f : ℤ → ℂ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ n ∈ Ioc a b, f n)+(∑ n ∈ Ioc b c, f n) = ∑ n ∈ Ioc a c, f n := by
  rw [←Ioc_union_Ioc_eq_Ioc hab hbc, sum_union]
  apply disjoint_left.mpr
  intro n hn hn'
  have := mem_Ioc.mp hn
  have := mem_Ioc.mp hn'
  omega

lemma norm_dyadic_sum_bound (f : ℤ → ℂ) {N : ℤ} (hN : 0 < N)
    {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ) (K : ℕ)
    (hblock : ∀ j < K,
      ‖∑ n ∈ Ioc ((2:ℤ)^j*N) ((2:ℤ)^(j+1)*N), f n‖ ≤
        D*(((2:ℝ)^j*(N:ℝ))^(-δ))) :
    ‖∑ n ∈ Ioc N ((2:ℤ)^K*N), f n‖ ≤ D*(N:ℝ)^(-δ)/(1-(2:ℝ)^(-δ)) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  let r : ℝ := (2:ℝ)^(-δ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have he (j : ℕ) : ((2:ℝ)^j*(N:ℝ))^(-δ) = (N:ℝ)^(-δ)*r^j := by
    rw [Real.mul_rpow (by positivity) hN'.le, Real.rpow_pow_comm (by norm_num)]
    exact mul_comm _ _
  have hb (J : ℕ) (hJK : J ≤ K) :
      ‖∑ n ∈ Ioc N ((2:ℤ)^J*N), f n‖ ≤ D*(N:ℝ)^(-δ)*(∑ j ∈ range J, r^j) := by
    induction J with
    | zero => simp
    | succ J ih =>
      have hpow : N ≤ (2:ℤ)^J*N := by nlinarith [one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2) (n := J)]
      have hnext : (2:ℤ)^J*N ≤ (2:ℤ)^(J+1)*N := by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0:ℤ) < 2) J]
      rw [←sum_int_Ioc_consecutive f hpow hnext]
      calc
        _ ≤ ‖∑ n ∈ Ioc N ((2:ℤ)^J*N), f n‖ + ‖∑ n ∈ Ioc ((2:ℤ)^J*N) ((2:ℤ)^(J+1)*N), f n‖ := norm_add_le _ _
        _ ≤ D*(N:ℝ)^(-δ)*(∑ j ∈ range J, r^j) + D*(((2:ℝ)^J*(N:ℝ))^(-δ)) :=
          add_le_add (ih (by omega)) (hblock J (by omega))
        _ = _ := by rw [he, sum_range_succ]; ring
  have hgeom : (∑ j ∈ range K, r^j) ≤ 1/(1-r) := by
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    have hh := geom_sum_mul r K
    nlinarith [pow_nonneg hr0 K]
  calc
    _ ≤ D*(N:ℝ)^(-δ)*(∑ j ∈ range K, r^j) := hb K le_rfl
    _ ≤ D*(N:ℝ)^(-δ)*(1/(1-r)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by dsimp [r] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterLFunctionCutoff
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded remainder after truncating a nonprincipal Dirichlet L-series -/
namespace JointDickman
open Complex Finset LargePrimeGaps

lemma sum_nat_Icc_int_cast {E : Type*} [AddCommMonoid E] (f : ℤ → E) (a b : ℕ) :
    (∑ n ∈ Icc a b, f (n:ℤ)) = ∑ n ∈ Icc (a:ℤ) (b:ℤ), f n := by
  apply sum_bij (fun (n : ℕ) _ => (n:ℤ))
  · intro n hn
    exact mem_Icc.mpr ⟨by exact_mod_cast (mem_Icc.mp hn).1,
      by exact_mod_cast (mem_Icc.mp hn).2⟩
  · intro n _ m _ h
    exact_mod_cast h
  · intro m hm
    have hm0 : 0 ≤ m := (Nat.cast_nonneg a).trans (mem_Icc.mp hm).1
    refine ⟨m.toNat, mem_Icc.mpr ⟨?_,?_⟩, Int.toNat_of_nonneg hm0⟩
    · exact_mod_cast (show (a:ℤ) ≤ (m.toNat:ℤ) by simpa [Int.toNat_of_nonneg hm0] using (mem_Icc.mp hm).1)
    · exact_mod_cast (show (m.toNat:ℤ) ≤ (b:ℤ) by simpa [Int.toNat_of_nonneg hm0] using (mem_Icc.mp hm).2)
  · intro n hn
    rfl

lemma character_LFunction_head_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 ≤ s.re) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ (n:ZMod q)*(n:ℂ)^(-s)‖ ≤ 1+Real.log N := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖χ (n:ZMod q)*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [norm_mul, show (n:ℂ) = ((n:ℝ):ℂ) by simp,
        norm_cpow_eq_rpow_re_of_pos (by linarith), neg_re]
      exact (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans
        (by simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hn1 (show -s.re ≤ -1 by linarith))
    _ = (harmonic N:ℝ) := by simp [harmonic_eq_sum_Icc]
    _ ≤ _ := harmonic_le_one_add_log N

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterFrequencyScales
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Truncation scales for logarithmic character estimates -/
namespace JointDickman
open Filter
open scoped Topology

theorem character_frequency_scales {B : ℝ} (hB : 2 ≤ B) (U₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∃ N K : ℕ,
      1 ≤ N ∧ U₀ ≤ (N:ℝ) ∧ (N:ℝ) ≤ T ∧
      Real.log N ≤ Real.log 2 + (1/B)*Real.log T ∧
      T ≤ (2:ℝ)^K*(N:ℝ) ∧ (2:ℝ)^K*(N:ℝ) ≤ 2*T ∧
      ((2:ℝ)^K*(N:ℝ))^(1/2:ℝ) ≤ T/(2*Real.pi) ∧
      T/(2*Real.pi) ≤ (N:ℝ)^B := by
  have hB0 : 0 < B := by linarith
  have hε : 0 < 1/B := one_div_pos.mpr hB0
  have hε1 : 1/B < 1 := (div_lt_one hB0).mpr (by linarith)
  have hpower := (tendsto_rpow_atTop hε).eventually_ge_atTop U₀
  have hgap := (tendsto_rpow_atTop (show 0 < 1-1/B by linarith)).eventually_ge_atTop 2
  filter_upwards [hpower,hgap,eventually_ge_atTop (max 1 (8*Real.pi^2))] with T hp hg hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hx : 1 ≤ T^(1/B) := Real.one_le_rpow hT1 hε.le
  let N : ℕ := ⌈T^(1/B)⌉₊
  have hNl : T^(1/B) ≤ (N:ℝ) := Nat.le_ceil _
  have hNu : (N:ℝ) ≤ 2*T^(1/B) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hT0.le (1/B))
    dsimp [N]
    linarith
  have hpow : T^(1/B)*T^(1-1/B) = T := by
    rw [←Real.rpow_add hT0]
    simp
  have hNT : (N:ℝ) ≤ T := hNu.trans (by nlinarith [Real.rpow_pos_of_pos hT0 (1/B)])
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le (by positivity : 0 < T^(1/B)) hNl
  have hN1 : 1 ≤ N := by exact_mod_cast hx.trans hNl
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near ((one_le_div hN0).mpr hNT) (by norm_num : (1:ℝ) < 2)
  have hcap : (2:ℝ)^(k+1)*(N:ℝ) ≤ 2*T := by
    rw [pow_succ]
    have hh := (le_div_iff₀ hN0).mp hk
    linarith
  have hcover : T ≤ (2:ℝ)^(k+1)*(N:ℝ) := ((div_lt_iff₀ hN0).mp hk').le
  refine ⟨N,k+1,hN1,hp.trans hNl,hNT,?_,hcover,hcap,?_,?_⟩
  · calc
      Real.log N ≤ Real.log (2*T^(1/B)) := Real.log_le_log hN0 hNu
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity),Real.log_rpow hT0]
  · rw [←Real.sqrt_eq_rpow]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hlarge : 8*Real.pi^2 ≤ T := (le_max_right _ _).trans hT
    have hsq : 2*T ≤ (T/(2*Real.pi))^2 := by
      have hpi := Real.pi_pos
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos (show 0 < 2*Real.pi by positivity))).mpr
      nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hlarge)]
    exact hcap.trans hsq
  · calc
      T/(2*Real.pi) ≤ T := div_le_self hT0.le (by nlinarith [Real.pi_gt_three])
      _ = (T^(1/B))^B := by rw [←Real.rpow_mul hT0.le, one_div_mul_cancel hB0.ne', Real.rpow_one]
      _ ≤ (N:ℝ)^B := Real.rpow_le_rpow (by positivity) hNl hB0.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterMiddleSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the middle part of a character Dirichlet sum -/
namespace JointDickman
open Complex Filter Finset
open scoped Topology

lemma int_Ioc_eq_Icc_succ (a b : ℤ) : Ioc a b = Icc (a+1) b := by
  ext n
  simp only [mem_Ioc, mem_Icc]
  omega

theorem character_middle_sum_bound (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ U₀ : ℝ, 0 < A ∧ 0 < δ ∧ 1 ≤ U₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
        (σ t : ℝ) (N : ℤ) (K : ℕ),
        U₀ ≤ (N:ℝ) → 1 ≤ σ →
        ((2:ℝ)^K*(N:ℝ))^(1/2:ℝ) ≤ |t/(2*Real.pi)| →
        |t/(2*Real.pi)| ≤ (N:ℝ)^B →
        ‖∑ n ∈ Ioc N ((2:ℤ)^K*N), χ (n:ZMod q)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤
          ((q:ℝ)*A)*(N:ℝ)^(-δ)/(1-(2:ℝ)^(-δ)) := by
  obtain ⟨A,δ,hA,hδ,hh⟩ := character_dyadic_sum_uniform B hB
  obtain ⟨U₀,hU₀⟩ := eventually_atTop.mp hh
  refine ⟨A,δ,max 1 U₀,hA,hδ,le_max_left _ _,?_⟩
  intro q _ χ σ t N K hN hσ hlo hhi
  have hN1 : (1:ℝ) ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN1)
  apply norm_dyadic_sum_bound _ hN0 (by positivity) hδ
  intro j hj
  have hNj : (N:ℝ) ≤ (2:ℝ)^j*(N:ℝ) := by
    nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j)]
  have hUj : U₀ ≤ (2:ℝ)^j*(N:ℝ) := ((le_max_right _ _).trans hN).trans hNj
  have hpow : (2:ℝ)^j*(N:ℝ) ≤ (2:ℝ)^K*(N:ℝ) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj.le) (by linarith)
  rw [int_Ioc_eq_Icc_succ]
  have hc := hU₀ _ hUj q χ σ t (((2:ℤ)^j*N)+1) ((2:ℤ)^(j+1)*N) hσ
    ((Real.rpow_le_rpow (by positivity) hpow (by norm_num)).trans hlo)
    (hhi.trans (Real.rpow_le_rpow (by linarith) hNj (by linarith)))
    (by push_cast <;> linarith)
    (by push_cast; rw [pow_succ]; ring_nf; exact le_rfl)
  simpa only [mul_assoc] using hc

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaCutoff
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded zeta truncation error away from the pole -/
namespace JointDickman
open Complex Finset LargePrimeGaps

lemma regularSeries_constant_eq {s : ℂ} (hs : 1 < s.re) :
    regularSeries (positiveCoefficients (fun _ => 1)) 1 s =
      riemannZeta s - 1 / (s - 1) := by
  rw [regularSeries_eq_LSeries_sub
    (positiveCoefficients_norm_le (by intro n; simp)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun t ht => discrepancy_constant_bound ht.le) hs,
    LSeries_positiveCoefficients]
  change LSeries (1 : ℕ → ℂ) s - 1 / (s - 1) = _
  rw [LSeries_one_eq_riemannZeta hs]

lemma zeta_cutoff_bound {s : ℂ} (hs : 1 < s.re) (hs2 : s.re ≤ 2)
    {N : ℕ} (hN : 1 ≤ N) (htlo : 1 ≤ |s.im|) (hthi : |s.im| ≤ N) :
    ‖riemannZeta s - ∑ n ∈ Icc 1 N, (n : ℂ)^(-s)‖ ≤ 5 := by
  have hs0 : 0 < s.re := by linarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hsne : s - 1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [sub_re, one_re, zero_re] at hr
    linarith
  let A := seriesDiscrepancy (positiveCoefficients (fun _ => 1)) 1
  have he := regularSeries_cutoff (positiveCoefficients_zero (fun _ => 1))
    (D := 1) (by norm_num) (fun t ht => discrepancy_constant_bound ht.le) hN hs0
  rw [regularSeries_constant_eq hs] at he
  have hp : (∑ n ∈ Icc 1 N, positiveCoefficients (fun _ => 1) n * (n : ℂ)^(-s)) =
      ∑ n ∈ Icc 1 N, (n : ℂ)^(-s) := by
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    simp [positiveCoefficients, hn0]
  rw [hp, one_mul] at he
  have hi : (1 / (s - 1) : ℂ) - (∫ t in (1 : ℝ)..N, (t : ℂ)^(-s)) =
      (N : ℂ)^(1-s)/(s-1) := by
    have hc := cpow_sub_eq_mul_intervalIntegral hNR s
    simp only [Complex.ofReal_natCast] at hc
    apply (eq_div_iff hsne).mpr
    calc
      _ = 1 + (1-s)*(∫ t in (1 : ℝ)..N, (t : ℂ)^(-s)) := by field_simp <;> ring
      _ = _ := by rw [←hc]; ring
  have herr : riemannZeta s - ∑ n ∈ Icc 1 N, (n : ℂ)^(-s) =
      -(A N * (N : ℂ)^(-s)) + s * discrepancyTail A N s + (N : ℂ)^(1-s)/(s-1) := by
    dsimp [A]
    rw [←hi]
    linear_combination he
  have hpow : (N : ℝ)^(-s.re) ≤ (N : ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hNR
      (show -s.re ≤ -1 by linarith)
  have htail : ‖discrepancyTail A N s‖ ≤ (N : ℝ)⁻¹ := by
    have hh := discrepancyTail_norm_le hN0 (by norm_num : (0 : ℝ) ≤ 1)
      (measurable_seriesDiscrepancy _ (1 : ℂ))
      (fun t (ht : (N : ℝ) < t) => discrepancy_constant_bound (hNR.trans ht.le)) hs0
    apply hh.trans
    simp only [one_mul]
    exact (div_le_self (by positivity) hs.le).trans hpow
  have hc : ‖A N * (N : ℂ)^(-s)‖ ≤ (N : ℝ)⁻¹ := by
    rw [norm_mul, show (N : ℂ) = ((N : ℝ) : ℂ) by simp,
      norm_cpow_eq_rpow_re_of_pos hN0, neg_re]
    exact (mul_le_of_le_one_left (by positivity) (discrepancy_constant_bound hNR)).trans hpow
  have hnorm : ‖s‖ ≤ 2 + (N : ℝ) := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at hh
    linarith
  have hpole : ‖(N : ℂ)^(1-s)/(s-1)‖ ≤ 1 := by
    rw [norm_div, show (N : ℂ) = ((N : ℝ) : ℂ) by simp,
      norm_cpow_eq_rpow_re_of_pos hN0]
    apply (div_le_one (norm_pos_iff.mpr hsne)).mpr
    have hnum : (N : ℝ)^((1-s).re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hNR (by simp only [sub_re, one_re] <;> linarith)
    have him : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s-1)
    linarith
  rw [herr]
  calc
    _ ≤ (‖A N * (N : ℂ)^(-s)‖ + ‖s‖ * ‖discrepancyTail A N s‖) +
        ‖(N : ℂ)^(1-s)/(s-1)‖ := by
      simpa only [norm_neg, norm_mul] using
        (norm_add_le (-(A N * (N : ℂ)^(-s)) + s * discrepancyTail A N s)
          ((N : ℂ)^(1-s)/(s-1))).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (N : ℝ)⁻¹ + (2 + (N : ℝ)) * (N : ℝ)⁻¹ + 1 :=
      add_le_add (add_le_add hc (mul_le_mul hnorm htail (norm_nonneg _) (by positivity))) hpole
    _ ≤ 5 := by
      have hNi : (N : ℝ)*(N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN0.ne'
      have hile : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNR
      nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaLogFrequency
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Zeta growth on polynomial logarithmic frequency ranges away from the pole

The regularized Dirichlet series has small power growth, and the pole term
is bounded when the frequency has absolute value at least one.
-/
namespace JointDickman
open Complex

lemma zeta_log_frequency_norm {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, Real.exp 1 ≤ X → ∀ t : ℝ,
      1 ≤ |t| → |t| ≤ (Real.log X)^A →
      ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤
        K*(Real.log X)^(1/4:ℝ) := by
  let ε : ℝ := 1/(8*(A+1))
  have hε : 0 < ε := by dsimp [ε] <;> positivity
  have hε1 : ε ≤ 1/2 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0<8*(A+1))).mpr
    linarith
  have hAε : A*(2*ε) ≤ (1/4:ℝ) := by
    dsimp [ε]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have he : A*(2*(1/(8*(A+1))))*4 = A/(A+1) := by
      field_simp
      ring
    rw [he]
    exact (div_le_one (by positivity : 0<A+1)).mpr (by linarith)
  obtain ⟨K,hK,hbound⟩ := LargePrimeGaps.regularSeries_norm_small_power hε hε1
  refine ⟨(K+1)*(10:ℝ)^(2*ε),by positivity,?_⟩
  intro X hX t htlo ht
  have hlog1 : 1 ≤ Real.log X := by
    simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlog : 0 < Real.log X := by linarith
  have hp : 1 ≤ (Real.log X)^A := Real.one_le_rpow hlog1 hA
  have hσ : 0 < 1+1/Real.log X := by positivity
  have hσ2 : 1+1/Real.log X ≤ 2 := by
    have h := (div_le_one hlog).mpr hlog1
    linarith
  have hs : 1-ε ≤ (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,sub_zero,zero_mul,add_zero]
    linarith [one_div_pos.mpr hlog]
  have hnorm : ‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖+2 ≤ 5*(Real.log X)^A := by
    have h := norm_add_le (((1+1/Real.log X:ℝ):ℂ)) ((t:ℂ)*I)
    rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hσ,Complex.norm_real,Real.norm_eq_abs] at h
    linarith
  have hs1 : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, sub_zero, zero_mul, add_zero]
    linarith [one_div_pos.mpr hlog]
  have hreg := hbound (LargePrimeGaps.positiveCoefficients (fun _ => 1)) 1 1
    (LargePrimeGaps.positiveCoefficients_zero _)
    (LargePrimeGaps.positiveCoefficients_norm_le (by intro n; simp))
    (by simp) (by norm_num) (fun u hu => LargePrimeGaps.discrepancy_constant_bound hu)
    (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I) hs
  have hpole : ‖(1 : ℂ) / ((((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)-1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hh := Complex.abs_im_le_norm ((((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)-1)
    have hn : 1 ≤ ‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)-1‖ :=
      htlo.trans (by simpa using hh)
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hn)).mpr hn
  have hpower : 1 ≤ (2*(‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖+2))^(2*ε) :=
    Real.one_le_rpow (by nlinarith [norm_nonneg (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)])
      (by positivity)
  have hzeta : ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤
      (K+1)*(2*(‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖+2))^(2*ε) := by
    have he := regularSeries_constant_eq hs1
    have htri := norm_add_le
      (LargePrimeGaps.regularSeries (LargePrimeGaps.positiveCoefficients (fun _ => 1)) 1
        (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I))
      (1 / ((((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)-1))
    rw [he, sub_add_cancel] at htri
    norm_num only [one_add_one_eq_two] at hreg
    rw [he] at hreg
    nlinarith
  calc
    _ ≤ (K+1)*(2*(‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖+2))^(2*ε) := hzeta
    _ ≤ (K+1)*((10:ℝ)*(Real.log X)^A)^(2*ε) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      linarith
    _ = ((K+1)*(10:ℝ)^(2*ε))*(Real.log X)^(A*(2*ε)) := by
      rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hlog.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog1 hAε) (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaLogarithmicBound
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An arbitrarily small logarithmic bound for zeta away from its pole -/
namespace JointDickman
open Complex Filter Finset
open scoped Topology

theorem zeta_logarithmic_bound {B : ℝ} (hB : 2 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ t σ : ℝ,
      |t| = T → 1 < σ → σ ≤ 2 →
      ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖ ≤ (1/B)*Real.log T+C := by
  obtain ⟨A,δ,U₀,hA,hδ,hU₀,hmid⟩ := character_middle_sum_bound B (by linarith)
  have hden : 0 < 1-(2:ℝ)^(-δ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  let C : ℝ := 1+Real.log 2+5+A/(1-(2:ℝ)^(-δ))
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨C,hC,?_⟩
  let χ : DirichletCharacter ℂ 1 := 1
  filter_upwards [character_frequency_scales hB U₀, eventually_ge_atTop (1 : ℝ)] with T hscale hT
  intro t σ ht hσ hσ2
  obtain ⟨N,K,hN,hNU,hNT,hlog,hcover,hcap,hlo,hhi⟩ := hscale
  let M : ℕ := 2^K*N
  have hNM : N ≤ M := by
    dsimp [M]
    nlinarith [one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2) (n := K)]
  have hM : 1 ≤ M := hN.trans hNM
  have hMR : (M:ℝ) = (2:ℝ)^K*(N:ℝ) := by simp [M]
  have hMI : (M:ℤ) = (2:ℤ)^K*(N:ℤ) := by simp [M]
  have hN0 : (0:ℝ) < N := by exact_mod_cast (zero_lt_one.trans_le hN)
  have hfreq : |t/(2*Real.pi)| = T/(2*Real.pi) := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 2*Real.pi),ht]
  have hsre : ((σ:ℂ)+(t:ℂ)*I).re = σ := by simp
  have hsim : ((σ:ℂ)+(t:ℂ)*I).im = t := by simp
  have htail₀ := zeta_cutoff_bound (s := (σ:ℂ)+(t:ℂ)*I)
    (by simpa only [hsre] using hσ) (by simpa only [hsre] using hσ2) hM
    (by simpa only [hsim, ht] using hT)
    (by simpa only [hsim,ht,hMR] using hcover)
  have hχn (n : ZMod 1) : χ n = 1 := by
    rw [show n = 1 from Subsingleton.elim _ _]; exact map_one χ
  have htail : ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I) -
      ∑ n ∈ Icc 1 M, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤ 5 := by
    simpa only [hχn, one_mul] using htail₀
  have hmiddle := hmid 1 χ σ t (N:ℤ) K (by exact_mod_cast hNU) hσ.le
    (by simpa only [Int.cast_natCast,hfreq] using hlo)
    (by simpa only [Int.cast_natCast,hfreq] using hhi)
  have hpow : (N:ℝ)^(-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hN) (by linarith)
  have hmiddle' : ‖∑ n ∈ Ioc (N:ℤ) (M:ℤ),
      χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤ A/(1-(2:ℝ)^(-δ)) := by
    rw [hMI]
    have hm : ‖∑ n ∈ Ioc (N:ℤ) ((2:ℤ)^K*(N:ℤ)),
        χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))‖ ≤ A*(N:ℝ)^(-δ)/(1-(2:ℝ)^(-δ)) := by
      simpa only [Nat.cast_one, Int.cast_natCast, one_mul] using hmiddle
    exact hm.trans (div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (by positivity) hpow) hden.le)
  let f : ℤ → ℂ := fun n => χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))
  have hsplit : (∑ n ∈ Icc 1 N, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))+
      (∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n) =
      ∑ n ∈ Icc 1 M, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)) := by
    have hh := sum_int_Ioc_consecutive f (a := 0) (b := N) (c := M)
      (by exact_mod_cast (Nat.zero_le N)) (by exact_mod_cast hNM)
    rw [int_Ioc_eq_Icc_succ 0, int_Ioc_eq_Icc_succ 0] at hh
    simp only [zero_add] at hh
    have heN := sum_nat_Icc_int_cast f 1 N
    have heM := sum_nat_Icc_int_cast f 1 M
    simp only [Nat.cast_one] at heN heM
    rw [←heN,←heM] at hh
    simpa [f] using hh
  have hhead := character_LFunction_head_bound χ ((σ:ℂ)+(t:ℂ)*I)
    (by simpa only [hsre] using hσ.le) N
  have hfull := norm_add_le
    (riemannZeta ((σ:ℂ)+(t:ℂ)*I)-∑ n ∈ Icc 1 M, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))
    (∑ n ∈ Icc 1 M, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))
  rw [sub_add_cancel] at hfull
  have htail' : ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I) -
      ((∑ n ∈ Icc 1 N, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I))) +
      ∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n)‖ ≤ 5 := by
    rw [hsplit]
    exact htail
  rw [←hsplit] at hfull
  have hsum := norm_add_le
    (∑ n ∈ Icc 1 N, χ (n:ZMod 1)*(n:ℂ)^(-((σ:ℂ)+(t:ℂ)*I)))
    (∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n)
  change ‖∑ n ∈ Ioc (N:ℤ) (M:ℤ), f n‖ ≤ _ at hmiddle'
  dsimp only [C]
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaUniformSublog
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform sublogarithmic zeta bounds away from zero frequency -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem zeta_uniform_sublog {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ 2*X →
      ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ η*Real.log X := by
  let B : ℝ := 2+4/η
  have hB : 2 ≤ B := by dsimp [B] <;> linarith [div_pos (show (0:ℝ) < 4 by norm_num) hη]
  have hB0 : 0 < B := by linarith
  have hBcoef : 1/B ≤ η/4 := by
    apply (div_le_iff₀ hB0).mpr
    have he : (η/4)*B = η/2+1 := by dsimp [B]; field_simp <;> ring
    rw [he]
    linarith
  obtain ⟨C,hC,hlarge⟩ := zeta_logarithmic_bound hB
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hlarge
  obtain ⟨K,hK,hsmall⟩ := zeta_log_frequency_norm (show (0:ℝ) ≤ 1 by norm_num)
  have hlog := Real.tendsto_log_atTop
  have hpower := (tendsto_rpow_atTop (show (0:ℝ) < 3/4 by norm_num)).comp hlog
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (2 : ℝ),hlog.eventually_ge_atTop T₀,
    hlog.eventually_ge_atTop (2*C/η),hpower.eventually_ge_atTop (K/η)]
    with X hX hX2 hXT hXC hXK
  intro t htlo ht
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlog0 : 0 < Real.log X := by linarith
  have hσ1 : 1 < 1+1/Real.log X := by linarith [one_div_pos.mpr hlog0]
  have hσ2 : 1+1/Real.log X ≤ 2 := by
    have hh := (div_le_one hlog0).mpr hlog1
    linarith
  by_cases htlog : |t| ≤ Real.log X
  · have hb := hsmall X hX t htlo (by simpa using htlog)
    have hKbound : K ≤ η*(Real.log X)^(3/4:ℝ) := by
      simpa only [Function.comp_def, mul_comm] using (div_le_iff₀ hη).mp hXK
    have he : (Real.log X)^(3/4:ℝ)*(Real.log X)^(1/4:ℝ) = Real.log X := by
      rw [←Real.rpow_add hlog0]
      norm_num
    exact hb.trans (by
      calc
        _ ≤ (η*(Real.log X)^(3/4:ℝ))*(Real.log X)^(1/4:ℝ) :=
          mul_le_mul_of_nonneg_right hKbound (by positivity)
        _ = _ := by rw [mul_assoc,he])
  · have ht0 : 0 < |t| := hlog0.trans (lt_of_not_ge htlog)
    have hb := hT₀ |t| (hXT.trans (lt_of_not_ge htlog).le) t (1+1/Real.log X) rfl hσ1 hσ2
    have hCbound : C ≤ (η/2)*Real.log X := by
      have hh := (div_le_iff₀ hη).mp hXC
      nlinarith
    have hlt₀ := Real.log_le_log ht0 ht
    have hlt : Real.log |t| ≤ 2*Real.log X := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : X ≠ 0)] at hlt₀
      have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX2
      linarith
    calc
      _ ≤ (1/B)*Real.log |t|+C := hb
      _ ≤ (1/B)*(2*Real.log X)+C := add_le_add (mul_le_mul_of_nonneg_left hlt (by positivity : 0 ≤ 1/B)) le_rfl
      _ ≤ (η/4)*(2*Real.log X)+(η/2)*Real.log X :=
        add_le_add (mul_le_mul_of_nonneg_right hBcoef (by positivity)) hCbound
      _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDistanceComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changes of prime values in the squared pretentious distance -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem primeDistance_phase_norm (p : ℕ) (t : ℝ) :
    ‖Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)‖ = 1 := by
  simp only [Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
    Complex.neg_im,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
    sub_self,neg_zero,Real.exp_zero]

theorem primeDistance_term_sub_le (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (p : ℕ) (t : ℝ) :
    (1-(g p*Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)).re)/(p : ℝ)-
      (1-(f p*Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)).re)/(p : ℝ) ≤
        2/(p : ℝ) := by
  let e := Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)
  have he : ‖e‖ = 1 := primeDistance_phase_norm p t
  have hfn : ‖f p*e‖ ≤ 1 := by simpa only [norm_mul,he,mul_one] using hf p
  have hgn : ‖g p*e‖ ≤ 1 := by simpa only [norm_mul,he,mul_one] using hg p
  have hl : -1 ≤ (g p*e).re := by
    have hh := (Complex.abs_re_le_norm (g p*e)).trans hgn
    exact (abs_le.mp hh).1
  have hu : (f p*e).re ≤ 1 := (Complex.re_le_norm _).trans hfn
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by dsimp [e] at hl hu <;> linarith) (Nat.cast_nonneg _)

theorem primeDistanceSquared_lower_of_agree (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (P : Finset ℕ) (X Y t : ℝ)
    (heq : ∀ p : ℕ, p.Prime → p ∉ P → (p : ℝ) ≤ Y → f p = g p) :
    primeDistanceSquared g X t-2*((∑ p ∈ largePrimeSet X Y, 1/(p : ℝ))+
      ∑ p ∈ P, 1/(p : ℝ)) ≤ primeDistanceSquared f X t := by
  let S := (Icc 2 ⌊X⌋₊).filter Nat.Prime
  have hb : primeDistanceSquared g X t-primeDistanceSquared f X t ≤
      ∑ p ∈ S, ((if Y < (p : ℝ) then 2/(p : ℝ) else 0)+
        (if p ∈ P then 2/(p : ℝ) else 0)) := by
    unfold primeDistanceSquared
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro p hp
    have hp' : p.Prime := (mem_filter.mp hp).2
    by_cases hP : p ∈ P
    · have hh := primeDistance_term_sub_le f g hf hg p t
      rw [ite_eq_left hP]
      split_ifs <;> linarith [show (0 : ℝ) ≤ 2/(p : ℝ) by positivity]
    · rw [ite_eq_right hP,add_zero]
      by_cases hY : Y < (p : ℝ)
      · rw [ite_eq_left hY]
        exact primeDistance_term_sub_le f g hf hg p t
      · rw [ite_eq_right hY,heq p hp' hP (le_of_not_gt hY),sub_self]
  have hl : (∑ p ∈ S, if Y < (p : ℝ) then 2/(p : ℝ) else 0) =
      2*∑ p ∈ largePrimeSet X Y, 1/(p : ℝ) := by
    rw [← sum_filter]
    change (∑ p ∈ ((Icc 2 ⌊X⌋₊).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)), 2/(p : ℝ)) = _
    rw [← primesLE_eq_filter]
    change (∑ p ∈ largePrimeSet X Y, 2/(p : ℝ)) = _
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  have hp : (∑ p ∈ S, if p ∈ P then 2/(p : ℝ) else 0) ≤ 2*∑ p ∈ P, 1/(p : ℝ) := by
    rw [← sum_filter,mul_sum]
    calc
      _ ≤ ∑ p ∈ P, 2/(p : ℝ) := sum_le_sum_of_subset_of_nonneg
        (fun p hp => (mem_filter.mp hp).2) (fun p _ _ => by positivity)
      _ = _ := by apply sum_congr rfl; intro p _; ring
  rw [sum_add_distrib,hl] at hb
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePhaseDivergence
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Qualitative prime-phase separation on the full frequency range -/
namespace JointDickman
open Complex Filter Finset PublishedInputs
open scoped Topology

lemma principalDistance_eq_cosine (X t : ℝ) :
    primeDistanceSquared (characterArithmetic (1 : DirichletCharacter ℂ 1)) X t =
      ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
        (1 - Real.cos (t * Real.log (p : ℝ))) / (p : ℝ) := by
  unfold primeDistanceSquared
  apply sum_congr rfl
  intro p hp
  rw [characterArithmetic_prime _ (mem_filter.mp hp).2]
  have hc : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 := by
    rw [show (p : ZMod 1) = 1 from Subsingleton.elim _ _]; exact map_one _
  simp only [hc, one_mul, Complex.exp_re, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    neg_zero, add_zero, Real.exp_zero, Real.cos_neg]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePhasePolynomial
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-phase separation up to a fixed power of the cutoff -/
namespace JointDickman
open Complex Filter Finset
open scoped Topology

theorem zeta_uniform_sublog_polynomial (A : ℝ) (hA : 1 ≤ A) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ X^A →
      ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ η*Real.log X := by
  let B : ℝ := 2+2*A/η
  have hA0 : 0 < A := by linarith
  have hB : 2 ≤ B := by dsimp [B] <;> linarith [div_pos (mul_pos (by norm_num : (0:ℝ)<2) hA0) hη]
  have hB0 : 0 < B := by linarith
  have hcoef : 1/B ≤ η/(2*A) := by
    apply (div_le_iff₀ hB0).mpr
    have he : (η/(2*A))*B = η/A+1 := by dsimp [B]; field_simp
    rw [he]
    linarith [div_pos hη hA0]
  obtain ⟨C,hC,hlarge⟩ := zeta_logarithmic_bound hB
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hlarge
  filter_upwards [zeta_uniform_sublog hη,eventually_ge_atTop (max T₀ (Real.exp 1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*C/η))]
    with X hbase hX hXC
  intro t htlo ht
  by_cases hsmall : |t| ≤ 2*X
  · exact hbase t htlo hsmall
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hXT : T₀ ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hXe
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hXe
  have hlog0 : 0 < Real.log X := by linarith
  have ht0 : 0 < |t| := by linarith
  have hσ1 : 1 < 1+1/Real.log X := by linarith [one_div_pos.mpr hlog0]
  have hσ2 : 1+1/Real.log X ≤ 2 := by
    have := (div_le_one hlog0).mpr hlog1
    linarith
  have hb := hT₀ |t| (by linarith) t (1+1/Real.log X) rfl hσ1 hσ2
  have hCbound : C ≤ (η/2)*Real.log X := by
    have hh := (div_le_iff₀ hη).mp hXC
    nlinarith
  have hlt : Real.log |t| ≤ A*Real.log X := by
    have hh := Real.log_le_log ht0 ht
    rwa [Real.log_rpow hX0] at hh
  calc
    _ ≤ (1/B)*Real.log |t|+C := hb
    _ ≤ (1/B)*(A*Real.log X)+C :=
      add_le_add (mul_le_mul_of_nonneg_left hlt (by positivity)) le_rfl
    _ ≤ (η/(2*A))*(A*Real.log X)+(η/2)*Real.log X :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (by positivity)) hCbound
    _ = _ := by field_simp <;> ring

theorem prime_cosine_defect_polynomial (A : ℝ) (hA : 1 ≤ A) (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ X^A →
      R ≤ ∑ p ∈ (Icc 2 ⌊X⌋₊).filter Nat.Prime,
        (1-Real.cos (t*Real.log (p:ℝ)))/(p:ℝ) := by
  obtain ⟨C,hC⟩ := characterDistance_ge_log_sub_L
  let η := Real.exp (-(R+C+1))
  filter_upwards [zeta_uniform_sublog_polynomial A hA (Real.exp_pos (-(R+C+1))),
    eventually_ge_atTop (max 2 (Real.exp 1))] with X hbound hX
  intro t htlo ht
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hXe
  have hlog : 0 < Real.log X := by linarith
  have hs : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,sub_zero,zero_mul,add_zero]
    linarith [one_div_pos.mpr hlog]
  have hn : 0 < ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs)
  have hl := Real.log_le_log hn (hbound t htlo ht)
  rw [Real.log_mul (Real.exp_pos _).ne' hlog.ne',Real.log_exp] at hl
  have hd := hC 1 (1 : DirichletCharacter ℂ 1) X hX t
  rw [DirichletCharacter.LFunction_modOne_eq,principalDistance_eq_cosine] at hd
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeAgreementPolynomial
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large-frequency distance from small-prime agreement -/
namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

theorem prime_agreement_distance_polynomial_jd_oai {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (P : Finset ℕ) (A : ℝ) (hA : 1 ≤ A) (R : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ f : ArithmeticFunction ℂ,
      (∀ n, ‖f n‖ ≤ 1) →
      (∀ p : ℕ, p.Prime → p ∉ P → (p:ℝ) ≤ X^c → f p = 1) →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ X^A → R ≤ primeDistanceSquared f X t := by
  let M : ℝ := -Real.log c+1+∑ p ∈ P, 1/(p:ℝ)
  have htail := (largePrimeSet_reciprocal_tendsto primeReciprocalMertensInput hc hc1).eventually
    (eventually_le_nhds (lt_add_one (-Real.log c)))
  filter_upwards [prime_cosine_defect_polynomial A hA (R+2*M),htail]
    with X hX htailX
  intro f hf heq t htlo ht
  let g := characterArithmetic (1 : DirichletCharacter ℂ 1)
  have hg : ∀ n, ‖g n‖ ≤ 1 := characterArithmetic_norm_le_one _
  have hgp (p : ℕ) (hp : p.Prime) : g p = 1 := by
    dsimp [g]
    rw [characterArithmetic_prime _ hp,
      show (p:ZMod 1) = 1 from Subsingleton.elim _ _]
    exact map_one _
  have hh := primeDistanceSquared_lower_of_agree f g hf hg P X (X^c) t (by
    intro p hp hpP hpX
    rw [heq p hp hpP hpX,hgp p hp])
  have hd := hX t htlo ht
  rw [← principalDistance_eq_cosine] at hd
  change R+2*M ≤ primeDistanceSquared g X t at hd
  dsimp only [M] at hd
  linarith

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.prime_agreement_distance_polynomial_jd_oai := @OAI.JointDickman.prime_agreement_distance_polynomial_jd_oai
