-- Prove2me | solution 1 for OAI.JointDickman.mellin_prime_sampling_arithmetic_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:48:27.217173+00:00
-- url     : https://prove2.me/submissions/43c7774d-7d9f-46eb-a634-2540d0e04dc9

import Mathlib
import Definitions.Def_OAIQ083J000
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

section
-- module Solutions.OAIQ083_JD.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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
/-- Mathlib d13f23b's `integral_comp_log_Ioi_zero`: the substitution `y = log x` over `Ioi 0` (JointDickman
MellinSieveProfile, CubicMoment, q142). -/
theorem integral_comp_log_Ioi_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x in Set.Ioi (0 : ℝ), x⁻¹ • g (Real.log x) = ∫ y, g y := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := (Set.univ : Set ℝ))
    (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) (fun x => x⁻¹ • g (Real.log x))
  rw [Set.image_univ, Real.range_exp] at h
  rw [h, MeasureTheory.setIntegral_univ]
  congr 1; funext x
  simp [abs_of_pos (Real.exp_pos x), smul_smul, Real.exp_ne_zero]
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
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

end Mertens

end Erdos970
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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IncreasingPartialSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Increasing weights in finite partial summation -/
namespace JointDickman
open Finset

lemma increasing_weighted_sum_range_bound (g : ℕ → ℂ) (w : ℕ → ℝ)
    {N : ℕ} {D : ℝ} (hD : 0 ≤ D) (hw : ∀ i, 0 ≤ w i)
    (hmono : Monotone w)
    (hpartial : ∀ k ≤ N, ‖∑ i ∈ range k, g i‖ ≤ D) :
    ‖∑ i ∈ range N, w i • g i‖ ≤ 2*D*w N := by
  have htel (M : ℕ) : (∑ i ∈ range M, (w (i+1)-w i)) = w M-w 0 := by
    induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ, ih]; ring
  cases N with
  | zero => simpa only [range_zero, sum_empty, norm_zero] using
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hD) (hw 0)
  | succ N =>
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel]
    have hterm : ‖w N • (∑ i ∈ range (N+1), g i)‖ ≤ w N*D := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw N)]
      exact mul_le_mul_of_nonneg_left (hpartial _ le_rfl) (hw N)
    have hsum : ‖∑ i ∈ range N, (w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ ≤
        (∑ i ∈ range N, (w (i+1)-w i))*D := by
      apply (norm_sum_le _ _).trans
      rw [sum_mul]
      apply sum_le_sum
      intro i hi
      have hii : w i ≤ w (i+1) := hmono (by omega)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hii)]
      exact mul_le_mul_of_nonneg_left (hpartial _ (by have := mem_range.mp hi; omega))
        (sub_nonneg.mpr hii)
    calc
      _ ≤ ‖w N • (∑ i ∈ range (N+1), g i)‖ +
          ‖∑ i ∈ range N, (w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ := norm_sub_le _ _
      _ ≤ w N*D+(∑ i ∈ range N, (w (i+1)-w i))*D := add_le_add hterm hsum
      _ ≤ 2*D*w (N+1) := by
        rw [htel]
        nlinarith [hw 0, hmono (show N ≤ N+1 by omega)]

lemma increasing_weighted_sum_Icc_bound (g : ℤ → ℂ) (w : ℤ → ℝ)
    (L R : ℤ) (hLR : L ≤ R) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ n, L ≤ n → 0 ≤ w n)
    (hmono : MonotoneOn w (Set.Ici L))
    (hpartial : ∀ V, L ≤ V → V ≤ R → ‖∑ n ∈ Icc L V, g n‖ ≤ D) :
    ‖∑ n ∈ Icc L R, w n • g n‖ ≤ 2*D*w (R+1) := by
  let N := (R+1-L).toNat
  have hN : (N:ℤ) = R+1-L := Int.toNat_of_nonneg (by omega)
  have hR : R = L+(N:ℤ)-1 := by omega
  rw [hR, sum_Icc_int_translate]
  have hh := increasing_weighted_sum_range_bound (fun i => g (L+i))
    (fun i => w (L+i)) hD (fun i => hw _ (by omega))
    (fun i j hij => hmono (by simp) (by simp) (by omega)) (N := N) (by
      intro k hk
      by_cases hk0 : k = 0
      · simpa [hk0] using hD
      · rw [← sum_Icc_int_translate]
        exact hpartial _ (by omega) (by omega))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  omega

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LipschitzRiemannSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite Riemann-sum error for a Lipschitz function -/
namespace JointDickman
open Finset MeasureTheory

lemma lipschitz_riemann_sum_error (f : ℝ → ℂ) (M : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x ∈ Set.Icc (0:ℝ) M, ∀ y ∈ Set.Icc (0:ℝ) M,
      ‖f y-f x‖ ≤ L*|y-x|) :
    ‖(∑ n ∈ range M, f (n+1)) - ∫ x in (0:ℝ)..M, f x‖ ≤ M*L := by
  have hcont : ContinuousOn f (Set.Icc (0:ℝ) M) :=
    (LipschitzOnWith.of_dist_le' (fun x hx y hy => by
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hf y hy x hx)).continuousOn
  have hint (n : ℕ) (hn : n < M) : IntervalIntegrable f volume n (n+1) := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (n:ℝ) ≤ n+1)] at hx
    exact ⟨(Nat.cast_nonneg n).trans hx.1, hx.2.trans (by exact_mod_cast hn)⟩
  have herror (n : ℕ) (hn : n < M) :
      ‖f (n+1) - ∫ x in (n:ℝ)..n+1, f x‖ ≤ L := by
    have he : f (n+1) - (∫ x in (n:ℝ)..n+1, f x) =
        ∫ x in (n:ℝ)..n+1, (f (n+1)-f x) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hint n hn),
        intervalIntegral.integral_const]
      simp
    rw [he]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := L)
      (a := (n:ℝ)) (b := n+1) (f := fun x => f (n+1)-f x) (by
        intro x hx
        rw [Set.uIoc_of_le (by norm_num : (n:ℝ) ≤ n+1)] at hx
        have hxM : x ∈ Set.Icc (0:ℝ) M :=
          ⟨(Nat.cast_nonneg n).trans hx.1.le, hx.2.trans (by exact_mod_cast hn)⟩
        have hnM : (n:ℝ)+1 ∈ Set.Icc (0:ℝ) M :=
          ⟨by positivity, by exact_mod_cast hn⟩
        apply (hf x hxM (n+1) hnM).trans
        apply mul_le_of_le_one_right hL
        rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
        linarith [hx.1])
    simpa only [add_sub_cancel_left, abs_one, mul_one] using hh
  have hs : (∑ n ∈ range M, ∫ x in (n:ℝ)..n+1, f x) = ∫ x in (0:ℝ)..M, f x := by
    convert intervalIntegral.sum_integral_adjacent_intervals
      (a := fun n : ℕ => (n:ℝ)) (fun n hn => by simpa only [Nat.cast_add, Nat.cast_one] using hint n hn) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  rw [← hs, ← sum_sub_distrib]
  exact (norm_sum_le _ _).trans ((sum_le_sum (fun n hn => herror n (mem_range.mp hn))).trans_eq (by simp))

lemma riemann_sum_range_succ_eq_Icc {E : Type*} [AddCommMonoid E] (f : ℕ → E) (M : ℕ) :
    (∑ n ∈ range M, f (n+1)) = ∑ n ∈ Icc 1 M, f n := by
  apply sum_bij (fun n _ => n+1)
  · intro n hn
    exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hn; omega⟩
  · intro n hn m hm he
    omega
  · intro n hn
    refine ⟨n-1, mem_range.mpr ?_, ?_⟩
    · have := mem_Icc.mp hn
      omega
    · have := mem_Icc.mp hn
      omega
  · intro n hn
    rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSetWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prime-selection and fair-split weights

The independent prime-set model and its fair splits satisfy exact finite
identities without prime asymptotics or analytic equidistribution premises.
-/

namespace JointDickman

open scoped BigOperators

theorem bernoulliSubsetMass_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {q : α → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    0 ≤ bernoulliSubsetMass P q S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p hp => (hq p (hS hp)).1)
  · exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hq p
      (Finset.mem_sdiff.mp hp).1).2)

theorem bernoulliSubsetMass_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S = 1 := by
  simp only [bernoulliSubsetMass]
  rw [← Finset.prod_add]
  simp

/-- The exact finite product formula for a multiplicative tilt. -/
theorem bernoulliSubsetMass_tilt {α : Type*} [DecidableEq α]
    (P : Finset α) (q v : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * (∏ p ∈ S, v p) =
      ∏ p ∈ P, (1 - q p + q p * v p) := by
  calc
    _ = ∑ S ∈ P.powerset,
        (∏ p ∈ S, q p * v p) * ∏ p ∈ P \ S, (1 - q p) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib]
      unfold bernoulliSubsetMass
      ring
    _ = _ := by rw [← Finset.prod_add]; congr 1; ext p; ring

/-- Products of distinct prime sets remember their set of factors. -/
theorem primeProduct_injective {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have hSF := Nat.primeFactors_prod (fun p hp => hP p (hS hp))
  have hTF := Nat.primeFactors_prod (fun p hp => hP p (hT hp))
  rw [← hSF, ← hTF, heq]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogProductBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite logarithmic errors for prime-product normalizations

The quadratic logarithmic error is summable above the lower prime cutoff.
The inverse factors in the exact Bernoulli product mass are controlled
separately by a reciprocal sum over the selected primes.
-/

namespace JointDickman

open Finset

theorem log_one_sub_add_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  have hbase : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_of_nonneg hx, add_comm] using h
  have hden : 0 < 1 - x := by linarith
  apply hbase.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

/-- The exact odds correction is bounded by an exponential of the
selected reciprocal mass, uniformly in the number of allowed primes. -/
theorem inverse_product_le_exp {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    (∏ i ∈ P, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ P, x i) := by
  have hpoint (i : ι) (hi : i ∈ P) : (1 - x i)⁻¹ ≤ Real.exp (2 * x i) := by
    have hpos : 0 < 1 - x i := by linarith [(hx i hi).2]
    have herr := log_one_sub_add_error (hx i hi).1 (hx i hi).2
    have hlog : Real.log ((1 - x i)⁻¹) ≤ 2 * x i := by
      rw [Real.log_inv]
      have hmul := mul_nonneg (hx i hi).1 (show 0 ≤ 1 - 2 * x i by linarith [(hx i hi).2])
      nlinarith [(abs_le.mp herr).1]
    calc
      _ = Real.exp (Real.log ((1 - x i)⁻¹)) := (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    _ ≤ ∏ i ∈ P, Real.exp (2 * x i) := Finset.prod_le_prod
      (fun i hi => inv_nonneg.mpr (by linarith [(hx i hi).2])) hpoint
    _ = Real.exp (∑ i ∈ P, 2 * x i) := (Real.exp_sum P (fun i => 2 * x i)).symm
    _ = _ := by rw [← mul_sum]

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Even inclusion-exclusion truncations for the finite sieve -/
namespace JointDickman
open Finset

 theorem brunTruncation_eq_choose_sum (S : Finset ℕ) (m : ℕ) :
    brunTruncation S m = ∑ k ∈ range (m+1), (-1 : ℝ)^k*(S.card.choose k) := by
  classical
  have hf := sum_fiberwise_of_maps_to (g := Finset.card)
    (s := S.powerset.filter (fun D => D.card ≤ m)) (t := range (m+1))
    (fun D hD => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2))
    (fun D => (-1 : ℝ)^D.card)
  rw [brunTruncation, ← hf]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
  have he : (S.powerset.filter (fun D => D.card ≤ m)).filter (fun D => D.card = k) =
      S.powersetCard k := by
    ext D
    simp only [mem_filter, mem_powerset, mem_powersetCard]
    constructor
    · rintro ⟨⟨hDS,_⟩,hDk⟩
      exact ⟨hDS,hDk⟩
    · rintro ⟨hDS,hDk⟩
      exact ⟨⟨hDS,hDk.trans_le hkm⟩,hDk⟩
  rw [he]
  trans ∑ _D ∈ S.powersetCard k, (-1 : ℝ)^k
  · apply sum_congr rfl
    intro D hD
    rw [(mem_powersetCard.mp hD).2]
  · simp [mul_comm]

 theorem brunTruncation_even (S : Finset ℕ) (r : ℕ) :
    brunTruncation S (2*r) = if S = ∅ then 1 else ((S.card-1).choose (2*r) : ℝ) := by
  classical
  rw [brunTruncation_eq_choose_sum]
  by_cases hS : S = ∅
  · subst S
    rw [ite_eq_left rfl, sum_eq_single 0]
    · simp
    · intro k _ hk
      simp only [card_empty]
      rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
      simp
    · simp
  · rw [ite_eq_right hS]
    have hs : S.card = (S.card-1)+1 := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr hS); omega
    have h := Int.alternating_sum_range_choose_eq_choose (n := S.card-1) (m := 2*r)
    have hr : (-1 : ℤ)^(2*r) = 1 := by simp [pow_mul]
    rw [← hs,hr,one_mul] at h
    exact_mod_cast h

 theorem brunTruncation_nonneg (S : Finset ℕ) (r : ℕ) : 0 ≤ brunTruncation S (2*r) := by
  rw [brunTruncation_even]
  split_ifs <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunTruncationError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An exponential error bound for even truncation -/
namespace JointDickman
open Finset

 theorem brunTruncation_error (S : Finset ℕ) (r : ℕ) :
    brunTruncation S (2*r) ≤ (if S = ∅ then 1 else 0) + (4 : ℝ)^S.card/(4 : ℝ)^r := by
  classical
  rw [brunTruncation_even]
  by_cases hS : S = ∅
  · simp only [hS, ite_true, if_true, card_empty, pow_zero]
    have h : 0 ≤ (1 : ℝ)/4^r := by positivity
    linarith
  · simp only [hS, ite_false, if_false, zero_add]
    by_cases hcard : S.card ≤ 2*r
    · have hlt : S.card-1 < 2*r := by
        have hp := card_pos.mpr (nonempty_iff_ne_empty.mpr hS)
        omega
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero]
      positivity
    · have hcr : 2*r ≤ S.card := by omega
      have hchoose : ((S.card-1).choose (2*r) : ℝ) ≤ (2 : ℝ)^(S.card-1) := by
        exact_mod_cast Nat.choose_le_two_pow (S.card-1) (2*r)
      apply hchoose.trans
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4^r)).mpr
      calc
        (2 : ℝ)^(S.card-1)*4^r = 2^(S.card-1+2*r) := by
          rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_add]
        _ ≤ 2^(2*S.card) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 4^S.card := by rw [show (4 : ℝ) = 2^2 by norm_num, pow_mul]

 theorem brunMean_le (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) {B : ℝ} (hB : ∑ p ∈ P, g p ≤ B) :
    brunMean P g r ≤ (∏ p ∈ P, (1-g p)) + Real.exp (3*B)/(4 : ℝ)^r := by
  classical
  have he : (∑ E ∈ P.powerset, bernoulliSubsetMass P g E * (if E = ∅ then 1 else 0)) =
      ∏ p ∈ P, (1-g p) := by
    rw [sum_eq_single ∅]
    · simp [bernoulliSubsetMass]
    · intro E _ hE
      simp [hE]
    · simp
  have hm : (∑ E ∈ P.powerset, bernoulliSubsetMass P g E * (4 : ℝ)^E.card) =
      ∏ p ∈ P, (1+3*g p) := by
    simpa only [prod_const, show ∀ p, 1-g p+g p*4 = 1+3*g p by intro p; ring] using
      bernoulliSubsetMass_tilt P g (fun _ => 4)
  have hp : (∏ p ∈ P, (1+3*g p)) ≤ Real.exp (3*B) := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (3*g p) := Finset.prod_le_prod
        (fun p hp => by linarith [(hg p hp).1])
        (fun p _ => by simpa only [add_comm] using Real.add_one_le_exp (3*g p))
      _ = Real.exp (3*∑ p ∈ P, g p) := by rw [mul_sum, Real.exp_sum]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ ∑ E ∈ P.powerset, bernoulliSubsetMass P g E *
        ((if E = ∅ then 1 else 0)+(4 : ℝ)^E.card/(4 : ℝ)^r) := by
      apply sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_left (brunTruncation_error E r)
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hE) hg)
    _ = (∏ p ∈ P, (1-g p)) + (∏ p ∈ P, (1+3*g p))/(4 : ℝ)^r := by
      simp only [mul_add, ← mul_div_assoc, sum_add_distrib, ← sum_div, he, hm]
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hp (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) r))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RequiredPrimeSubset
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability that an independent site contains prescribed primes -/

namespace JointDickman
open Finset

open Classical in
theorem bernoulliSubsetMass_required {α : Type*} [DecidableEq α]
    (P A : Finset α) (q : α → ℝ) (hA : A ⊆ P) :
    (∑ S ∈ P.powerset, if A ⊆ S then bernoulliSubsetMass P q S else 0) =
      ∏ p ∈ A, q p := by
  have hm {S : Finset α} (hS : S ⊆ P) (hAS : A ⊆ S) :
      bernoulliSubsetMass P q S =
        (∏ p ∈ A, q p)*bernoulliSubsetMass (P \ A) q (S \ A) := by
    have he : (P \ A) \ (S \ A) = P \ S := by
      ext p
      simp only [mem_sdiff]
      constructor
      · rintro ⟨⟨hp, ha⟩, hs⟩
        exact ⟨hp, fun h => hs ⟨h,ha⟩⟩
      · rintro ⟨hp, hs⟩
        exact ⟨⟨hp, fun h => hs (hAS h)⟩, fun h => hs h.1⟩
    unfold bernoulliSubsetMass
    rw [he, ← prod_sdiff hAS]
    ring
  calc
    _ = ∑ S ∈ P.powerset.filter (fun S => A ⊆ S), bernoulliSubsetMass P q S := by
      rw [sum_filter]
    _ = ∑ T ∈ (P \ A).powerset, (∏ p ∈ A, q p)*bernoulliSubsetMass (P \ A) q T := by
      apply sum_bij (fun S _ => S \ A)
      · intro S hS
        apply mem_powerset.mpr
        intro p hp
        exact mem_sdiff.mpr ⟨(mem_powerset.mp (mem_filter.mp hS).1)
          (mem_sdiff.mp hp).1, (mem_sdiff.mp hp).2⟩
      · intro S hS T hT he
        have hAS := (mem_filter.mp hS).2
        have hAT := (mem_filter.mp hT).2
        have hs := sdiff_union_of_subset hAS
        have ht := sdiff_union_of_subset hAT
        rw [he] at hs
        exact hs.symm.trans ht
      · intro T hT
        have ht := mem_powerset.mp hT
        refine ⟨A ∪ T, mem_filter.mpr ⟨mem_powerset.mpr (union_subset hA (ht.trans sdiff_subset)),
          subset_union_left⟩, ?_⟩
        ext p
        have hp : p ∈ T → p ∉ A := fun h => (mem_sdiff.mp (ht h)).2
        simp only [mem_sdiff, mem_union]
        tauto
      · intro S hS
        exact hm (mem_powerset.mp (mem_filter.mp hS).1) (mem_filter.mp hS).2
    _ = _ := by rw [← mul_sum,bernoulliSubsetMass_sum,mul_one]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunFinitePopulation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-population upper sieve from an even truncation -/
namespace JointDickman
open Finset

 theorem brunTruncation_inter (P E : Finset ℕ) (m : ℕ) :
    brunTruncation (P ∩ E) m = ∑ D ∈ P.powerset.filter (fun D => D.card ≤ m),
      if D ⊆ E then (-1 : ℝ)^D.card else 0 := by
  classical
  rw [brunTruncation, ← sum_filter]
  apply sum_congr
  · ext D
    simp only [mem_filter, mem_powerset, subset_inter_iff]
    tauto
  · intros; rfl

 theorem brunMean_eq (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ) :
    brunMean P g r = ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2*r),
      (-1 : ℝ)^D.card * ∏ p ∈ D, g p := by
  classical
  have he (E : Finset ℕ) (hE : E ∈ P.powerset) : E = P ∩ E := by
    symm
    exact inter_eq_right.mpr (mem_powerset.mp hE)
  have hexp (E : Finset ℕ) (hE : E ∈ P.powerset) : brunTruncation E (2*r) =
      ∑ D ∈ P.powerset.filter (fun D => D.card ≤ 2*r),
        if D ⊆ E then (-1 : ℝ)^D.card else 0 :=
    (congrArg (fun T => brunTruncation T (2*r)) (he E hE)).trans (brunTruncation_inter P E (2*r))
  unfold brunMean
  rw [sum_congr rfl (fun E hE => congrArg (fun t => bernoulliSubsetMass P g E*t) (hexp E hE))]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro D hD
  calc
    _ = (-1 : ℝ)^D.card * ∑ E ∈ P.powerset,
        if D ⊆ E then bernoulliSubsetMass P g E else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro E _
      split_ifs <;> ring
    _ = _ := by rw [bernoulliSubsetMass_required P D g (mem_powerset.mp (mem_filter.mp hD).1)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlocks
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Products of even truncations over disjoint prime blocks -/
namespace JointDickman
open Finset

 theorem brunBlockChoices_mem {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (D : ι → Finset ℕ) : D ∈ brunBlockChoices P r ↔ ∀ i, D i ⊆ P i ∧ (D i).card ≤ 2*r i := by
  classical
  simp only [brunBlockChoices, Fintype.mem_piFinset, mem_filter, mem_powerset]

 theorem brunBlockSign_abs {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) : |brunBlockSign D| = 1 := by
  simp [brunBlockSign, abs_prod, abs_pow]

 theorem brunBlockUnion_inter {ι : Type*} [Fintype ι] (P D : ι → Finset ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (hD : ∀ i, D i ⊆ P i) (i : ι) :
    brunBlockUnion D ∩ P i = D i := by
  classical
  ext p
  simp only [mem_inter]
  constructor
  · rintro ⟨hp,hpi⟩
    obtain ⟨j,_,hpj⟩ := mem_biUnion.mp hp
    by_cases hji : j = i
    · simpa [hji] using hpj
    · exact False.elim (disjoint_left.mp (hP hji) (hD j hpj) hpi)
  · intro hp
    exact ⟨mem_biUnion.mpr ⟨i,mem_univ i,hp⟩,hD i hp⟩

 theorem brunBlockUnion_injOn {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Set.InjOn brunBlockUnion (brunBlockChoices P r : Set (ι → Finset ℕ)) := by
  intro D hD F hF he
  funext i
  rw [← brunBlockUnion_inter P D hP (fun i => (brunBlockChoices_mem P r D).mp hD i |>.1),
    ← brunBlockUnion_inter P F hP (fun i => (brunBlockChoices_mem P r F).mp hF i |>.1), he]

 theorem brunBlock_upper {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (E : Finset ℕ) : avoidsSelected (brunBlockUnion P) E ≤
      ∏ i, brunTruncation (P i ∩ E) (2*r i) := by
  classical
  by_cases hd : Disjoint (brunBlockUnion P) E
  · have he (i : ι) : P i ∩ E = ∅ := by
      apply disjoint_iff_inter_eq_empty.mp
      apply disjoint_left.mpr
      intro p hp hpe
      exact disjoint_left.mp hd (mem_biUnion.mpr ⟨i,mem_univ i,hp⟩) hpe
    simp [avoidsSelected,hd,he,brunTruncation_even]
  · simp only [avoidsSelected,hd,ite_false, if_false]
    exact prod_nonneg (fun i _ => brunTruncation_nonneg _ _)

 theorem brunBlock_expansion {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (E : Finset ℕ) :
    (∏ i, brunTruncation (P i ∩ E) (2*r i)) =
      ∑ D ∈ brunBlockChoices P r, if brunBlockUnion D ⊆ E then brunBlockSign D else 0 := by
  classical
  simp_rw [brunTruncation_inter]
  rw [prod_univ_sum]
  unfold brunBlockChoices
  apply sum_congr rfl
  intro D _
  rw [Fintype.prod_ite_zero]
  have he : (∀ i, D i ⊆ E) ↔ brunBlockUnion D ⊆ E := by
    simp only [brunBlockUnion, biUnion_subset, mem_univ, forall_true_left]
  simp only [he,brunBlockSign]

 theorem brunBlock_main {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (r : ι → ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (g : ℕ → ℝ) :
    (∑ D ∈ brunBlockChoices P r, brunBlockSign D * ∏ p ∈ brunBlockUnion D, g p) =
      ∏ i, brunMean (P i) g (r i) := by
  classical
  simp_rw [brunMean_eq]
  rw [prod_univ_sum]
  unfold brunBlockChoices
  apply sum_congr rfl
  intro D hD
  have hDP (i : ι) : D i ⊆ P i := ((brunBlockChoices_mem P r D).mp hD i).1
  have hd : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint D := by
    intro i _ j _ hij
    exact (hP hij).mono (hDP i) (hDP j)
  rw [brunBlockUnion, prod_biUnion hd, brunBlockSign, ← prod_mul_distrib]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveDimensionLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sieve dimension condition on logarithmic intervals -/
namespace JointDickman
open Finset

 theorem sieveDimension_log_interval {P Q : Finset ℕ} {g : ℕ → ℝ} {κ A z a b R : ℝ}
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hp : ∀ p ∈ P, 0 < (p:ℝ)) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hQP : Q ⊆ P)
    (ha : Real.log 2 ≤ a) (hab : a ≤ b) (hbz : b ≤ Real.log z) (hz : 0 < z)
    (hQ : ∀ p ∈ Q, a ≤ Real.log p ∧ Real.log p ≤ b)
    (hR : 0 < R) (hba : b ≤ R*a) :
    (∏ p ∈ Q, (1-g p)⁻¹) ≤ Real.exp (κ*Real.log R+A/Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 < a := h2.trans_le ha
  have hsub : Q ⊆ P.filter (fun p : ℕ => Real.exp a ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp b) := by
    intro p hq
    refine mem_filter.mpr ⟨hQP hq,?_,?_⟩
    · exact (Real.exp_le_exp.mpr (hQ p hq).1).trans_eq (Real.exp_log (hp p (hQP hq)))
    · exact (Real.exp_log (hp p (hQP hq))).symm.trans_le (Real.exp_le_exp.mpr (hQ p hq).2)
  calc
    _ ≤ ∏ p ∈ P.filter (fun p : ℕ => Real.exp a ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp b), (1-g p)⁻¹ := by
      apply prod_le_prod_of_subset_of_one_le hsub
      · intro p hq
        exact inv_nonneg.mpr (by linarith [(hg p (hQP hq)).2])
      · intro p hq _
        exact (one_le_inv₀ (by linarith [(hg p (mem_filter.mp hq).1).2])).mpr
          (by linarith [(hg p (mem_filter.mp hq).1).1])
    _ ≤ (Real.log (Real.exp b)/Real.log (Real.exp a))^κ *
        Real.exp (A/Real.log (Real.exp a)) := by
      apply hd
      · calc (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
             _ ≤ _ := Real.exp_le_exp.mpr ha
      · exact Real.exp_le_exp.mpr hab
      · exact (Real.exp_le_exp.mpr hbz).trans_eq (Real.exp_log hz)
    _ ≤ R^κ * Real.exp (A/Real.log 2) := by
      simp only [Real.log_exp]
      apply mul_le_mul
      · exact Real.rpow_le_rpow (div_nonneg (ha0.le.trans hab) ha0.le)
          ((div_le_iff₀ ha0).mpr hba) hκ
      · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hA h2 ha)
      · exact (Real.exp_pos _).le
      · exact Real.rpow_nonneg hR.le κ
    _ = _ := by rw [Real.rpow_def_of_pos hR, ← Real.exp_add]; congr 1; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunPrimeBlocks
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic logarithmic prime blocks -/
namespace JointDickman
open Finset

 theorem brunPrimeBlock_subset (P : Finset ℕ) (L : ℝ) (j : ℕ) : brunPrimeBlock P L j ⊆ P :=
  filter_subset _ _

 theorem brun_level_antitone {L : ℝ} (hL : 0 ≤ L) {i j : ℕ} (hij : i ≤ j) :
    L/(2:ℝ)^j ≤ L/(2:ℝ)^i := by
  exact div_le_div_of_nonneg_left hL (by positivity)
    (pow_le_pow_right₀ (by norm_num) hij)

 theorem brunPrimeBlock_disjoint (P : Finset ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Pairwise (fun i j : ℕ => Disjoint (brunPrimeBlock P L i) (brunPrimeBlock P L j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro p hpi hpj
  have hi := (mem_filter.mp hpi).2
  have hj := (mem_filter.mp hpj).2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (not_lt_of_ge (hj.2.trans (brun_level_antitone hL hlt))) hi.1
  · exact (not_lt_of_ge (hi.2.trans (brun_level_antitone hL hgt))) hj.1

 theorem brunPrimeBlocks_disjoint (P : Finset ℕ) {L : ℝ} (hL : 0 ≤ L) (N : ℕ) :
    Pairwise (fun i j : Fin N => Disjoint (brunPrimeBlock P L i.val) (brunPrimeBlock P L j.val)) := by
  intro i j hij
  exact brunPrimeBlock_disjoint P hL (fun h => hij (Fin.ext h))

 theorem brunPrimeBlocks_union (P : Finset ℕ) {L : ℝ} (hL : 0 ≤ L) (N : ℕ)
    (hN : ∀ p ∈ P, L/(2:ℝ)^N < Real.log p) :
    brunBlockUnion (fun j : Fin N => brunPrimeBlock P L j.val) =
      P.filter (fun p : ℕ => Real.log p ≤ L) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
    obtain ⟨hp,hlo,hhi⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hp,hhi.trans (by simpa using brun_level_antitone hL (Nat.zero_le i.val))⟩
  · intro hp
    obtain ⟨hp,hpL⟩ := mem_filter.mp hp
    have hex : ∃ n : ℕ, L/(2:ℝ)^n < Real.log p := ⟨N,hN p hp⟩
    let n := Nat.find hex
    have hn : L/(2:ℝ)^n < Real.log p := Nat.find_spec hex
    have hnN : n ≤ N := Nat.find_min' hex (hN p hp)
    have hn0 : n ≠ 0 := by
      intro he
      simp only [he,pow_zero,div_one] at hn
      exact (not_lt_of_ge hpL) hn
    have hj : n-1 < N := by omega
    have hjp : Real.log p ≤ L/(2:ℝ)^(n-1) := by
      exact le_of_not_gt (Nat.find_min hex (show n-1 < n by omega))
    apply mem_biUnion.mpr
    refine ⟨⟨n-1,hj⟩,mem_univ _,mem_filter.mpr ⟨hp,?_,hjp⟩⟩
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)] using hn

 theorem exists_brun_block_depth (L : ℝ) : ∃ N : ℕ, L/(2:ℝ)^N < Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (L/Real.log 2) (by norm_num : (1:ℝ)<2)
  refine ⟨N,(div_lt_iff₀ (by positivity)).mpr ?_⟩
  exact (div_lt_iff₀ hlog).mp hN |>.trans_eq (mul_comm _ _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlockDimension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The dimension hypothesis controls each logarithmic prime block -/
namespace JointDickman
open Finset

 theorem prime_log_two_le {p : ℕ} (hp : p.Prime) : Real.log 2 ≤ Real.log p :=
  Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)

 theorem brunPrimeBlock_inverse_bound {P : Finset ℕ} {g : ℕ → ℝ} {κ A z L : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) (hL : 0 ≤ L) (hLz : L ≤ Real.log z)
    (j : ℕ) :
    (∏ p ∈ brunPrimeBlock P L j, (1-g p)⁻¹) ≤ Real.exp (κ*Real.log 2+A/Real.log 2) := by
  let a := max (Real.log 2) (L/(2:ℝ)^(j+1))
  let b := max (Real.log 2) (L/(2:ℝ)^j)
  have ha0 : 0 ≤ a := (Real.log_pos (by norm_num : (1:ℝ)<2)).le.trans (le_max_left _ _)
  have hb : b ≤ Real.log z := max_le
    (Real.log_le_log (by norm_num) hz)
    ((brun_level_antitone hL (Nat.zero_le j)).trans (by simpa using hLz))
  have hba : b ≤ 2*a := by
    apply max_le
    · have := le_max_left (Real.log 2) (L/(2:ℝ)^(j+1))
      dsimp [a] at ha0 ⊢
      linarith
    · have hh : L/(2:ℝ)^j = 2*(L/(2:ℝ)^(j+1)) := by rw [pow_succ]; field_simp
      rw [hh]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  apply sieveDimension_log_interval hg (fun p hp => by exact_mod_cast (hP p hp).1.pos)
    hκ hA hd (brunPrimeBlock_subset P L j) (le_max_left _ _)
    (max_le_max le_rfl (brun_level_antitone hL (Nat.le_succ j))) hb (by linarith) _ (by norm_num) hba
  intro p hp
  have hh := mem_filter.mp hp
  exact ⟨max_le (prime_log_two_le (hP p hh.1).1) hh.2.1.le,hh.2.2.trans (le_max_right _ _)⟩

 theorem brunPrimeTail_inverse_bound {P : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) :
    (∏ p ∈ P \ P.filter (fun p : ℕ => Real.log p ≤ Real.log z/8), (1-g p)⁻¹) ≤
      Real.exp (κ*Real.log 8+A/Real.log 2) := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  apply sieveDimension_log_interval (a := max (Real.log 2) (Real.log z/8)) (b := Real.log z) (R := 8)
    hg (fun p hp => by exact_mod_cast (hP p hp).1.pos)
    hκ hA hd sdiff_subset (le_max_left _ _)
    (max_le (Real.log_le_log (by norm_num) hz) (by linarith)) le_rfl hz0 _ (by norm_num) _
  · intro p hp
    have hh := mem_sdiff.mp hp
    have hlo : Real.log z/8 ≤ Real.log p := by
      have hn : ¬ Real.log p ≤ Real.log z/8 := fun h => hh.2 (mem_filter.mpr ⟨hh.1,h⟩)
      linarith
    exact ⟨max_le (prime_log_two_le (hP p hh.1).1) hlo,
      Real.log_le_log (by exact_mod_cast (hP p hh.1).1.pos) (hP p hh.1).2⟩
  · have hh := le_max_right (Real.log 2) (Real.log z/8)
    linarith

 theorem sieve_survival_subset {P Q : Finset ℕ} {g : ℕ → ℝ} {C : ℝ}
    (hQP : Q ⊆ P) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hC : (∏ p ∈ P \ Q, (1-g p)⁻¹) ≤ C) :
    (∏ p ∈ Q, (1-g p)) ≤ C*(∏ p ∈ P, (1-g p)) := by
  have hpos : 0 < ∏ p ∈ P, (1-g p) := prod_pos (fun p hp => by linarith [(hg p hp).2])
  have hne : (∏ p ∈ P \ Q, (1-g p)) ≠ 0 :=
    (prod_pos (fun p hp => by linarith [(hg p (mem_sdiff.mp hp).1).2])).ne'
  have heq : (∏ p ∈ P, (1-g p))*(∏ p ∈ P \ Q, (1-g p)⁻¹) = ∏ p ∈ Q, (1-g p) := by
    rw [prod_inv_distrib, ← prod_sdiff hQP]
    field_simp
  calc
    _ = (∏ p ∈ P, (1-g p))*(∏ p ∈ P \ Q, (1-g p)⁻¹) := heq.symm
    _ ≤ (∏ p ∈ P, (1-g p))*C := mul_le_mul_of_nonneg_left hC hpos.le
    _ = _ := mul_comm _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlockMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative error for the mean of an even Brun truncation -/
namespace JointDickman
open Finset

 theorem sum_le_log_inverse_product (P : Finset ℕ) (g : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    (∑ p ∈ P, g p) ≤ Real.log (∏ p ∈ P, (1-g p)⁻¹) := by
  rw [Real.log_prod (fun p hp => inv_ne_zero (by linarith [(hg p hp).2]))]
  apply sum_le_sum
  intro p hp
  rw [Real.log_inv]
  have h := Real.log_le_sub_one_of_pos (show 0 < 1-g p by linarith [(hg p hp).2])
  linarith

 theorem brunMean_nonneg (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1) : 0 ≤ brunMean P g r := by
  classical
  apply sum_nonneg
  intro E hE
  exact mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hE) hg)
    (brunTruncation_nonneg E r)

 theorem brunMean_relative (P : Finset ℕ) (g : ℕ → ℝ) (r : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) {B : ℝ}
    (hB : (∏ p ∈ P, (1-g p)⁻¹) ≤ Real.exp B) :
    brunMean P g r ≤ (∏ p ∈ P, (1-g p)) * (1+Real.exp (4*B)/(4:ℝ)^r) := by
  have hpos : 0 < ∏ p ∈ P, (1-g p) := prod_pos (fun p hp => by linarith [(hg p hp).2])
  have hsum : (∑ p ∈ P, g p) ≤ B := by
    apply (sum_le_log_inverse_product P g hg).trans
    exact (Real.log_le_log (prod_pos (fun p hp => inv_pos.mpr (by linarith [(hg p hp).2]))) hB).trans_eq (Real.log_exp B)
  have hmul : 1 ≤ (∏ p ∈ P, (1-g p))*Real.exp B := by
    rw [prod_inv_distrib] at hB
    have h := mul_le_mul_of_nonneg_left hB hpos.le
    rwa [mul_inv_cancel₀ hpos.ne'] at h
  have he : Real.exp (3*B) ≤ (∏ p ∈ P, (1-g p))*Real.exp (4*B) := by
    have h := mul_le_mul_of_nonneg_right hmul (Real.exp_pos (3*B)).le
    rw [show 4*B = B+3*B by ring, Real.exp_add]
    nlinarith
  calc
    _ ≤ (∏ p ∈ P, (1-g p)) + Real.exp (3*B)/(4:ℝ)^r :=
      brunMean_le P g r (fun p hp => ⟨(hg p hp).1,(hg p hp).2.le⟩) hsum
    _ ≤ (∏ p ∈ P, (1-g p)) + ((∏ p ∈ P, (1-g p))*Real.exp (4*B))/(4:ℝ)^r :=
      add_le_add le_rfl (div_le_div_of_nonneg_right he (by positivity))
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunGeometric
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite geometric estimates for the block truncation -/
namespace JointDickman
open Finset

 theorem brun_weighted_geometric (N : ℕ) :
    (∑ j ∈ range N, ((j:ℝ)+1)/(2:ℝ)^j) = 4-2*((N:ℝ)+2)/(2:ℝ)^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ,ih,pow_succ]
    push_cast
    field_simp
    ring

 theorem brun_weighted_geometric_le (N : ℕ) :
    (∑ j ∈ range N, ((j:ℝ)+1)/(2:ℝ)^j) ≤ 4 := by
  rw [brun_weighted_geometric]
  have : 0 ≤ 2*((N:ℝ)+2)/(2:ℝ)^N := by positivity
  linarith

 theorem brun_geometric (N : ℕ) :
    (∑ j ∈ range N, 1/(4:ℝ)^(j+1)) = (1-1/(4:ℝ)^N)/3 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ,ih,pow_succ]
    field_simp
    ring

 theorem brun_geometric_le (N : ℕ) : (∑ j ∈ range N, 1/(4:ℝ)^(j+1)) ≤ 1 := by
  rw [brun_geometric]
  have : 0 ≤ 1/(4:ℝ)^N := by positivity
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlockMeanProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for the product of block means -/
namespace JointDickman
open Finset

 theorem brun_exp_product_bound {ι : Type*} [Fintype ι] (e : ι → ℝ)
    (he : ∀ i, 0 ≤ e i) : (∏ i, (1+e i)) ≤ Real.exp (∑ i, e i) := by
  calc
    _ ≤ ∏ i, Real.exp (e i) := Finset.prod_le_prod (fun i _ => by linarith [he i])
      (fun i _ => by simpa only [add_comm] using Real.add_one_le_exp (e i))
    _ = _ := (Real.exp_sum _ _).symm

 theorem brun_geometric_fin (N : ℕ) : (∑ i : Fin N, 1/(4:ℝ)^(i.val+1)) ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1/(4:ℝ)^(j+1)) N]
  exact brun_geometric_le N

 theorem brun_error_product (N : ℕ) (B : ℝ) :
    (∏ i : Fin N, (1+Real.exp (4*B)/(4:ℝ)^(i.val+1))) ≤ Real.exp (Real.exp (4*B)) := by
  have hs : (∑ i : Fin N, Real.exp (4*B)/(4:ℝ)^(i.val+1)) ≤ Real.exp (4*B) := by
    calc
      _ = Real.exp (4*B)*(∑ i : Fin N, 1/(4:ℝ)^(i.val+1)) := by rw [mul_sum]; simp only [mul_one_div]
      _ ≤ _ := mul_le_of_le_one_right (Real.exp_pos _).le (brun_geometric_fin N)
  exact (brun_exp_product_bound (fun i : Fin N => Real.exp (4*B)/(4:ℝ)^(i.val+1))
    (fun i => by positivity)).trans (Real.exp_le_exp.mpr hs)

 theorem brun_absence_product_nonneg {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (g : ℕ → ℝ) (hg : ∀ i p, p ∈ P i → g p ≤ 1) :
    0 ≤ ∏ i, ∏ p ∈ P i, (1-g p) := by
  apply prod_nonneg
  intro i _
  exact prod_nonneg (fun p hp => sub_nonneg.mpr (hg i p hp))

 theorem brunBlockMean_product_bound {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (g : ℕ → ℝ) (r : ι → ℕ) {B : ℝ}
    (hg : ∀ i p, p ∈ P i → 0 ≤ g p ∧ g p < 1)
    (hB : ∀ i, (∏ p ∈ P i, (1-g p)⁻¹) ≤ Real.exp B) :
    (∏ i, brunMean (P i) g (r i)) ≤
      (∏ i, ∏ p ∈ P i, (1-g p)) * ∏ i, (1+Real.exp (4*B)/(4:ℝ)^(r i)) := by
  rw [← prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i _
    exact brunMean_nonneg (P i) g (r i) (fun p hp => ⟨(hg i p hp).1,(hg i p hp).2.le⟩)
  · intro i _
    exact brunMean_relative (P i) g (r i) (hg i) (hB i)

 theorem brunBlockMean_product (N : ℕ) (P : Fin N → Finset ℕ) (g : ℕ → ℝ) {B : ℝ}
    (hg : ∀ i p, p ∈ P i → 0 ≤ g p ∧ g p < 1)
    (hB : ∀ i, (∏ p ∈ P i, (1-g p)⁻¹) ≤ Real.exp B) :
    (∏ i, brunMean (P i) g (i.val+1)) ≤
      (∏ i, ∏ p ∈ P i, (1-g p))*Real.exp (Real.exp (4*B)) := by
  exact (brunBlockMean_product_bound P g (fun i => i.val+1) hg hB).trans
    (mul_le_mul_of_nonneg_left (brun_error_product N B)
      (brun_absence_product_nonneg P g (fun i p hp => (hg i p hp).2.le)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunBlockPopulation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite block upper sieve with unit remainder coefficients -/
namespace JointDickman
open Finset

 theorem avoidsSelected_antitone {P Q E : Finset ℕ} (hQP : Q ⊆ P) :
    avoidsSelected P E ≤ avoidsSelected Q E := by
  classical
  by_cases h : Disjoint P E
  · simp [avoidsSelected,h,h.mono_left hQP]
  · simp only [avoidsSelected,h,ite_false, if_false]
    split_ifs <;> norm_num

 theorem brunBlock_population_sum {X ι : Type*} [Fintype X] [Fintype ι]
    (P : ι → Finset ℕ) (r : ι → ℕ) (E : X → Finset ℕ) (w : X → ℝ) :
    (∑ x, w x * ∏ i, brunTruncation (P i ∩ E x) (2*r i)) =
      ∑ D ∈ brunBlockChoices P r, brunBlockSign D * sieveIntersection E w (brunBlockUnion D) := by
  classical
  simp_rw [brunBlock_expansion,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  rw [sieveIntersection,mul_sum]
  apply sum_congr rfl
  intro x _
  split_ifs <;> ring

 theorem brunBlock_population_bound {X ι : Type*} [Fintype X] [Fintype ι]
    (Q : Finset ℕ) (P : ι → Finset ℕ) (r : ι → ℕ)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) (hPQ : ∀ i, P i ⊆ Q)
    (E : X → Finset ℕ) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (M z : ℝ) (g : ℕ → ℝ)
    (hcut : ∀ D ∈ brunBlockChoices P r, (∏ p ∈ brunBlockUnion D, p : ℕ) ≤ z) :
    (∑ x, w x * avoidsSelected Q (E x)) ≤
      M*(∏ i, brunMean (P i) g (r i)) +
      ∑ D ∈ Q.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z), |sieveRemainder E w M g D| := by
  classical
  have hUQ : brunBlockUnion P ⊆ Q := by
    intro p hp
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
    exact hPQ i hi
  calc
    _ ≤ ∑ x, w x * ∏ i, brunTruncation (P i ∩ E x) (2*r i) := by
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hw x)
      exact (avoidsSelected_antitone hUQ).trans (brunBlock_upper P r (E x))
    _ = M*(∏ i, brunMean (P i) g (r i)) +
        ∑ D ∈ brunBlockChoices P r, brunBlockSign D*sieveRemainder E w M g (brunBlockUnion D) := by
      rw [brunBlock_population_sum, ← brunBlock_main P r hP, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro D _
      rw [sieveRemainder]
      ring
    _ ≤ M*(∏ i, brunMean (P i) g (r i)) +
        ∑ D ∈ brunBlockChoices P r, |sieveRemainder E w M g (brunBlockUnion D)| := by
      apply add_le_add le_rfl
      apply sum_le_sum
      intro D _
      calc
        _ ≤ |brunBlockSign D*sieveRemainder E w M g (brunBlockUnion D)| := le_abs_self _
        _ = _ := by rw [abs_mul,brunBlockSign_abs,one_mul]
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply sum_le_sum_of_injOn brunBlockUnion (brunBlockUnion_injOn P r hP)
      · intro F hF
        obtain ⟨D,hD,rfl⟩ := mem_image.mp hF
        apply mem_filter.mpr
        refine ⟨mem_powerset.mpr ?_,hcut D hD⟩
        intro p hp
        obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
        exact hPQ i (((brunBlockChoices_mem P r D).mp hD i).1 hi)
      · intro D _
        exact le_rfl
      · intro D _ _
        exact abs_nonneg _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunProductCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every truncated block choice has product below the sifting bound -/
namespace JointDickman
open Finset

 theorem brunPrimeBlocks_cutoff (P : Finset ℕ) {L z : ℝ} (hL : 0 ≤ L)
    (hscale : 8*L ≤ Real.log z) (hz : 0 < z) (hp : ∀ p ∈ P, 0 < (p:ℝ)) (N : ℕ)
    (D : Fin N → Finset ℕ)
    (hD : D ∈ brunBlockChoices (fun j : Fin N => brunPrimeBlock P L j.val) (fun j => j.val+1)) :
    (∏ p ∈ brunBlockUnion D, p : ℕ) ≤ z := by
  classical
  have hchoice := (brunBlockChoices_mem _ _ D).mp hD
  have hd : (↑(univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint D := by
    intro i _ j _ hij
    exact (brunPrimeBlocks_disjoint P hL N hij).mono (hchoice i).1 (hchoice j).1
  have hDP (p : ℕ) (hpu : p ∈ brunBlockUnion D) : p ∈ P := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hpu
    exact brunPrimeBlock_subset P L i.val ((hchoice i).1 hi)
  have hpos : 0 < (∏ p ∈ brunBlockUnion D, (p:ℝ)) := prod_pos (fun p hpu => hp p (hDP p hpu))
  have heq : ((∏ p ∈ brunBlockUnion D, p : ℕ):ℝ) = ∏ p ∈ brunBlockUnion D, (p:ℝ) := by simp only [Nat.cast_prod]
  rw [heq]
  apply (Real.log_le_log_iff hpos hz).mp
  calc
    _ = ∑ i : Fin N, ∑ p ∈ D i, Real.log p := by
      rw [Real.log_prod (fun p hpu => (hp p (hDP p hpu)).ne'),brunBlockUnion,sum_biUnion hd]
    _ ≤ ∑ i : Fin N, (2*((i.val:ℝ)+1))*(L/(2:ℝ)^i.val) := by
      apply sum_le_sum
      intro i _
      calc
        _ ≤ ∑ _p ∈ D i, L/(2:ℝ)^i.val := by
          apply sum_le_sum
          intro p hpi
          exact (mem_filter.mp ((hchoice i).1 hpi)).2.2
        _ = (D i).card*(L/(2:ℝ)^i.val) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (hchoice i).2) (by positivity)
    _ = 2*L*(∑ j ∈ range N, ((j:ℝ)+1)/(2:ℝ)^j) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (2*((i:ℝ)+1))*(L/(2:ℝ)^i)) N,mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ 2*L*4 := mul_le_mul_of_nonneg_left (brun_weighted_geometric_le N) (by positivity)
    _ ≤ Real.log z := by linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BrunUpperSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An unconditional proof of the required upper sieve

Even inclusion-exclusion truncations on disjoint logarithmic prime blocks have
coefficients of absolute value one. Their orders grow with the block index,
so their errors are summable while every supported prime product stays below
`z`. This proves the finite-event consequence of Ford's Theorem 2.4 used here.
-/
namespace JointDickman
open Finset

 theorem brunPrimeBlocks_survival {P : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) (N : ℕ)
    (hN : ∀ p ∈ P, (Real.log z/8)/(2:ℝ)^N < Real.log p) :
    (∏ i : Fin N, ∏ p ∈ brunPrimeBlock P (Real.log z/8) i.val, (1-g p)) ≤
      Real.exp (κ*Real.log 8+A/Real.log 2)*(∏ p ∈ P, (1-g p)) := by
  have hL : 0 ≤ Real.log z/8 := div_nonneg (Real.log_nonneg (by linarith)) (by norm_num)
  have hdj : (↑(univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
      (fun i : Fin N => brunPrimeBlock P (Real.log z/8) i.val) := by
    intro i _ j _ hij
    exact brunPrimeBlocks_disjoint P hL N hij
  rw [← prod_biUnion hdj]
  change (∏ p ∈ brunBlockUnion (fun i : Fin N => brunPrimeBlock P (Real.log z/8) i.val), (1-g p)) ≤ _
  rw [brunPrimeBlocks_union P hL N hN]
  exact sieve_survival_subset (filter_subset _ _) hg (brunPrimeTail_inverse_bound hP hg hκ hA hd hz)

 theorem brunPrimeBlocks_mean_bound {P : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) (N : ℕ)
    (hN : ∀ p ∈ P, (Real.log z/8)/(2:ℝ)^N < Real.log p) :
    (∏ i : Fin N, brunMean (brunPrimeBlock P (Real.log z/8) i.val) g (i.val+1)) ≤
      brunSieveConstant κ A*(∏ p ∈ P, (1-g p)) := by
  have hlog : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hL : 0 ≤ Real.log z/8 := by positivity
  have hLz : Real.log z/8 ≤ Real.log z := by linarith
  calc
    _ ≤ (∏ i : Fin N, ∏ p ∈ brunPrimeBlock P (Real.log z/8) i.val, (1-g p))*
        Real.exp (Real.exp (4*(κ*Real.log 2+A/Real.log 2))) := by
      apply brunBlockMean_product
      · intro i p hp
        exact hg p (brunPrimeBlock_subset _ _ _ hp)
      · intro i
        exact brunPrimeBlock_inverse_bound hP hg hκ hA hd hz hL hLz i.val
    _ ≤ (Real.exp (κ*Real.log 8+A/Real.log 2)*(∏ p ∈ P, (1-g p)))*
        Real.exp (Real.exp (4*(κ*Real.log 2+A/Real.log 2))) :=
      mul_le_mul_of_nonneg_right (brunPrimeBlocks_survival hP hg hκ hA hd hz N hN) (Real.exp_pos _).le
    _ = _ := by
      conv_rhs => rw [brunSieveConstant,Real.exp_add]
      ring

 theorem fordUpperSieveInput : PublishedInputs.FordUpperSieveInput := by
  intro κ A hκ hA
  refine ⟨brunSieveConstant κ A,Real.exp_pos _,?_⟩
  intro X _ P E w M z g hz hM hw hP hg hd
  have hlog : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hL : 0 ≤ Real.log z/8 := by positivity
  obtain ⟨N,hN⟩ := exists_brun_block_depth (Real.log z/8)
  have hNP : ∀ p ∈ P, (Real.log z/8)/(2:ℝ)^N < Real.log p :=
    fun p hp => hN.trans_le (prime_log_two_le (hP p hp).1)
  have hpop := brunBlock_population_bound P (fun i : Fin N => brunPrimeBlock P (Real.log z/8) i.val)
    (fun i => i.val+1) (brunPrimeBlocks_disjoint P hL N)
    (fun i => brunPrimeBlock_subset _ _ _) E w hw M z g
    (fun D hD => brunPrimeBlocks_cutoff P hL (by linarith) (by linarith)
      (fun p hp => by exact_mod_cast (hP p hp).1.pos) N D hD)
  apply hpop.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ M*(brunSieveConstant κ A*(∏ p ∈ P, (1-g p))) :=
      mul_le_mul_of_nonneg_left (brunPrimeBlocks_mean_bound hP hg hκ.le hA hd hz N hNP) hM
    _ = _ := by ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeNormalizer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the independent prime-product law

The logarithm of the all-absent probability is its linear prime sum up to
a reciprocal-square error. Mertens' second theorem therefore determines
the normalization for a moving lower and upper cutoff.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Both endpoint Mertens remainders control the prime-interval remainder. -/
theorem prime_interval_mertens_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : ℝ, 2 ≤ X → X ≤ Y →
      |(∑ p ∈ largePrimeSet Y X, 1 / (p : ℝ)) -
        (Real.log (Real.log Y) - Real.log (Real.log X))| ≤
        C / Real.log Y + C / Real.log X := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨C, hC, fun X Y hX hXY => ?_⟩
  have hY : 2 ≤ Y := hX.trans hXY
  have h₁ : |primeReciprocalSum X - Real.log (Real.log X) - M| ≤ C / Real.log X := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound X hX
  have h₂ : |primeReciprocalSum Y - Real.log (Real.log Y) - M| ≤ C / Real.log Y := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound Y hY
  rw [largePrimeSet_reciprocal_eq (by linarith) hXY]
  calc
    _ = |(primeReciprocalSum Y - Real.log (Real.log Y) - M) -
        (primeReciprocalSum X - Real.log (Real.log X) - M)| := by congr 1; ring
    _ ≤ |primeReciprocalSum Y - Real.log (Real.log Y) - M| +
        |primeReciprocalSum X - Real.log (Real.log X) - M| := abs_sub _ _
    _ ≤ _ := add_le_add h₂ h₁

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveDimension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sieve dimension from Mertens' estimate -/

namespace JointDickman

open Finset

/-- The possible prime at the lower endpoint costs at most `1 / log y`. -/
theorem closed_prime_interval_sum_le
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : Finset ℕ) (y v : ℝ),
      (∀ p ∈ P, p.Prime) → 2 ≤ y → y ≤ v →
      (∑ p ∈ P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v),
        1 / (p : ℝ)) ≤ Real.log (Real.log v / Real.log y) + K / Real.log y := by
  obtain ⟨C, hC, hbound⟩ := prime_interval_mertens_error hM
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro P y v hP hy hyv
  have hy0 : 0 ≤ y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlv : 0 < Real.log v := Real.log_pos (by linarith)
  have hlogle : Real.log y ≤ Real.log v := Real.log_le_log (by linarith) hyv
  have hnle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hln : Real.log y ≤ (⌊y⌋₊ : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < y by linarith), Nat.lt_floor_add_one y]
  have hnpos : (0 : ℝ) < ⌊y⌋₊ := hly.trans_le hln
  have hnot : ⌊y⌋₊ ∉ largePrimeSet v y := by
    intro hn
    exact (not_lt_of_ge hnle) (mem_filter.mp hn).2
  have hsub : P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v) ⊆
      insert ⌊y⌋₊ (largePrimeSet v y) := by
    intro p hp
    obtain ⟨hpP, hpy, hpv⟩ := mem_filter.mp hp
    by_cases hlt : y < (p : ℝ)
    · apply mem_insert_of_mem
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpv, hP p hpP⟩, hlt⟩
    · have heq : (p : ℝ) = y := le_antisymm (le_of_not_gt hlt) hpy
      apply mem_insert.mpr
      left
      rw [← heq, Nat.floor_natCast]
  calc
    _ ≤ ∑ p ∈ insert ⌊y⌋₊ (largePrimeSet v y), 1 / (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = 1 / (⌊y⌋₊ : ℝ) + ∑ p ∈ largePrimeSet v y, 1 / (p : ℝ) := sum_insert hnot
    _ ≤ 1 / Real.log y +
        ((Real.log (Real.log v) - Real.log (Real.log y)) +
          (C / Real.log v + C / Real.log y)) := by
      apply add_le_add
      · exact one_div_le_one_div_of_le hly hln
      · linarith [(abs_le.mp (hbound y v hy hyv)).2]
    _ ≤ Real.log (Real.log v / Real.log y) + (2 * C + 1) / Real.log y := by
      rw [Real.log_div hlv.ne' hly.ne']
      have hd := div_le_div_of_nonneg_left hC hly hlogle
      simp only [add_div, mul_div_assoc]
      linarith

/-- A fixed number of forbidden classes per prime has bounded dimension.
The dimension `2*k` is deliberately sufficient, rather than optimal. -/
theorem sieveDimension_of_reciprocal_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℝ} (hk : 0 < k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : Finset ℕ) (g : ℕ → ℝ) (z : ℝ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ)) →
      SieveDimension P g (2 * k) A z := by
  obtain ⟨K, hK, hbound⟩ := closed_prime_interval_sum_le hM
  refine ⟨2 * k * K, by positivity, ?_⟩
  intro P g z hP hg y v hy hyv _
  let S := P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v)
  have hsub : S ⊆ P := filter_subset _ _
  have hsum : (∑ p ∈ S, g p) ≤ k * ∑ p ∈ S, 1 / (p : ℝ) := by
    rw [mul_sum]
    exact sum_le_sum (fun p hp => by simpa only [mul_one_div] using (hg p (hsub hp)).2.2)
  calc
    _ ≤ Real.exp (2 * ∑ p ∈ S, g p) :=
      inverse_product_le_exp S g (fun p hp => ⟨(hg p (hsub hp)).1, (hg p (hsub hp)).2.1⟩)
    _ ≤ Real.exp (2 * k *
        (Real.log (Real.log v / Real.log y) + K / Real.log y)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (hbound P y v hP hy hyv) hk.le]
    _ = (Real.log v / Real.log y) ^ (2 * k) *
        Real.exp ((2 * k * K) / Real.log y) := by
      have hp : 0 < Real.log v / Real.log y :=
        div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
      rw [Real.rpow_def_of_pos hp, ← Real.exp_add]
      congr 1
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPrimeSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The proved sieve applied to nonnegative Mellin square weights -/
namespace JointDickman
open Finset
open scoped Classical

lemma sieve_level_card_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Z : ℕ) :
    (P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z)).card ≤ Z+1 := by
  rw [← card_range (Z+1)]
  apply card_le_card_of_injOn (fun D => ∏ p ∈ D, p)
  · intro D hD
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2)
  · intro D hD E hE hDE
    exact primeProduct_injective hP (mem_powerset.mp (mem_filter.mp hD).1)
      (mem_powerset.mp (mem_filter.mp hE).1) hDE

lemma primeDivisorEvents_prime {P : Finset ℕ} {Z n : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Z) (hn : n.Prime) (hZn : Z < n) :
    primeDivisorEvents P n = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpP, hpn⟩ := mem_filter.mp hp
  have he := (Nat.prime_dvd_prime_iff_eq (hP p hpP).1 hn).mp hpn
  have := (hP p hpP).2
  omega

/-- Positive weights on primes larger than the sieve level. The error is
the literal sum of residue-class discrepancies of the given weight. -/
theorem prime_weighted_sieve : ∃ C : ℝ, 0 < C ∧
    ∀ (K Z : ℕ) (P Q : Finset ℕ) (w : ℕ → ℝ) (M R : ℝ),
      2 ≤ Z → 0 ≤ M → 0 ≤ R →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z) →
      Q ⊆ Icc 1 K → (∀ q ∈ Q, q.Prime ∧ Z < q) →
      (∀ n ∈ Icc 1 K, 0 ≤ w n) →
      (∀ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z),
        |sieveRemainder (fun n : Icc 1 K => primeDivisorEvents P n)
          (fun n => w n) M (fun p => 1/(p : ℝ)) D| ≤ R) →
      (∑ q ∈ Q, w q) ≤ C*M*(∏ p ∈ P, (1-1/(p : ℝ))) + (Z+1:ℕ)*R := by
  obtain ⟨A, hA, hdim⟩ := sieveDimension_of_reciprocal_bound primeReciprocalMertensInput
    (k := 1) (by norm_num)
  obtain ⟨C, hC, hbound⟩ := fordUpperSieveInput 2 A (by norm_num) hA
  refine ⟨C, hC, ?_⟩
  intro K Z P Q w M R hZ hM hR hP hQ hQprime hw herr
  have hg : ∀ p ∈ P, 0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1/2 ∧
      1/(p : ℝ) ≤ 1/(p : ℝ) := by
    intro p hp
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hP p hp).1.two_le
    exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) hp2, le_rfl⟩
  have hs := hbound (Icc 1 K) P (fun n => primeDivisorEvents P n)
    (fun n => w n) M Z (fun p => 1/(p : ℝ)) (by exact_mod_cast hZ) hM
    (fun n => hw n n.property)
    (fun p hp => ⟨(hP p hp).1, by exact_mod_cast (hP p hp).2⟩)
    (fun p hp => ⟨(hg p hp).1, lt_of_le_of_lt (hg p hp).2.1 (by norm_num)⟩)
    (by simpa only [mul_one] using hdim P _ Z (fun p hp => (hP p hp).1) hg)
  simp only [Nat.cast_le] at hs
  have havoid (q : ℕ) (hq : q ∈ Q) : avoidsSelected P (primeDivisorEvents P q) = 1 := by
    rw [primeDivisorEvents_prime hP (hQprime q hq).1 (hQprime q hq).2]
    simp [avoidsSelected]
  have hleft : (∑ q ∈ Q, w q) ≤
      ∑ n : Icc 1 K, w n*avoidsSelected P (primeDivisorEvents P n) := by
    rw [(Icc 1 K).sum_coe_sort (fun n : ℕ => w n*avoidsSelected P (primeDivisorEvents P n))]
    calc
      _ = ∑ q ∈ Q, w q*avoidsSelected P (primeDivisorEvents P q) := by
        apply sum_congr rfl
        intro q hq
        rw [havoid q hq, mul_one]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hQ (by
        intro n hn _
        exact mul_nonneg (hw n hn) (by unfold avoidsSelected; split_ifs <;> norm_num))
  apply hleft.trans (hs.trans _)
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z), R :=
      sum_le_sum herr
    _ = ((P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z)).card : ℝ)*R := by simp
    _ ≤ _ := by
      have hh : ((P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z)).card : ℝ) ≤ (Z+1 : ℕ) := by
        exact_mod_cast sieve_level_card_le P (fun p hp => (hP p hp).1) Z
      exact mul_le_mul_of_nonneg_right hh hR

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquareKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential majorant for Dirichlet-polynomial mean squares

This is the elementary kernel behind the mean-value estimate used at the
start of corrected MRT, Appendix A, Proposition A.3.  Its Fourier transform
has quadratic decay, so the ensuing row sum loses no logarithm.
-/

namespace TwoPointCorrelations

open Complex MeasureTheory Set

lemma mrtMeanSquareKernel_right {T : ℝ} (ω : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonneg ht,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_left {T : ℝ} (ω : ℝ) {t : ℝ} (ht : t ≤ 0) :
    mrtMeanSquareKernel T ω t =
      Complex.exp ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
  simp only [mrtMeanSquareKernel, abs_of_nonpos ht, neg_neg,
    Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_one]
  congr 1
  ring

lemma mrtMeanSquareKernel_integrable {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    Integrable (mrtMeanSquareKernel T ω) := by
  have hr : IntegrableOn (mrtMeanSquareKernel T ω) (Ioi 0) := by
    apply (integrableOn_exp_mul_complex_Ioi
      (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0).congr_fun
        (fun t ht => ?_) measurableSet_Ioi
    simpa using (mrtMeanSquareKernel_right ω ht.le).symm
  have hl : IntegrableOn (mrtMeanSquareKernel T ω) (Iic 0) := by
    apply (integrableOn_exp_mul_complex_Iic
      (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
      (by simpa using one_div_pos.mpr hT) 0).congr_fun
        (fun t ht => ?_) measurableSet_Iic
    exact (mrtMeanSquareKernel_left ω ht).symm
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

/-- Exact quadratic-decay Fourier transform, without an asymptotic constant. -/
theorem integral_mrtMeanSquareKernel {T : ℝ} (hT : 0 < T) (ω : ℝ) :
    (∫ t : ℝ, mrtMeanSquareKernel T ω t) =
      ((2 * T / (1 + T ^ 2 * ω ^ 2) : ℝ) : ℂ) := by
  have hi := mrtMeanSquareKernel_integrable hT ω
  have hr : (∫ t in Ioi (0 : ℝ), mrtMeanSquareKernel T ω t) =
      -1 / (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), Complex.exp
          ((((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        simpa using mrtMeanSquareKernel_right ω ht.le
      _ = _ := by
        simpa using integral_exp_mul_complex_Ioi
          (a := ((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using neg_lt_zero.mpr (one_div_pos.mpr hT)) 0
  have hl : (∫ t in Iic (0 : ℝ), mrtMeanSquareKernel T ω t) =
      1 / (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) := by
    calc
      _ = ∫ t in Iic (0 : ℝ), Complex.exp
          ((((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        exact mrtMeanSquareKernel_left ω ht
      _ = _ := by
        simpa using integral_exp_mul_complex_Iic
          (a := ((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I)
          (by simpa using one_div_pos.mpr hT) 0
  rw [← integral_add_compl measurableSet_Iic hi, compl_Iic, hl, hr]
  have hTp : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hp : (((1 / T : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : (1 / T : ℝ) = 0 := by simpa using this
    exact (one_div_pos.mpr hT).ne' he
  have hm : (((-(1 / T) : ℝ) : ℂ) + (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    have he : -(1 / T : ℝ) = 0 := by simpa using this
    exact (neg_lt_zero.mpr (one_div_pos.mpr hT)).ne he
  have hp1 : (1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hm1 : (-1 + (T : ℂ) * (ω : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hd : (1 + T ^ 2 * ω ^ 2 : ℝ) ≠ 0 := by positivity
  have hdc : (1 + (T : ℂ) ^ 2 * (ω : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp
  ring_nf
  field_simp [hp1, hm1, hdc]
  ring_nf
  simp only [Complex.I_sq]
  ring

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMeanSquare
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Dirichlet-polynomial mean squares, using the integrable
exponential majorant and its exact quadratic-decay Fourier transform. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Finset Set
open scoped BigOperators ComplexConjugate

lemma mrt_phase_pair (x y : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) *
        conj (Complex.exp ((y : ℂ) * Complex.I)) =
      Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I, ofReal_sub]
  ring

lemma mrt_weighted_square_expansion {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (T t : ℝ) :
    ((Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S,
        (a i * conj (a j)) * mrtMeanSquareKernel T (freq i - freq j) t := by
  rw [ofReal_mul, ofReal_pow, ← Complex.mul_conj']
  simp only [mrtExponentialPolynomial, map_sum, sum_mul, mul_sum]
  rw [sum_comm (s := S) (t := S)]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [map_mul]
  have hp := mrt_phase_pair (freq i * t) (freq j * t)
  have he : (((freq i - freq j) * t : ℝ) : ℂ) * Complex.I =
      ((freq i * t - freq j * t : ℝ) : ℂ) * Complex.I := by congr 1; push_cast <;> ring
  dsimp only [mrtMeanSquareKernel]
  rw [he, ← hp]
  ring

/-- Exact finite mean-square formula.  This identity is valid for arbitrary
real frequencies; separation is needed only for the subsequent bound. -/
theorem mrt_weighted_mean_square {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, Real.exp (-|t| / T) * ‖mrtExponentialPolynomial S a freq t‖ ^ 2) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)).re *
        (2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2)) := by
  have he : (∫ t : ℝ, ((Real.exp (-|t| / T) *
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ i ∈ S, ∑ j ∈ S, (a i * conj (a j)) *
        ((2 * T / (1 + T ^ 2 * (freq i - freq j) ^ 2) : ℝ) : ℂ) := by
    simp_rw [mrt_weighted_square_expansion]
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply sum_congr rfl
        intro j _
        rw [integral_const_mul, integral_mrtMeanSquareKernel hT]
      · intro j _
        exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
    · intro i _
      apply integrable_finsetSum
      intro j _
      exact (mrtMeanSquareKernel_integrable hT (freq i - freq j)).const_mul _
  rw [integral_complex_ofReal] at he
  have hr := congrArg Complex.re he
  simpa only [ofReal_re, Complex.re_sum, mul_re, ofReal_im, mul_zero, sub_zero] using hr

/-- A symmetric positive kernel is bounded on the squared norm by its
largest row sum.  The numerical row estimate is proved separately. -/
lemma mrt_symmetric_row_bound {ι : Type*} (S : Finset ι) (K : ι → ι → ℝ)
    (v : ι → ℝ) (C : ℝ) (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, K i j ≤ C) :
    (∑ i ∈ S, ∑ j ∈ S, v i * v j * K i j) ≤ C * ∑ i ∈ S, (v i) ^ 2 := by
  have he : (∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j) =
      ∑ i ∈ S, (v i) ^ 2 * ∑ j ∈ S, K i j := by
    simp only [add_div, add_mul, sum_add_distrib]
    rw [sum_comm (s := S) (t := S) (f := fun i j => (v j) ^ 2 / 2 * K i j)]
    simp only [← mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hk : (∑ j ∈ S, K j i) = ∑ j ∈ S, K i j :=
      sum_congr rfl fun j hj => hsymm j hj i hi
    rw [hk]
    ring
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ((v i) ^ 2 + (v j) ^ 2) / 2 * K i j := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ (hK i hi j hj)
      nlinarith [sq_nonneg (v i - v j)]
    _ = _ := he
    _ ≤ ∑ i ∈ S, (v i) ^ 2 * C := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
    _ = _ := by rw [← sum_mul, mul_comm]

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSampleDuality
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite duality for sampled Mellin polynomials

Finite duality reduces sparse-prime sampling to a row bound for the
weighted Mellin kernel.
-/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped ComplexConjugate

lemma norm_finite_complex_pairing_sq {ι : Type*} (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ n ∈ S, a n*b n‖^2 ≤
      (∑ n ∈ S, ‖a n‖^2)*(∑ n ∈ S, ‖b n‖^2) := by
  have h := norm_sum_le S (fun n => a n*b n)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (sum_mul_sq_le_sq_mul_sq S (fun n => ‖a n‖) (fun n => ‖b n‖))

/-- Finite transpose duality, with no compactness or limiting argument. -/
theorem mellin_samples_of_dual (P : Finset ℕ) (S : Finset ℝ)
    (a : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hdual : ∀ b : ℝ → ℂ,
      (∑ n ∈ P, ‖∑ t ∈ S, b t *
        Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) ≤
          C*∑ t ∈ S, ‖b t‖^2) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun n => -Real.log (n : ℝ)) t‖^2) ≤
      C*∑ n ∈ P, ‖a n‖^2 := by
  let q := mrtExponentialPolynomial P a (fun n => -Real.log (n : ℝ))
  let d : ℕ → ℂ := fun n => ∑ t ∈ S, conj (q t)*
    Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)
  let E : ℝ := ∑ t ∈ S, ‖q t‖^2
  let F : ℝ := ∑ n ∈ P, ‖a n‖^2
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  have hF : 0 ≤ F := sum_nonneg fun _ _ => sq_nonneg _
  have hpair : (∑ n ∈ P, a n*d n) = (E : ℂ) := by
    dsimp only [d, E]
    simp only [mul_sum, Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.mul_conj']
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    dsimp only [q, mrtExponentialPolynomial]
    rw [sum_mul]
    apply sum_congr rfl
    intro n _
    ring
  have hD : (∑ n ∈ P, ‖d n‖^2) ≤ C*E := by
    simpa only [d, E, Complex.norm_conj] using hdual (fun t => conj (q t))
  have hsq := norm_finite_complex_pairing_sq P a d
  rw [hpair, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hsq
  change E^2 ≤ F*∑ n ∈ P, ‖d n‖^2 at hsq
  have hh := hsq.trans (mul_le_mul_of_nonneg_left hD hF)
  change E ≤ C*F
  by_cases hz : E = 0
  · rw [hz]
    positivity
  · have hp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
    nlinarith

lemma mellin_weighted_dual_identity (P : Finset ℕ) (S : Finset ℝ)
    (w : ℕ → ℝ) (b : ℝ → ℂ) :
    (∑ n ∈ P, w n*‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) =
      ∑ t ∈ S, ∑ u ∈ S,
        ((b t*conj (b u))*mellinSampleKernel P w (t-u)).re := by
  have he : ((∑ n ∈ P, w n*‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2 : ℝ) : ℂ) =
      ∑ t ∈ S, ∑ u ∈ S,
        (b t*conj (b u))*mellinSampleKernel P w (t-u) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
      ← Complex.mul_conj', map_sum, map_mul, sum_mul, mul_sum]
    rw [sum_comm]
    conv_lhs => arg 2; ext t; rw [sum_comm]
    rw [sum_comm (s := S) (t := S)]
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro u _
    unfold mellinSampleKernel
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    have hh := mrt_phase_pair (-Real.log (n : ℝ)*t) (-Real.log (n : ℝ)*u)
    rw [show -Real.log (n : ℝ)*t - -Real.log (n : ℝ)*u =
      -Real.log (n : ℝ)*(t-u) by ring] at hh
    rw [← hh]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, mul_assoc, mul_comm, mul_left_comm]
  simpa only [Complex.ofReal_re, Complex.re_sum] using congrArg Complex.re he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive smooth weight for sparse prime sampling

The weight is at least 1/8 on `[N,2N]` and its Mellin transform has
quadratic decay. This provides the majorant used by the finite sieve.
-/
namespace JointDickman
open MeasureTheory TwoPointCorrelations

lemma mellinSieveWeight_nonneg {N x : ℝ} (hN : 0 ≤ N) (hx : 0 ≤ x) :
    0 ≤ mellinSieveWeight N x := by
  unfold mellinSieveWeight
  positivity

lemma mellinSieveWeight_left {N x : ℝ} (hN : 0 < N) (hx : 0 < x) (hxN : x ≤ N) :
    mellinSieveWeight N x = x/N := by
  have hl := Real.log_le_log hx hxN
  have he : Real.exp (2*(Real.log x-Real.log N)) = (x/N)^2 := by
    rw [← Real.log_div hx.ne' hN.ne', show Real.exp (2*Real.log (x/N)) = (Real.exp (Real.log (x/N)))^2 by simpa using Real.exp_nat_mul (Real.log (x/N)) 2, Real.exp_log (div_pos hx hN)]
  unfold mellinSieveWeight
  rw [abs_of_nonpos (sub_nonpos.mpr hl), show -2* -(Real.log x-Real.log N) =
    2*(Real.log x-Real.log N) by ring, he]
  field_simp

lemma mellinSieveWeight_right {N x : ℝ} (hN : 0 < N) (hxN : N ≤ x) :
    mellinSieveWeight N x = (N/x)^3 := by
  have hx : 0 < x := hN.trans_le hxN
  have hl := Real.log_le_log hN hxN
  have he : Real.exp (-2*(Real.log x-Real.log N)) = (N/x)^2 := by
    rw [show -2*(Real.log x-Real.log N) = 2*(Real.log N-Real.log x) by ring,
      ← Real.log_div hN.ne' hx.ne', show Real.exp (2*Real.log (N/x)) = (Real.exp (Real.log (N/x)))^2 by simpa using Real.exp_nat_mul (Real.log (N/x)) 2, Real.exp_log (div_pos hN hx)]
  unfold mellinSieveWeight
  rw [abs_of_nonneg (sub_nonneg.mpr hl), he]
  ring

lemma mellinSieveWeight_interval {N x : ℝ} (hN : 0 < N) (hx : N ≤ x) (hx2 : x ≤ 2*N) :
    (1/8 : ℝ) ≤ mellinSieveWeight N x := by
  rw [mellinSieveWeight_right hN hx]
  have hxp : 0 < x := hN.trans_le hx
  have hr : (1/2 : ℝ) ≤ N/x := (le_div_iff₀ hxp).mpr (by linarith)
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hr 3
  norm_num at hh ⊢
  exact hh

lemma mellinSieveAtom_log (N t x : ℝ) :
    mellinSieveAtom N t x = x⁻¹ •
      ((N : ℂ)*mrtMeanSquareKernel (1/2) (-t) (Real.log x-Real.log N)) := by
  change _ = ((x⁻¹ : ℝ) : ℂ)*_
  unfold mellinSieveAtom mellinSieveWeight mrtMeanSquareKernel
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
  norm_num
  ring_nf

/-- The positive weight has an exact quadratic-decay Mellin transform. -/
theorem integral_mellinSieveAtom (N t : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), mellinSieveAtom N t x) =
      ((4*N/(4+t^2) : ℝ) : ℂ) := by
  simp_rw [mellinSieveAtom_log]
  rw [integral_comp_log_Ioi_zero (fun v =>
    (N : ℂ)*mrtMeanSquareKernel (1/2) (-t) (v-Real.log N)), integral_const_mul]
  have he := integral_add_right_eq_self (μ := volume)
    (fun v : ℝ => mrtMeanSquareKernel (1/2) (-t) v) (-Real.log N)
  change (∫ v : ℝ, mrtMeanSquareKernel (1/2) (-t) (v-Real.log N)) = _ at he
  rw [he, integral_mrtMeanSquareKernel (by norm_num : (0:ℝ) < 1/2)]
  push_cast
  field_simp
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTSampling
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling a differentiable function at separated points.  Unit
intervals give a finite Sobolev estimate, which will be applied to the
prime-polynomial powers already expanded into Dirichlet coefficients. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped RealInnerProductSpace

lemma mrt_value_le_unit_integral (F F' B : ℝ → ℝ)
    (hF : Continuous F) (hF' : ∀ t, HasDerivAt F (F' t) t)
    (hB : Continuous B) (hB0 : ∀ t, 0 ≤ B t)
    (hd : ∀ t, |F' t| ≤ B t) (a : ℝ) :
    F a ≤ ∫ t in a..(a + 1), F t + B t := by
  have hiB : IntervalIntegrable B volume a (a + 1) := hB.intervalIntegrable a (a + 1)
  have hp (y : ℝ) (hy : y ∈ Icc a (a + 1)) :
      F a ≤ F y + ∫ t in a..(a + 1), B t := by
    have hdiff : ‖F y - F a‖ ≤ ∫ t in a..y, B t := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le hy.1 hF.continuousOn
        (fun t _ => (hF' t).differentiableAt.differentiableWithinAt)
      · exact Filter.Eventually.of_forall fun t _ => by
          rw [(hF' t).deriv, Real.norm_eq_abs]
          exact hd t
      · exact hB.intervalIntegrable a y
    have hm : (∫ t in a..y, B t) ≤ ∫ t in a..(a + 1), B t :=
      intervalIntegral.integral_mono_interval le_rfl hy.1 hy.2
        (Filter.Eventually.of_forall hB0) hiB
    have he : F a - F y ≤ ‖F y - F a‖ := by
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact le_abs_self _
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + 1)
    (continuous_const.intervalIntegrable a (a + 1))
    ((hF.add continuous_const).intervalIntegrable a (a + 1)) hp
  change (∫ t in a..(a + 1), F a) ≤
    ∫ t in a..(a + 1), F t + (∫ u in a..(a + 1), B u) at hi
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hF.intervalIntegrable a (a + 1))
    (continuous_const.intervalIntegrable a (a + 1)), intervalIntegral.integral_const] at hi
  have hlen : a + 1 - a = 1 := by ring
  simp only [hlen, one_smul] at hi
  rw [intervalIntegral.integral_add (hF.intervalIntegrable a (a + 1)) hiB]
  exact hi

lemma mrt_unit_intervals_disjoint (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    Set.Pairwise (S : Set ℝ) (fun x y => Disjoint (Set.Ioc x (x + 1))
      (Set.Ioc y (y + 1))) := by
  intro x hx y hy hne
  have h := hsep x hx y hy hne
  by_cases hxy : x ≤ y
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at h
    exact Ioc_disjoint_Ioc_of_le (by linarith)
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))] at h
    exact (Ioc_disjoint_Ioc_of_le (by linarith : y + 1 ≤ x)).symm

lemma mrt_sum_unit_integrals_le (S : Finset ℝ) (G : ℝ → ℝ)
    (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (a b : ℝ) (hab : a ≤ b)
    (hS : ∀ x ∈ S, a ≤ x ∧ x + 1 ≤ b) :
    (∑ x ∈ S, ∫ t in x..(x + 1), G t) ≤ ∫ t in a..b, G t := by
  have hint (x : ℝ) : (∫ t in x..(x + 1), G t) = ∫ t in Ioc x (x + 1), G t :=
    intervalIntegral.integral_of_le (by linarith)
  simp_rw [hint]
  rw [← integral_biUnion_finset S (fun _ _ => measurableSet_Ioc)
    (mrt_unit_intervals_disjoint S hsep)
    (fun x _ => (hG.intervalIntegrable x (x + 1)).1),
    intervalIntegral.integral_of_le hab]
  apply setIntegral_mono_set (hG.intervalIntegrable a b).1
    (Filter.Eventually.of_forall hG0)
  exact Filter.Eventually.of_forall fun t ht => by
    obtain ⟨x, hx, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨lt_of_le_of_lt (hS x hx).1 ht.1, ht.2.trans (hS x hx).2⟩

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SeparatedMellinKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic-decay kernels on separated frequency samples -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations

lemma separated_cauchy_kernel_sum (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) (t : ℝ) :
    (∑ u ∈ S, 1/(1+(u-t)^2)) ≤ 8 := by
  let F : ℝ → ℝ := fun x => 1/(1+(x-t)^2)
  let F' : ℝ → ℝ := fun x => -2*(x-t)/(1+(x-t)^2)^2
  have hD (x : ℝ) : 0 < 1+(x-t)^2 := by positivity
  have hF : Continuous F := continuous_const.div
    (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun x => (hD x).ne')
  have hder (x : ℝ) : HasDerivAt F (F' x) x := by
    have hh := ((hasDerivAt_id x).sub_const t).pow 2
    have hi := (hh.const_add 1).inv (hD x).ne'
    refine (hi.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv (Eq.symm ?_)
    · beta_reduce
      simp [F, one_div]
    · dsimp [F']
      ring
  have hb (x : ℝ) : |F' x| ≤ F x := by
    dsimp [F', F]
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_pow, abs_of_pos (hD x)]
    apply (div_le_div_iff₀ (sq_pos_of_pos (hD x)) (hD x)).mpr
    have ha := sq_nonneg (|x-t|-1)
    rw [sub_sq, sq_abs] at ha
    nlinarith [hD x]
  have hval (u : ℝ) : F u ≤ ∫ x in u..(u+1), 2*F x := by
    have hh := mrt_value_le_unit_integral F F' F hF hder hF
      (fun x => by dsimp [F] <;> positivity) hb u
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    ring
  let M : ℝ := (∑ u ∈ S, |u|)+1
  have hM : 0 < M := by dsimp [M] <;> positivity
  have hrange : ∀ u ∈ S, -M ≤ u ∧ u+1 ≤ M := by
    intro u hu
    have hh : |u| ≤ ∑ v ∈ S, |v| := single_le_sum (fun v _ => abs_nonneg v) hu
    have hh' := abs_le.mp hh
    dsimp [M]
    constructor <;> linarith
  have hs := mrt_sum_unit_integrals_le S (fun x => 2*F x) (hF.const_mul 2)
    (fun x => by dsimp [F] <;> positivity) hsep (-M) M (by linarith) hrange
  have hint : (∫ x in -M..M, F x) ≤ Real.pi := by
    change (∫ x in -M..M, (fun y : ℝ => 1/(1+y^2)) (x-t)) ≤ _
    rw [intervalIntegral.integral_comp_sub_right (fun y : ℝ => 1/(1+y^2)) t, integral_one_div_one_add_sq]
    linarith [Real.arctan_lt_pi_div_two (M-t), Real.neg_pi_div_two_lt_arctan (-M-t)]
  calc
    _ = ∑ u ∈ S, F u := rfl
    _ ≤ ∑ u ∈ S, ∫ x in u..(u+1), 2*F x := sum_le_sum fun u _ => hval u
    _ ≤ ∫ x in -M..M, 2*F x := hs
    _ = 2*(∫ x in -M..M, F x) := intervalIntegral.integral_const_mul _ _
    _ ≤ 2*Real.pi := mul_le_mul_of_nonneg_left hint (by norm_num)
    _ ≤ 8 := by linarith [Real.pi_lt_four]

lemma separated_mellin_profile_rows (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) {N : ℝ} (hN : 0 ≤ N) (t : ℝ) :
    (∑ u ∈ S, 4*N/(4+(t-u)^2)) ≤ 32*N := by
  calc
    _ ≤ ∑ u ∈ S, 4*N*(1/(1+(u-t)^2)) := by
      apply sum_le_sum
      intro u _
      rw [mul_one_div, show (t-u)^2 = (u-t)^2 by ring]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    _ = 4*N*(∑ u ∈ S, 1/(1+(u-t)^2)) := (mul_sum _ _ _).symm
    _ ≤ 4*N*8 := mul_le_mul_of_nonneg_left (separated_cauchy_kernel_sum S hsep t)
      (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveQuadratic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive continuous main term for the sparse-prime sieve -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped ComplexConjugate

lemma mellinSieveMain_nonneg {N : ℝ} (hN : 0 ≤ N) (S : Finset ℝ) (b : ℝ → ℂ) :
    0 ≤ mellinSieveMain N S b := by
  unfold mellinSieveMain
  apply mul_nonneg hN
  exact integral_nonneg (fun _ => by positivity)

lemma norm_mellinSieveMainKernel {N : ℝ} (hN : 0 ≤ N) (t : ℝ) :
    ‖mellinSieveMainKernel N t‖ = 4*N/(4+t^2) := by
  unfold mellinSieveMainKernel
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma mellinSieveMain_eq (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ) :
    mellinSieveMain N S b = ∑ t ∈ S, ∑ u ∈ S,
      ((b t*conj (b u))*mellinSieveMainKernel N (t-u)).re := by
  unfold mellinSieveMain
  rw [mrt_weighted_mean_square S _ _ (by norm_num : (0:ℝ) < 1/2), mul_sum]
  apply sum_congr rfl
  intro t _
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  have hp := mrt_phase_pair (-Real.log N*t) (-Real.log N*u)
  rw [show -Real.log N*t - -Real.log N*u = -Real.log N*(t-u) by ring] at hp
  have he : (b t*Complex.exp (((-Real.log N*t : ℝ) : ℂ)*Complex.I))*
      conj (b u*Complex.exp (((-Real.log N*u : ℝ) : ℂ)*Complex.I)) =
      (b t*conj (b u))*Complex.exp (((-Real.log N*(t-u) : ℝ) : ℂ)*Complex.I) := by
    rw [map_mul, ← hp]
    ring
  rw [he]
  unfold mellinSieveMainKernel
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hden : 0 < 4+(t-u)^2 := by positivity
  field_simp
  ring

lemma mellinSieveMain_bound {N : ℝ} (hN : 0 ≤ N) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) (b : ℝ → ℂ) :
    mellinSieveMain N S b ≤ 32*N*∑ t ∈ S, ‖b t‖^2 := by
  rw [mellinSieveMain_eq]
  calc
    _ ≤ ∑ t ∈ S, ∑ u ∈ S, ‖b t‖*‖b u‖*(4*N/(4+(t-u)^2)) := by
      apply sum_le_sum
      intro t _
      apply sum_le_sum
      intro u _
      simpa only [norm_mul, Complex.norm_conj, norm_mellinSieveMainKernel hN] using
        Complex.re_le_norm ((b t*conj (b u))*mellinSieveMainKernel N (t-u))
    _ ≤ _ := by
      apply mrt_symmetric_row_bound S _ (fun t => ‖b t‖) (32*N)
        (fun _ _ _ _ => by positivity) _ (fun t _ => separated_mellin_profile_rows S hsep hN t)
      intro t _ u _
      rw [show (t-u)^2 = (u-t)^2 by ring]

/-- The remainder of a finite quadratic form is bounded from its actual
pairwise kernel discrepancies. The sample count is exposed explicitly. -/
lemma mellin_quadratic_kernel_error (S : Finset ℝ) (b : ℝ → ℂ)
    (K L : ℝ → ℝ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (herror : ∀ t ∈ S, ∀ u ∈ S, ‖K t u-L t u‖ ≤ δ) :
    |(∑ t ∈ S, ∑ u ∈ S, ((b t*conj (b u))*K t u).re) -
      (∑ t ∈ S, ∑ u ∈ S, ((b t*conj (b u))*L t u).re)| ≤
        δ*S.card*∑ t ∈ S, ‖b t‖^2 := by
  have he : (∑ t ∈ S, ∑ u ∈ S, ((b t*conj (b u))*K t u).re) -
      (∑ t ∈ S, ∑ u ∈ S, ((b t*conj (b u))*L t u).re) =
      (∑ t ∈ S, ∑ u ∈ S, (b t*conj (b u))*(K t u-L t u)).re := by
    simp only [Complex.re_sum, mul_sub, Complex.sub_re, sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ‖∑ t ∈ S, ∑ u ∈ S, (b t*conj (b u))*(K t u-L t u)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ t ∈ S, ∑ u ∈ S, ‖(b t*conj (b u))*(K t u-L t u)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun t _ => norm_sum_le _ _)
    _ ≤ ∑ t ∈ S, ∑ u ∈ S, ‖b t‖*‖b u‖*δ := by
      apply sum_le_sum
      intro t ht
      apply sum_le_sum
      intro u hu
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (herror t ht u hu) (by positivity)
    _ = δ*(∑ t ∈ S, ‖b t‖)^2 := by
      simp only [← sum_mul, ← mul_sum]
      ring
    _ ≤ _ := by
      have hh := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun t => ‖b t‖)
      simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hh
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hδ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveRemainder
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal divisor-sum remainders for the Mellin sieve -/
namespace JointDickman
open Finset
open scoped Classical ComplexConjugate

lemma primeProduct_dvd_iff_dup2 (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (n : ℕ) :
    (∏ p ∈ D, p) ∣ n ↔ ∀ p ∈ D, p ∣ n := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert p D hp ih =>
    have hprime : p.Prime := hD p (mem_insert_self _ _)
    have hD' : ∀ q ∈ D, q.Prime := fun q hq => hD q (mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ D, q) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply (Nat.coprime_primes hprime (hD' q hq)).mpr
      intro he
      exact hp (he ▸ hq)
    rw [prod_insert hp]
    constructor
    · intro h q hq
      rcases mem_insert.mp hq with rfl | hq
      · exact dvd_trans (dvd_mul_right _ _) h
      · exact ((ih hD').mp (dvd_trans (dvd_mul_left _ _) h)) q hq
    · intro h
      apply hcop.mul_dvd_of_dvd_of_dvd (h p (mem_insert_self _ _))
      exact (ih hD').mpr (fun q hq => h q (mem_insert_of_mem hq))

lemma primeDivisorEvents_subset_iff {P D : Finset ℕ}
    (hD : D ⊆ P) (hprime : ∀ p ∈ D, p.Prime) (n : ℕ) :
    D ⊆ primeDivisorEvents P n ↔ (∏ p ∈ D, p) ∣ n := by
  rw [primeProduct_dvd_iff_dup2 D hprime]
  constructor
  · intro h p hp
    exact (mem_filter.mp (h hp)).2
  · intro h p hp
    exact mem_filter.mpr ⟨hD hp, h p hp⟩

lemma mellinSieveSquareWeight_nonneg {N : ℝ} (hN : 0 ≤ N)
    (S : Finset ℝ) (b : ℝ → ℂ) (n : ℕ) : 0 ≤ mellinSieveSquareWeight N S b n := by
  exact mul_nonneg (mellinSieveWeight_nonneg hN (Nat.cast_nonneg n)) (sq_nonneg _)

lemma mellinSieveMain_div (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ) (d : ℕ) :
    mellinSieveMain N S b / d = ∑ t ∈ S, ∑ u ∈ S,
      ((b t*conj (b u))*(mellinSieveMainKernel N (t-u)/(d : ℂ))).re := by
  rw [mellinSieveMain_eq, sum_div]
  apply sum_congr rfl
  intro t _
  rw [sum_div]
  apply sum_congr rfl
  intro u _
  rw [← mul_div_assoc]
  simp only [div_eq_mul_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Only the concrete scalar divisor-sum kernel discrepancy is needed
for the weighted sieve remainder. No short-average premise is used. -/
theorem mellin_sieve_remainder_bound {P D : Finset ℕ}
    (hD : D ⊆ P) (hprime : ∀ p ∈ D, p.Prime)
    (K : ℕ) (N : ℝ) (S : Finset ℝ) (b : ℝ → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hkernel : ∀ t ∈ S, ∀ u ∈ S,
      ‖mellinSieveDiscreteKernel K (∏ p ∈ D, p) N (t-u) -
        mellinSieveMainKernel N (t-u)/((∏ p ∈ D, p : ℕ) : ℂ)‖ ≤ δ) :
    |sieveRemainder (fun n : Icc 1 K => primeDivisorEvents P n)
      (fun n => mellinSieveSquareWeight N S b n) (mellinSieveMain N S b)
      (fun p => 1/(p : ℝ)) D| ≤ δ*S.card*∑ t ∈ S, ‖b t‖^2 := by
  have hcond (n : Icc 1 K) := primeDivisorEvents_subset_iff hD hprime n
  have hi : sieveIntersection (fun n : Icc 1 K => primeDivisorEvents P n)
      (fun n => mellinSieveSquareWeight N S b n) D =
      ∑ n ∈ (Icc 1 K).filter (fun n => (∏ p ∈ D, p) ∣ n), mellinSieveSquareWeight N S b n := by
    unfold sieveIntersection
    simp_rw [hcond]
    rw [(Icc 1 K).sum_coe_sort (fun n : ℕ => if (∏ p ∈ D, p) ∣ n then
      mellinSieveSquareWeight N S b n else 0), sum_filter]
  have hp : (∏ p ∈ D, 1/(p : ℝ)) = 1/((∏ p ∈ D, p : ℕ) : ℝ) := by
    rw [prod_div_distrib]
    simp
  unfold sieveRemainder
  rw [hi, hp, mul_one_div, mellinSieveMain_div]
  rw [show (∑ n ∈ (Icc 1 K).filter (fun n => (∏ p ∈ D, p) ∣ n),
      mellinSieveSquareWeight N S b n) = ∑ t ∈ S, ∑ u ∈ S,
      ((b t*conj (b u))*mellinSieveDiscreteKernel K (∏ p ∈ D, p) N (t-u)).re from
    mellin_weighted_dual_identity _ S (fun n => mellinSieveWeight N n) b]
  exact mellin_quadratic_kernel_error S b _ _ hδ hkernel

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPrimeSampling
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse prime sampling from concrete divisor-sum discrepancies

The constant is unconditional: it comes from the proved upper sieve.
Only the explicitly displayed finite logarithmic kernels remain to be
estimated in applications.
-/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

/-- A separated sample set gains the prime density, provided its actual
smooth divisor sums have the stated error. -/
theorem mellin_prime_sampling : ∃ C : ℝ, 0 < C ∧
    ∀ (K Z : ℕ) (P Q : Finset ℕ) (N : ℝ) (S : Finset ℝ) (δ : ℝ),
      2 ≤ Z → 0 < N → 0 ≤ δ →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z) →
      Q ⊆ Icc 1 K → (∀ q ∈ Q, q.Prime ∧ Z < q) →
      (∀ q ∈ Q, N ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z),
        ∀ t ∈ S, ∀ u ∈ S,
          ‖mellinSieveDiscreteKernel K (∏ p ∈ D, p) N (t-u) -
            mellinSieveMainKernel N (t-u)/((∏ p ∈ D, p : ℕ) : ℂ)‖ ≤ δ) →
      ∀ a : ℕ → ℂ,
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q a (fun n => -Real.log (n : ℝ)) t‖^2) ≤
        8*(32*C*N*(∏ p ∈ P, (1-1/(p : ℝ))) + (Z+1:ℕ)*δ*S.card)*
          ∑ q ∈ Q, ‖a q‖^2 := by
  obtain ⟨C, hC, hsieve⟩ := prime_weighted_sieve
  refine ⟨C, hC, ?_⟩
  intro K Z P Q N S δ hZ hN hδ hP hQ hQprime hQN hsep hkernel a
  have hprod : 0 ≤ ∏ p ∈ P, (1-1/(p : ℝ)) := by
    apply prod_nonneg
    intro p hp
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast (hP p hp).1.one_lt.le
    exact sub_nonneg.mpr ((div_le_one (by linarith : (0:ℝ) < p)).mpr hp1)
  have hcost : 0 ≤ 8*(32*C*N*(∏ p ∈ P, (1-1/(p : ℝ))) +
      (Z+1:ℕ)*δ*S.card) := by positivity
  apply mellin_samples_of_dual Q S a hcost
  intro b
  let B : ℝ := ∑ t ∈ S, ‖b t‖^2
  have hB : 0 ≤ B := sum_nonneg (fun _ _ => sq_nonneg _)
  have hR : 0 ≤ δ*S.card*B := by positivity
  have hrem (D : Finset ℕ)
      (hD : D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ Z)) :
      |sieveRemainder (fun n : Icc 1 K => primeDivisorEvents P n)
        (fun n => mellinSieveSquareWeight N S b n) (mellinSieveMain N S b)
        (fun p => 1/(p : ℝ)) D| ≤ δ*S.card*B := by
    have hDP := mem_powerset.mp (mem_filter.mp hD).1
    exact mellin_sieve_remainder_bound hDP (fun p hp => (hP p (hDP hp)).1)
      K N S b hδ (hkernel D hD)
  have hs := hsieve K Z P Q (mellinSieveSquareWeight N S b)
    (mellinSieveMain N S b) (δ*S.card*B) hZ
    (mellinSieveMain_nonneg hN.le S b) hR hP hQ hQprime
    (fun n _ => mellinSieveSquareWeight_nonneg hN.le S b n) hrem
  have hmain := mellinSieveMain_bound hN.le S hsep b
  have hupper : (∑ q ∈ Q, mellinSieveSquareWeight N S b q) ≤
      (32*C*N*(∏ p ∈ P, (1-1/(p : ℝ))) + (Z+1:ℕ)*δ*S.card)*B := by
    apply hs.trans
    calc
      _ ≤ C*(32*N*B)*(∏ p ∈ P, (1-1/(p : ℝ))) + (Z+1:ℕ)*(δ*S.card*B) := by
        apply add_le_add _ le_rfl
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmain hC.le) hprod
      _ = _ := by ring
  have hlower : (1/8:ℝ)*(∑ q ∈ Q, ‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (q : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) ≤
        ∑ q ∈ Q, mellinSieveSquareWeight N S b q := by
    rw [mul_sum]
    apply sum_le_sum
    intro q hq
    exact mul_le_mul_of_nonneg_right
      (mellinSieveWeight_interval hN (hQN q hq).1 (hQN q hq).2) (sq_nonneg _)
  have hh := hlower.trans hupper
  change _ ≤ _*B
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveRegularity
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity of the positive Mellin sieve profile -/
namespace JointDickman
open Complex

lemma mellin_power_phase {x : ℝ} (hx : 0 < x) (r t : ℝ) :
    (x : ℂ)^((r : ℂ)-(t : ℂ)*I) =
      ((x^r : ℝ) : ℂ)*Complex.exp (((-Real.log x*t : ℝ) : ℂ)*I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le]
  rw [show (Real.log x : ℂ)*((r : ℂ)-(t : ℂ)*I) =
    ((Real.log x*r : ℝ) : ℂ)+(((-Real.log x*t : ℝ) : ℂ)*I) by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp, Real.rpow_def_of_pos hx]

lemma mellinSieveFunction_left {N x : ℝ} (hN : 0 < N) (hx : 0 < x)
    (hxN : x ≤ N) (t : ℝ) :
    mellinSieveFunction N t x = (1/(N : ℂ))*(x : ℂ)^((1 : ℂ)-(t : ℂ)*I) := by
  rw [mellinSieveFunction, mellinSieveWeight_left hN hx hxN,
    (show (x : ℂ)^((1 : ℂ)-(t : ℂ)*I) = _ from
      by simpa only [Complex.ofReal_one] using mellin_power_phase hx 1 t), Real.rpow_one]
  push_cast
  ring

lemma mellinSieveFunction_right {N x : ℝ} (hN : 0 < N) (hxN : N ≤ x) (t : ℝ) :
    mellinSieveFunction N t x = (N : ℂ)^3*(x : ℂ)^((-3 : ℂ)-(t : ℂ)*I) := by
  have hx := hN.trans_le hxN
  rw [mellinSieveFunction, mellinSieveWeight_right hN hxN,
    show ((-3 : ℂ)-(t : ℂ)*I) = (((-3 : ℝ) : ℂ)-(t : ℂ)*I) by norm_num,
    mellin_power_phase hx, Real.rpow_neg hx.le]
  simp only [Real.rpow_ofNat, Complex.ofReal_inv, Complex.ofReal_pow]
  push_cast
  ring

lemma norm_mellin_exponent (r t : ℝ) :
    ‖(r : ℂ)-(t : ℂ)*I‖ ≤ |r|+|t| := by
  simpa only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using
    norm_sub_le (r : ℂ) ((t : ℂ)*I)

lemma mellinSieveFunction_left_sub {N a b : ℝ} (hN : 0 < N)
    (ha : 0 < a) (hab : a ≤ b) (hbN : b ≤ N) (t : ℝ) :
    ‖mellinSieveFunction N t b-mellinSieveFunction N t a‖ ≤
      ((3+|t|)/N)*(b-a) := by
  let s : ℂ := 1-(t : ℂ)*I
  have hs : s.re = 1 := by simp [s]
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; simp at hs
  have hder (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivAt (fun x : ℝ => (1/(N : ℂ))*(x : ℂ)^s)
        ((1/(N : ℂ))*(s*(x : ℂ)^(s-1))) x := by
    exact (hasDerivAt_ofReal_cpow_const (ha.trans_le hx.1).ne' hs0).const_mul _
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      ‖(1/(N : ℂ))*(s*(x : ℂ)^(s-1))‖ ≤ (3+|t|)/N := by
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx.1)]
    simp only [Complex.sub_re, hs, one_re, sub_self, Real.rpow_zero, mul_one,
      norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
    have hh := norm_mellin_exponent 1 t
    norm_num at hh
    dsimp [s]
    apply (show (1/N)*‖(1 : ℂ)-(t : ℂ)*I‖ = ‖(1 : ℂ)-(t : ℂ)*I‖/N by ring).trans_le
    exact div_le_div_of_nonneg_right (hh.trans (by linarith)) hN.le
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hder x hx).hasDerivWithinAt) hbound (convex_Icc a b)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hh
  rw [mellinSieveFunction_left hN (ha.trans_le hab) hbN,
    mellinSieveFunction_left hN ha (hab.trans hbN)]
  exact hh

lemma mellinSieveFunction_right_sub {N a b : ℝ} (hN : 0 < N)
    (hNa : N ≤ a) (hab : a ≤ b) (t : ℝ) :
    ‖mellinSieveFunction N t b-mellinSieveFunction N t a‖ ≤
      ((3+|t|)/N)*(b-a) := by
  let s : ℂ := -3-(t : ℂ)*I
  have hs : s.re = -3 := by simp [s]
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  have hder (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivAt (fun x : ℝ => (N : ℂ)^3*(x : ℂ)^s)
        ((N : ℂ)^3*(s*(x : ℂ)^(s-1))) x := by
    exact (hasDerivAt_ofReal_cpow_const (hN.trans_le (hNa.trans hx.1)).ne' hs0).const_mul _
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      ‖(N : ℂ)^3*(s*(x : ℂ)^(s-1))‖ ≤ (3+|t|)/N := by
    have hxN : N ≤ x := hNa.trans hx.1
    have hx0 : 0 < x := hN.trans_le hxN
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.sub_re, hs, one_re, show (-3:ℝ)-1 = -4 by norm_num,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
    rw [Real.rpow_neg hx0.le, show (4:ℝ) = (4:ℕ) by norm_num, Real.rpow_natCast]
    have hh : ‖s‖ ≤ 3+|t| := by simpa [s] using norm_mellin_exponent (-3) t
    have hp : N^4 ≤ x^4 := pow_le_pow_left₀ hN.le hxN 4
    have hfrac : N^3*(x^4)⁻¹ ≤ 1/N := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hx0 4) hN]
      nlinarith
    calc
      _ = (N^3*(x^4)⁻¹)*‖s‖ := by ring
      _ ≤ (1/N)*(3+|t|) := mul_le_mul hfrac hh (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hder x hx).hasDerivWithinAt) hbound (convex_Icc a b)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hh
  rw [mellinSieveFunction_right hN (hNa.trans hab), mellinSieveFunction_right hN hNa]
  exact hh

lemma norm_mellinSieveFunction (N t x : ℝ) :
    ‖mellinSieveFunction N t x‖ = |mellinSieveWeight N x| := by
  rw [mellinSieveFunction, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

lemma mellinSieveFunction_zero (N t : ℝ) : mellinSieveFunction N t 0 = 0 := by
  simp [mellinSieveFunction, mellinSieveWeight]

lemma norm_mellinSieveFunction_le {N x : ℝ} (hN : 0 < N) (hx : 0 ≤ x) (t : ℝ) :
    ‖mellinSieveFunction N t x‖ ≤ x/N := by
  rw [norm_mellinSieveFunction, abs_of_nonneg (mellinSieveWeight_nonneg hN.le hx)]
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [mellinSieveWeight]
  by_cases hxN : x ≤ N
  · exact (mellinSieveWeight_left hN hx hxN).le
  · have hNx : N ≤ x := le_of_not_ge hxN
    rw [mellinSieveWeight_right hN hNx]
    have hr : N/x ≤ 1 := (div_le_one hx).mpr hNx
    exact (pow_le_one₀ (by positivity) hr).trans ((one_le_div hN).mpr hNx)

/-- The cusp at the profile's maximum does not affect its global
Lipschitz bound on the nonnegative half-line. -/
lemma mellinSieveFunction_sub {N a b : ℝ} (hN : 0 < N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (t : ℝ) :
    ‖mellinSieveFunction N t b-mellinSieveFunction N t a‖ ≤
      ((3+|t|)/N)*|b-a| := by
  suffices hh : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ‖mellinSieveFunction N t b-mellinSieveFunction N t a‖ ≤
        ((3+|t|)/N)*(b-a) by
    rcases le_total a b with hab | hba
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hh a b ha hab
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hba)]
      exact hh b a hb hba
  intro a b ha hab
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [mellinSieveFunction_zero, sub_zero, sub_zero]
    apply (norm_mellinSieveFunction_le hN hab t).trans
    have hc : 1/N ≤ (3+|t|)/N :=
      div_le_div_of_nonneg_right (by linarith [abs_nonneg t]) hN.le
    simpa only [one_mul, div_mul_eq_mul_div] using mul_le_mul_of_nonneg_right hc hab
  · by_cases hbN : b ≤ N
    · exact mellinSieveFunction_left_sub hN ha hab hbN t
    · by_cases hNa : N ≤ a
      · exact mellinSieveFunction_right_sub hN hNa hab t
      · have haN : a ≤ N := le_of_not_ge hNa
        have hNb : N ≤ b := le_of_not_ge hbN
        calc
          _ ≤ ‖mellinSieveFunction N t b-mellinSieveFunction N t N‖ +
              ‖mellinSieveFunction N t N-mellinSieveFunction N t a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ((3+|t|)/N)*(b-N)+((3+|t|)/N)*(N-a) := add_le_add
            (mellinSieveFunction_right_sub hN le_rfl hNb t)
            (mellinSieveFunction_left_sub hN ha haN le_rfl t)
          _ = _ := by ring

lemma mellinSieveFunction_continuousOn {N : ℝ} (hN : 0 < N) (t : ℝ) :
    ContinuousOn (mellinSieveFunction N t) (Set.Ici 0) := by
  exact (LipschitzOnWith.of_dist_le' (fun a ha b hb => by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using mellinSieveFunction_sub hN hb ha t)).continuousOn

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinWeightedLogPhase
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic cancellation with the two Mellin profile weights -/
namespace JointDickman
open Finset Filter Complex Problem337
open scoped Topology

lemma mellinSieveFunction_dilate {N d x : ℝ} (hN : 0 < N) (hd : 0 < d)
    (hx : 0 < x) (t : ℝ) :
    mellinSieveFunction N t (d*x) =
      Complex.exp (((-Real.log d*t : ℝ) : ℂ)*I)*mellinSieveFunction (N/d) t x := by
  have hw : mellinSieveWeight N (d*x) = mellinSieveWeight (N/d) x := by
    unfold mellinSieveWeight
    rw [Real.log_mul hd.ne' hx.ne', Real.log_div hN.ne' hd.ne']
    rw [show Real.log d+Real.log x-Real.log N =
      Real.log x-(Real.log N-Real.log d) by ring]
    congr 1
    field_simp
  unfold mellinSieveFunction
  rw [hw, Real.log_mul hd.ne' hx.ne', mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma linear_log_phase_sum_bound (t : ℝ) (L R : ℤ) (hL : 0 < L) (hLR : L ≤ R)
    {D : ℝ} (hD : 0 ≤ D)
    (hpartial : ∀ V, L ≤ V → V ≤ R →
      ‖∑ n ∈ Icc L V, (n:ℂ)^(-((t:ℂ)*I))‖ ≤ D) :
    ‖∑ n ∈ Icc L R, (n:ℂ)*(n:ℂ)^(-((t:ℂ)*I))‖ ≤ 2*D*((R:ℝ)+1) := by
  have hh := increasing_weighted_sum_Icc_bound
    (fun n => (n:ℂ)^(-((t:ℂ)*I))) (fun n => (n:ℝ)) L R hLR hD
    (fun n hn => by exact_mod_cast (hL.le.trans hn))
    (fun i _ j _ hij => by change (i:ℝ) ≤ (j:ℝ); exact_mod_cast hij) hpartial
  simpa only [Complex.real_smul, Complex.ofReal_intCast, Int.cast_add, Int.cast_one] using hh

lemma mellinSieveFunction_left_sum {N : ℝ} (hN : 0 < N) (t : ℝ)
    (L R : ℤ) (hL : 0 < L) (hLR : L ≤ R) (hRN : (R:ℝ) ≤ N)
    {D : ℝ} (hD : 0 ≤ D)
    (hpartial : ∀ V, L ≤ V → V ≤ R →
      ‖∑ n ∈ Icc L V, (n:ℂ)^(-((t:ℂ)*I))‖ ≤ D) :
    ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ 2*D*((R:ℝ)+1)/N := by
  have he : (∑ n ∈ Icc L R, mellinSieveFunction N t n) =
      (1/(N:ℂ))*(∑ n ∈ Icc L R, (n:ℂ)*(n:ℂ)^(-((t:ℂ)*I))) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hL.trans_le (mem_Icc.mp hn).1
    rw [mellinSieveFunction_left hN hn0 (le_trans (by exact_mod_cast (mem_Icc.mp hn).2) hRN),
      show (1:ℂ)-(t:ℂ)*I = 1+(-((t:ℂ)*I)) by ring,
      cpow_add _ _ (by exact_mod_cast hn0.ne'), cpow_one]
    push_cast
    ring
  rw [he, norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  have hh := linear_log_phase_sum_bound t L R hL hLR hD hpartial
  have := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1/N by positivity)
  simpa only [one_div_mul_eq_div] using this

lemma mellinSieveFunction_right_sum {N : ℝ} (hN : 0 < N) (t : ℝ)
    (L R : ℤ) (hL : 0 < L) (hNL : N ≤ (L:ℝ))
    {D : ℝ} (hD : 0 ≤ D)
    (hpartial : ∀ V, L ≤ V → V ≤ R →
      ‖∑ n ∈ Icc L V, (n:ℂ)^(-((t:ℂ)*I))‖ ≤ D) :
    ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ N^3*D*(L:ℝ)^(-3:ℝ) := by
  have he : (∑ n ∈ Icc L R, mellinSieveFunction N t n) =
      (N:ℂ)^3*(∑ n ∈ Icc L R, (((n:ℝ)^(-3:ℝ):ℝ):ℂ)*(n:ℂ)^(-((t:ℂ)*I))) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hL.trans_le (mem_Icc.mp hn).1
    have hNn : N ≤ (n:ℝ) := hNL.trans (by exact_mod_cast (mem_Icc.mp hn).1)
    rw [mellinSieveFunction_right hN hNn,
      show (-3:ℂ)-(t:ℂ)*I = ((-3:ℝ):ℂ)+(-((t:ℂ)*I)) by push_cast; ring,
      cpow_add _ _ (by exact_mod_cast hn0.ne')]
    rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp, ← ofReal_cpow hn0.le]
  rw [he, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  have hh := rpow_weighted_sum_Icc_bound
    (fun n => (n:ℂ)^(-((t:ℂ)*I))) L R (σ := 3) hL hD (by norm_num) hpartial
  have := mul_le_mul_of_nonneg_left hh (show 0 ≤ N^3 by positivity)
  simpa only [mul_assoc] using this

/-- Logarithmic phase cancellation in the angular convention. -/
theorem angular_log_phase_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (t : ℝ) (L R : ℤ),
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, (n:ℂ)^(-((t:ℂ)*I))‖ ≤ A*U^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hbound⟩ := logarithmic_phase_uniform B hB
  refine ⟨A,δ,hA,hδ,?_⟩
  filter_upwards [hbound, eventually_gt_atTop (0:ℝ)] with U hbound hU
  intro t L R hlo hhi hL hR
  have he : (∑ n ∈ Icc L R, (n:ℂ)^(-((t:ℂ)*I))) =
      ∑ n ∈ Icc L R, differencingPhase (0*n+(-t/(2*Real.pi))*Real.log (n:ℝ)) := by
    apply sum_congr rfl
    intro n hn
    have hn0 : (0:ℝ) < n := hU.trans_le (hL.trans (by exact_mod_cast (mem_Icc.mp hn).1))
    simpa only [zero_mul, zero_add] using imaginary_power_as_log_phase t (by exact_mod_cast hn0)
  rw [he]
  exact hbound 0 (-t/(2*Real.pi)) L R
    (by simpa only [neg_div, abs_neg] using hlo)
    (by simpa only [neg_div, abs_neg] using hhi) hL hR

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinProfileBlock
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform logarithmic block bound for the Mellin profile -/
namespace JointDickman
open Finset Filter
open scoped Topology

lemma mellin_sum_Icc_split (f : ℤ → ℂ) {L K R : ℤ} (hLK : L ≤ K) (hKR : K < R) :
    (∑ n ∈ Icc L R, f n) = (∑ n ∈ Icc L K, f n)+(∑ n ∈ Icc (K+1) R, f n) := by
  have he : Icc L R = Icc L K ∪ Icc (K+1) R := by
    ext n
    simp only [mem_Icc, mem_union]
    omega
  rw [he, sum_union]
  apply disjoint_left.mpr
  intro n hn hn'
  simp only [mem_Icc] at hn hn'
  omega

lemma mellin_profile_crossing_bound {N : ℝ} (hN : 1 ≤ N) (t : ℝ) (L R : ℤ)
    (hL : 0 < L) (hLN : (L:ℝ) ≤ N) (hNR : N < (R:ℝ))
    {D : ℝ} (hD : 0 ≤ D)
    (hpartial : ∀ A B : ℤ, L ≤ A → B ≤ R →
      ‖∑ n ∈ Icc A B, (n:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤ D) :
    ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ 6*D := by
  let K : ℤ := ⌊N⌋
  have hLK : L ≤ K := Int.le_floor.mpr hLN
  have hKN : (K:ℝ) ≤ N := Int.floor_le N
  have hNK : N < (K:ℝ)+1 := Int.lt_floor_add_one N
  have hKR : K < R := by exact_mod_cast hKN.trans_lt hNR
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hl := mellinSieveFunction_left_sum hN0 t L K hL hLK hKN hD
    (fun V _ hVK => hpartial L V le_rfl (hVK.trans hKR.le))
  have hr := mellinSieveFunction_right_sum hN0 t (K+1) R (by omega)
    (by exact_mod_cast hNK.le) hD (fun V _ hVR => hpartial (K+1) V (by omega) hVR)
  have hlb : 2*D*((K:ℝ)+1)/N ≤ 4*D := by
    apply (div_le_iff₀ hN0).mpr
    nlinarith
  have hrb : N^3*D*((K+1:ℤ):ℝ)^(-3:ℝ) ≤ D := by
    have hK0 : (0:ℝ) < (K+1:ℤ) := by exact_mod_cast (show 0 < K+1 by omega)
    have hK : N ≤ ((K+1:ℤ):ℝ) := by exact_mod_cast hNK.le
    rw [Real.rpow_neg hK0.le, Real.rpow_ofNat]
    have hc : N^3*((((K+1:ℤ):ℝ)^3)⁻¹) ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (pow_pos hK0 3)]
      exact pow_le_pow_left₀ hN0.le hK 3
    nlinarith
  rw [mellin_sum_Icc_split _ hLK hKR]
  exact (norm_add_le _ _).trans (by linarith [hl,hr])

lemma mellin_profile_block_bound {N U A δ : ℝ} (hN : 1 ≤ N) (hU : 1 ≤ U)
    (hA : 0 ≤ A) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) (L R : ℤ)
    (hUL : U ≤ (L:ℝ)) (hRU : (R:ℝ) ≤ 2*U)
    (hpartial : ∀ l r : ℤ, L ≤ l → r ≤ R →
      ‖∑ n ∈ Icc l r, (n:ℂ)^(-((t:ℂ)*Complex.I))‖ ≤ A*U^(1-δ)) :
    ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ 6*A*N^(1-δ) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hL : 0 < L := by exact_mod_cast (hU0.trans_le hUL)
  have hD : 0 ≤ A*U^(1-δ) := by positivity
  by_cases hLR : L ≤ R
  swap
  · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hLR), sum_empty, norm_zero]
    positivity
  by_cases hRN : (R:ℝ) ≤ N
  · have hUN : U ≤ N := hUL.trans ((by exact_mod_cast hLR : (L:ℝ) ≤ R).trans hRN)
    have hh := mellinSieveFunction_left_sum hN0 t L R hL hLR hRN hD
      (fun V _ hVR => hpartial L V le_rfl hVR)
    have hp : U^(1-δ) ≤ N^(1-δ) := Real.rpow_le_rpow hU0.le hUN (by linarith)
    apply hh.trans
    apply (div_le_iff₀ hN0).mpr
    have hR : (R:ℝ)+1 ≤ 3*U := by linarith
    calc
      2*(A*U^(1-δ))*((R:ℝ)+1) ≤ 6*A*U^(1-δ)*U := by nlinarith [mul_nonneg hA (Real.rpow_nonneg hU0.le (1-δ))]
      _ ≤ 6*A*N^(1-δ)*N := mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hUN hU0.le (by positivity)
  by_cases hNL : N ≤ (L:ℝ)
  · have hh := mellinSieveFunction_right_sum hN0 t L R hL hNL hD
      (fun V _ hVR => hpartial L V le_rfl hVR)
    have hL0 : (0:ℝ) < L := by exact_mod_cast hL
    have hc : N^3*(L:ℝ)^(-3:ℝ) ≤ 1 := by
      rw [Real.rpow_neg hL0.le, Real.rpow_ofNat, ← div_eq_mul_inv,
        div_le_one (pow_pos hL0 3)]
      exact pow_le_pow_left₀ hN0.le hNL 3
    have hcore : N^3*(U^(1-δ)*(L:ℝ)^(-3:ℝ)) ≤ N^(1-δ) := by
      by_cases hUN : U ≤ N
      · have hp := Real.rpow_le_rpow hU0.le hUN (show 0 ≤ 1-δ by linarith)
        calc
          _ = (N^3*(L:ℝ)^(-3:ℝ))*U^(1-δ) := by ring
          _ ≤ 1*N^(1-δ) := mul_le_mul hc hp (Real.rpow_nonneg hU0.le _) (by norm_num)
          _ = _ := one_mul _
      · have hNU : N ≤ U := le_of_not_ge hUN
        calc
          _ ≤ N^3*(U^(1-δ)*U^(-3:ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hN0.le 3)
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hU0.le _)
            exact Real.rpow_le_rpow_of_nonpos hU0 hUL (by norm_num)
          _ = N^3*U^(-2-δ) := by rw [← Real.rpow_add hU0]; congr 2; ring
          _ ≤ N^3*N^(-2-δ) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hN0 hNU (by linarith)) (by positivity)
          _ = N^(1-δ) := by rw [← Real.rpow_natCast N 3, ← Real.rpow_add hN0]; congr 1; norm_num <;> ring
    have hb : N^3*(A*U^(1-δ))*(L:ℝ)^(-3:ℝ) ≤ A*N^(1-δ) := by
      calc
        _ = A*(N^3*(U^(1-δ)*(L:ℝ)^(-3:ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcore hA
    exact hh.trans (hb.trans (by nlinarith [mul_nonneg hA (Real.rpow_nonneg hN0.le (1-δ))]))
  · have hLN : (L:ℝ) ≤ N := le_of_not_ge hNL
    have hUN := hUL.trans hLN
    have hh := mellin_profile_crossing_bound hN t L R hL hLN (lt_of_not_ge hRN) hD hpartial
    exact hh.trans (by
      have hp := Real.rpow_le_rpow hU0.le hUN (show 0 ≤ 1-δ by linarith)
      calc
        6*(A*U^(1-δ)) = (6*A)*U^(1-δ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity))

/-- A fixed polynomial frequency range has a positive power saving for
all the scaled profile blocks, uniformly in the profile's maximum. -/
theorem mellin_profile_block_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ᶠ U : ℝ in atTop, ∀ (N t : ℝ) (L R : ℤ), 1 ≤ N →
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, mellinSieveFunction N t n‖ ≤ A*N^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hbound⟩ := angular_log_phase_uniform B hB
  let ε : ℝ := min δ 1
  have hε : 0 < ε := lt_min hδ zero_lt_one
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ 1 := min_le_right _ _
  refine ⟨6*A,ε,by positivity,hε,hε1,?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1:ℝ)] with U hbound hU
  intro N t L R hN hlo hhi hL hR
  have hh := mellin_profile_block_bound hN hU hA.le hε hε1 t L R hL hR (by
    intro l r hLl hrR
    apply (hbound t l r hlo hhi (hL.trans (by exact_mod_cast hLl))
      ((by exact_mod_cast hrR : (r:ℝ) ≤ R).trans hR)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU (by linarith)) hA.le)
  simpa only [mul_assoc] using hh

theorem mellin_dilated_profile_block_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ᶠ U : ℝ in atTop, ∀ (N d t : ℝ) (L R : ℤ), 0 < d → d ≤ N →
        U^(1/2:ℝ) ≤ |t/(2*Real.pi)| → |t/(2*Real.pi)| ≤ U^B →
        U ≤ (L:ℝ) → (R:ℝ) ≤ 2*U →
        ‖∑ n ∈ Icc L R, mellinSieveFunction N t (d*n)‖ ≤ A*(N/d)^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hδ1,hbound⟩ := mellin_profile_block_uniform B hB
  refine ⟨A,δ,hA,hδ,hδ1,?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1:ℝ)] with U hbound hU
  intro N d t L R hd hdN hlo hhi hL hR
  have hN : 0 < N := hd.trans_le hdN
  have he : (∑ n ∈ Icc L R, mellinSieveFunction N t (d*n)) =
      Complex.exp (((-Real.log d*t:ℝ):ℂ)*Complex.I)*
        ∑ n ∈ Icc L R, mellinSieveFunction (N/d) t n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    exact mellinSieveFunction_dilate hN hd
      (lt_of_lt_of_le zero_lt_one (hU.trans (hL.trans (by exact_mod_cast (mem_Icc.mp hn).1)))) t
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact hbound (N/d) t L R ((one_le_div hd).mpr hdN) hlo hhi hL hR

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveIntegral
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Mellin sieve profile: full integral and truncation error -/
namespace JointDickman
open MeasureTheory Complex

lemma mellinSieveFunction_atom (N t x : ℝ) :
    mellinSieveFunction N t x =
      Complex.exp (((-Real.log N*t : ℝ) : ℂ)*I)*mellinSieveAtom N t x := by
  unfold mellinSieveFunction mellinSieveAtom
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma integral_mellinSieveFunction (N t : ℝ) :
    (∫ x in Set.Ioi (0:ℝ), mellinSieveFunction N t x) = mellinSieveMainKernel N t := by
  simp_rw [mellinSieveFunction_atom]
  rw [integral_const_mul, integral_mellinSieveAtom]
  rfl

lemma mellinSieveFunction_tail_norm {N B : ℝ} (hN : 0 < N) (hNB : N ≤ B) (t : ℝ) :
    (∫ x in Set.Ioi B, ‖mellinSieveFunction N t x‖) = N^3/(2*B^2) := by
  have hB : 0 < B := hN.trans_le hNB
  have he (x : ℝ) (hx : x ∈ Set.Ioi B) :
      ‖mellinSieveFunction N t x‖ = N^3*x^(-3:ℝ) := by
    have hNx := hNB.trans hx.le
    rw [norm_mellinSieveFunction, abs_of_nonneg (mellinSieveWeight_nonneg hN.le
      (hN.le.trans hNx)), mellinSieveWeight_right hN hNx,
      Real.rpow_neg (hN.le.trans hNx), Real.rpow_ofNat]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hB]
  norm_num only [neg_add_cancel_left, show (-3:ℝ)+1 = -2 by norm_num]
  rw [Real.rpow_neg hB.le, Real.rpow_two]
  ring

lemma mellinSieveFunction_tail_integrable {N B : ℝ} (hN : 0 < N) (hNB : N ≤ B) (t : ℝ) :
    IntegrableOn (mellinSieveFunction N t) (Set.Ioi B) := by
  have hB : 0 < B := hN.trans_le hNB
  have hm : AEStronglyMeasurable (mellinSieveFunction N t) (volume.restrict (Set.Ioi B)) :=
    ((mellinSieveFunction_continuousOn hN t).mono (by
      intro x hx
      exact (hB.trans hx).le)).aestronglyMeasurable measurableSet_Ioi
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hB).const_mul (N^3) |>.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mellinSieveFunction, abs_of_nonneg (mellinSieveWeight_nonneg hN.le
    (hB.trans hx).le), mellinSieveWeight_right hN (hNB.trans hx.le),
    Real.rpow_neg (hB.trans hx).le, Real.rpow_ofNat]
  exact le_of_eq (by ring)

lemma mellinSieveFunction_integrable {N : ℝ} (hN : 0 < N) (t : ℝ) :
    IntegrableOn (mellinSieveFunction N t) (Set.Ioi 0) := by
  have hleft : IntegrableOn (mellinSieveFunction N t) (Set.Ioc 0 N) :=
    ((mellinSieveFunction_continuousOn hN t).mono Set.Icc_subset_Ici_self).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hright := mellinSieveFunction_tail_integrable hN le_rfl t
  have hu : Set.Ioc (0:ℝ) N ∪ Set.Ioi N = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith [hN]
    · intro hx
      by_cases hxN : x ≤ N
      · exact Or.inl ⟨hx,hxN⟩
      · exact Or.inr (lt_of_not_ge hxN)
  rw [← hu]
  exact hleft.union hright

/-- Truncating the full transform beyond the profile's maximum costs only
its elementary cubic tail. -/
theorem mellinSieveFunction_integral_error {N B : ℝ} (hN : 0 < N) (hNB : N ≤ B) (t : ℝ) :
    ‖(∫ x in (0:ℝ)..B, mellinSieveFunction N t x) - mellinSieveMainKernel N t‖ ≤
      N^3/(2*B^2) := by
  have hB := hN.trans_le hNB
  have hi := mellinSieveFunction_integrable hN t
  have hu : Set.Ioc (0:ℝ) B ∪ Set.Ioi B = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith [hB]
    · intro hx
      by_cases hxB : x ≤ B
      · exact Or.inl ⟨hx,hxB⟩
      · exact Or.inr (lt_of_not_ge hxB)
  have he := setIntegral_union (f := mellinSieveFunction N t)
    (s := Set.Ioc 0 B) (t := Set.Ioi B) (by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact (not_lt_of_ge hx.2) hy)
    measurableSet_Ioi (hi.mono_set Set.Ioc_subset_Ioi_self)
    (hi.mono_set (Set.Ioi_subset_Ioi hB.le))
  rw [hu, integral_mellinSieveFunction] at he
  rw [intervalIntegral.integral_of_le hB.le, he,
    show ((∫ x in Set.Ioc (0:ℝ) B, mellinSieveFunction N t x) -
      ((∫ x in Set.Ioc (0:ℝ) B, mellinSieveFunction N t x)+
        ∫ x in Set.Ioi B, mellinSieveFunction N t x)) =
      -(∫ x in Set.Ioi B, mellinSieveFunction N t x) by ring, norm_neg]
  exact (norm_integral_le_integral_norm _).trans_eq (mellinSieveFunction_tail_norm hN hNB t)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveGrid
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Direct divisor-grid approximation for the Mellin sieve kernel -/
namespace JointDickman
open Finset MeasureTheory

lemma sum_grid_eq_filter {E : Type*} [AddCommMonoid E] (f : ℕ → E)
    (K d : ℕ) (hd : 0 < d) :
    (∑ m ∈ range (K/d), f (d*(m+1))) =
      ∑ n ∈ (Icc 1 K).filter (fun n => d ∣ n), f n := by
  rw [riemann_sum_range_succ_eq_Icc (fun m => f (d*m))]
  apply sum_bij (fun m _ => d*m)
  · intro m hm
    obtain ⟨hm1, hmK⟩ := mem_Icc.mp hm
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
    have hh := (Nat.le_div_iff_mul_le hd).mp hmK
    simpa only [Nat.mul_comm] using hh
  · intro m hm n hn he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro n hn
    obtain ⟨hnK, hdn⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnK⟩ := mem_Icc.mp hnK
    have he : d*(n/d) = n := Nat.mul_div_cancel' hdn
    refine ⟨n/d, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnK⟩, he⟩
    have hdle := Nat.le_of_dvd (by omega : 0 < n) hdn
    exact Nat.div_pos hdle hd
  · intro m hm
    rfl

lemma mellinSieve_grid_riemann {N d : ℝ} (hN : 0 < N) (hd : 0 < d)
    (M : ℕ) (t : ℝ) :
    ‖(∑ m ∈ range M, mellinSieveFunction N t (d*(m+1))) -
      (d⁻¹ : ℂ)*(∫ x in (0:ℝ)..d*M, mellinSieveFunction N t x)‖ ≤
        (M:ℝ)*d*((3+|t|)/N) := by
  have hh := lipschitz_riemann_sum_error
    (fun x => mellinSieveFunction N t (d*x)) M
    (L := d*((3+|t|)/N)) (by positivity) (by
      intro x hx y hy
      have hb := mellinSieveFunction_sub hN (mul_nonneg hd.le hx.1)
        (mul_nonneg hd.le hy.1) t
      rw [← mul_sub, abs_mul, abs_of_pos hd] at hb
      exact hb.trans_eq (by ring))
  rw [intervalIntegral.integral_comp_mul_left (f := mellinSieveFunction N t) hd.ne', mul_zero,
    Complex.real_smul] at hh
  simpa only [mul_assoc, Complex.ofReal_inv] using hh

/-- The low-frequency kernel error, with the actual rounded divisor-grid
endpoint exposed. It is uniform in the divisor and in the frequency. -/
theorem mellinSieve_grid_error {N : ℝ} (hN : 0 < N) (K d : ℕ) (hd : 0 < d)
    (hB : N ≤ (d:ℝ)*(K/d:ℕ)) (t : ℝ) :
    ‖mellinSieveDiscreteKernel K d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
      (K/d:ℕ)*(d:ℝ)*((3+|t|)/N) + N^3/((d:ℝ)*2*((d:ℝ)*(K/d:ℕ))^2) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have he : mellinSieveDiscreteKernel K d N t =
      ∑ m ∈ range (K/d), mellinSieveFunction N t ((d:ℝ)*(m+1)) := by
    unfold mellinSieveDiscreteKernel mellinSampleKernel
    change (∑ n ∈ (Icc 1 K).filter (fun n => d ∣ n), mellinSieveFunction N t n) = _
    rw [← sum_grid_eq_filter (fun n => mellinSieveFunction N t n) K d hd]
    apply sum_congr rfl
    intro m hm
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [he]
  have hg := mellinSieve_grid_riemann hN hdR (K/d) t
  have ht := mellinSieveFunction_integral_error hN hB t
  let I : ℂ := ∫ x in (0:ℝ)..(d:ℝ)*(K/d:ℕ), mellinSieveFunction N t x
  calc
    _ ≤ ‖(∑ m ∈ range (K/d), mellinSieveFunction N t ((d:ℝ)*(m+1))) - (d:ℂ)⁻¹*I‖ +
        ‖(d:ℂ)⁻¹*I-mellinSieveMainKernel N t/(d:ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (K/d:ℕ)*(d:ℝ)*((3+|t|)/N) + N^3/((d:ℝ)*2*((d:ℝ)*(K/d:ℕ))^2) := by
      apply add_le_add hg
      rw [div_eq_mul_inv, mul_comm (mellinSieveMainKernel N t), ← mul_sub,
        norm_mul, norm_inv, Complex.norm_natCast]
      have hh := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hdR.le)
      exact hh.trans_eq (by ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DyadicPrimePartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dyadic partition of a finite prime set -/
namespace JointDickman
open Finset

lemma sum_monotone_blocks {R : Type*} [AddCommMonoid R]
    (P : Finset ℕ) (F : ℕ → R) (L : ℕ → ℕ) (hL : Monotone L) (J : ℕ) :
    (∑ j ∈ range J, ∑ p ∈ P.filter (fun p => L j < p ∧ p ≤ L (j+1)), F p) =
      ∑ p ∈ P.filter (fun p => L 0 < p ∧ p ≤ L J), F p := by
  induction J with
  | zero =>
    simp only [range_zero,sum_empty,sum_filter]
    symm
    apply sum_eq_zero
    intro p hp
    split_ifs with h
    · omega
    · rfl
  | succ J ih =>
    rw [sum_range_succ,ih]
    simp only [sum_filter]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have h0J := hL (Nat.zero_le J)
    have hJS := hL (Nat.le_succ J)
    by_cases h0 : L 0 < p
    · by_cases hJ : p ≤ L J
      · have hS : p ≤ L (J+1) := hJ.trans hJS
        have hn : ¬ L J < p := by omega
        simp [h0,hJ,hS,hn]
      · have hJ' : L J < p := by omega
        by_cases hS : p ≤ L (J+1) <;> simp [h0,hJ,hJ',hS]
    · have hJ : ¬ L J < p := by omega
      simp [h0,hJ]

lemma sum_dyadic_blocks {R : Type*} [AddCommMonoid R]
    (P : Finset ℕ) (F : ℕ → R) (Z J : ℕ)
    (hP : ∀ p ∈ P, Z < p ∧ p ≤ 2^J*Z) :
    (∑ p ∈ P, F p) = ∑ j ∈ range J,
      ∑ p ∈ P.filter (fun p => 2^j*Z < p ∧ p ≤ 2^(j+1)*Z), F p := by
  rw [sum_monotone_blocks P F (fun j => 2^j*Z)
    (fun i j hij => Nat.mul_le_mul_right Z (Nat.pow_le_pow_right (by norm_num) hij))]
  simp only [pow_zero,one_mul]
  symm
  apply sum_filter_of_ne
  intro p hp hn
  exact hP p hp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveHighFrequency
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing logarithmic blocks for the divisor-grid kernel -/
namespace JointDickman
open Finset Filter
open scoped Topology

/-- Dyadic recombination of logarithmic phase cancellation, with explicit
frequency and cutoff inequalities. -/
theorem mellin_profile_high_blocks (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ V : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (N d t : ℝ) (Z K J : ℕ), 0 < d → d ≤ N → 0 < Z → V ≤ Z →
        K ≤ 2^J*Z → ((2^J*Z:ℕ):ℝ)^(1/2:ℝ) ≤ |t/(2*Real.pi)| →
        |t/(2*Real.pi)| ≤ (Z:ℝ)^B →
        ‖∑ n ∈ Ioc Z K, mellinSieveFunction N t (d*n)‖ ≤
          (J:ℝ)*A*(N/d)^(1-δ) := by
  obtain ⟨A,δ,hA,hδ,hδ1,hbound⟩ := mellin_dilated_profile_block_uniform B hB
  obtain ⟨V,hV⟩ := eventually_atTop.mp hbound
  refine ⟨A,δ,V,hA,hδ,hδ1,?_⟩
  intro N d t Z K J hd hdN hZ hVZ hK hlo hhi
  have hblocks := sum_dyadic_blocks (Ioc Z K)
    (fun n => mellinSieveFunction N t (d*n)) Z J (by
      intro n hn
      exact ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans hK⟩)
  rw [hblocks]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ range J, A*(N/d)^(1-δ) := by
      apply sum_le_sum
      intro j hj
      have hjJ : j ≤ J := (mem_range.mp hj).le
      have hZU : Z ≤ 2^j*Z := by
        simpa only [one_mul] using Nat.mul_le_mul_right Z (Nat.one_le_pow j 2 (by norm_num))
      have hUU : 2^j*Z ≤ 2^J*Z := Nat.mul_le_mul_right Z
        (Nat.pow_le_pow_right (by norm_num) hjJ)
      have he : ((Ioc Z K).filter (fun n => 2^j*Z < n ∧ n ≤ 2^(j+1)*Z)) =
          Icc (2^j*Z+1) (min K (2^(j+1)*Z)) := by
        ext n
        simp only [mem_filter, mem_Ioc, mem_Icc, le_min_iff]
        omega
      rw [he]
      have hcast := sum_nat_Icc_int_cast (fun n : ℤ => mellinSieveFunction N t (d*n))
        (2^j*Z+1) (min K (2^(j+1)*Z))
      simp only [Int.cast_natCast] at hcast
      rw [hcast]
      apply hV ((2^j*Z:ℕ):ℝ) (hVZ.trans (by exact_mod_cast hZU)) N d t _ _ hd hdN
      · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hUU) (by norm_num)).trans hlo
      · exact hhi.trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hZU) (by linarith))
      · push_cast
        linarith
      · have hh : min K (2^(j+1)*Z) ≤ 2*(2^j*Z) := by
          have hm := min_le_right K (2^(j+1)*Z)
          simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm
        exact_mod_cast hh
    _ = _ := by simp <;> ring

lemma mellin_profile_small_sum {N d : ℝ} (hN : 0 < N) (hd : 0 ≤ d)
    (t : ℝ) (M Z : ℕ) (hMZ : M ≤ Z) :
    ‖∑ m ∈ Icc 1 M, mellinSieveFunction N t (d*m)‖ ≤ d*(Z:ℝ)^2/N := by
  have hpoint (m : ℕ) (hm : m ∈ Icc 1 M) :
      ‖mellinSieveFunction N t (d*m)‖ ≤ d*(Z:ℝ)/N := by
    apply (norm_mellinSieveFunction_le hN (mul_nonneg hd (Nat.cast_nonneg m)) t).trans
    apply div_le_div_of_nonneg_right _ hN.le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (mem_Icc.mp hm).2.trans hMZ) hd
  calc
    _ ≤ ∑ m ∈ Icc 1 M, ‖mellinSieveFunction N t (d*m)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Icc 1 M, d*(Z:ℝ)/N := sum_le_sum hpoint
    _ = (M:ℝ)*(d*(Z:ℝ)/N) := by simp
    _ ≤ (Z:ℝ)*(d*(Z:ℝ)/N) := mul_le_mul_of_nonneg_right (by exact_mod_cast hMZ) (by positivity)
    _ = _ := by ring

lemma mellinSieveDiscreteKernel_grid (N t : ℝ) (K d : ℕ) (hd : 0 < d) :
    mellinSieveDiscreteKernel K d N t =
      ∑ m ∈ Icc 1 (K/d), mellinSieveFunction N t ((d:ℝ)*m) := by
  unfold mellinSieveDiscreteKernel mellinSampleKernel
  change (∑ n ∈ (Icc 1 K).filter (fun n => d ∣ n), mellinSieveFunction N t n) = _
  rw [← sum_grid_eq_filter (fun n => mellinSieveFunction N t n) K d hd,
    riemann_sum_range_succ_eq_Icc (fun m => mellinSieveFunction N t ((d*m:ℕ):ℝ))]
  apply sum_congr rfl
  intro m hm
  simp only [Nat.cast_mul]

/-- The actual high-frequency divisor-kernel error. Every term on the
right is explicit; the phase saving comes from the proved derivative estimates. -/
theorem mellinSieve_high_error (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ V : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (N t : ℝ) (d K Z J : ℕ), 0 < d → (d:ℝ) ≤ N → 0 < Z → V ≤ Z →
        K/d ≤ 2^J*Z → ((2^J*Z:ℕ):ℝ)^(1/2:ℝ) ≤ |t/(2*Real.pi)| →
        |t/(2*Real.pi)| ≤ (Z:ℝ)^B →
        ‖mellinSieveDiscreteKernel K d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
          (d:ℝ)*(Z:ℝ)^2/N + (J:ℝ)*A*(N/d)^(1-δ) + 4*N/((d:ℝ)*(4+t^2)) := by
  obtain ⟨A,δ,V,hA,hδ,hδ1,hbound⟩ := mellin_profile_high_blocks B hB
  refine ⟨A,δ,V,hA,hδ,hδ1,?_⟩
  intro N t d K Z J hd hdN hZ hV hK hlo hhi
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hN : 0 < N := hdR.trans_le hdN
  have hb := hbound N d t Z (K/d) J hdR hdN hZ hV hK hlo hhi
  have he : (∑ m ∈ Icc 1 (K/d), mellinSieveFunction N t ((d:ℝ)*m)) =
      (∑ m ∈ Icc 1 (min Z (K/d)), mellinSieveFunction N t ((d:ℝ)*m)) +
        ∑ m ∈ Ioc Z (K/d), mellinSieveFunction N t ((d:ℝ)*m) := by
    have hu : Icc 1 (K/d) = Icc 1 (min Z (K/d)) ∪ Ioc Z (K/d) := by
      ext m
      simp only [mem_Icc, mem_Ioc, mem_union, le_min_iff]
      omega
    rw [hu, sum_union]
    apply disjoint_left.mpr
    intro m hm hm'
    have := (mem_Icc.mp hm).2
    have := (mem_Ioc.mp hm').1
    omega
  rw [mellinSieveDiscreteKernel_grid N t K d hd, he]
  have hs := mellin_profile_small_sum hN hdR.le t (min Z (K/d)) Z (min_le_left _ _)
  have hm : ‖mellinSieveMainKernel N t/(d:ℂ)‖ = 4*N/((d:ℝ)*(4+t^2)) := by
    rw [norm_div, norm_mellinSieveMainKernel hN.le, Complex.norm_natCast]
    field_simp
  calc
    _ ≤ ‖∑ m ∈ Icc 1 (min Z (K/d)), mellinSieveFunction N t ((d:ℝ)*m)‖ +
        ‖∑ m ∈ Ioc Z (K/d), mellinSieveFunction N t ((d:ℝ)*m)‖ +
          ‖mellinSieveMainKernel N t/(d:ℂ)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by rw [hm]; exact add_le_add (add_le_add hs hb) le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveScale
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial cutoffs for the explicit Mellin divisor error -/
namespace JointDickman

lemma mellinSieve_grid_error_coarse {N : ℝ} (hN : 0 < N) (K d : ℕ) (hd : 0 < d)
    (hNK : N ≤ (K:ℝ)/2) (hdK : (d:ℝ) ≤ (K:ℝ)/2) (t : ℝ) :
    ‖mellinSieveDiscreteKernel K d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
      (K:ℝ)*(3+|t|)/N + 2*N^3/((d:ℝ)*(K:ℝ)^2) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hK0 : (0:ℝ) < K := by linarith
  let L : ℝ := (d:ℝ)*(K/d:ℕ)
  have hL : (K:ℝ)/2 ≤ L := by
    have hmod : K % d < d := Nat.mod_lt K hd
    have he := Nat.mod_add_div K d
    have heR : (K:ℝ) = (K%d:ℕ)+(d:ℝ)*(K/d:ℕ) := by exact_mod_cast he.symm
    have hmR : ((K%d:ℕ):ℝ) < d := by exact_mod_cast hmod
    dsimp [L]
    linarith
  have hLK : L ≤ K := by dsimp [L]; exact_mod_cast Nat.mul_div_le K d
  have hL0 : 0 < L := (by linarith : 0 < (K:ℝ)/2).trans_le hL
  have hh := mellinSieve_grid_error hN K d hd (hNK.trans hL) t
  apply hh.trans
  apply add_le_add
  · have ht : 0 ≤ (3+|t|)/N := by positivity
    calc
      _ = L*((3+|t|)/N) := by dsimp [L]; ring
      _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hLK ht
  · change N^3/((d:ℝ)*2*L^2) ≤ _
    calc
      _ ≤ N^3/((d:ℝ)*2*((K:ℝ)/2)^2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hL 2) (by positivity)
      _ = _ := by field_simp

/-- One fixed set of integer powers gives a common low-frequency range
for all profiles between the tenth and eleventh powers. -/
theorem mellinSieve_integer_scale_low (q d : ℕ) (hq : 2 ≤ q) (hd : 0 < d) (hdq : d ≤ q)
    {N t : ℝ} (hNlo : (q:ℝ)^10 ≤ N) (hNhi : N ≤ (q:ℝ)^11)
    (ht : |t| ≤ (q:ℝ)^7) :
    ‖mellinSieveDiscreteKernel (q^12) d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
      6*(q:ℝ)^9 := by
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hN : 0 < N := (pow_pos hq0 10).trans_le hNlo
  have hNK : N ≤ ((q^12:ℕ):ℝ)/2 := by
    push_cast
    apply hNhi.trans
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), pow_succ]
    nlinarith [pow_pos hq0 11]
  have hdK : (d:ℝ) ≤ ((q^12:ℕ):ℝ)/2 := by
    have hdR : (d:ℝ) ≤ q := by exact_mod_cast hdq
    have hp : (q:ℝ)^2 ≤ (q:ℝ)^12 := pow_le_pow_right₀ hq1 (by norm_num)
    push_cast
    linarith [sq_nonneg ((q:ℝ)-2)]
  have hh := mellinSieve_grid_error_coarse hN (q^12) d hd hNK hdK t
  have hfirst : ((q^12:ℕ):ℝ)*(3+|t|)/N ≤ 4*(q:ℝ)^9 := by
    calc
      _ ≤ (q:ℝ)^12*(3+(q:ℝ)^7)/(q:ℝ)^10 := by push_cast; gcongr
      _ = (q:ℝ)^2*(3+(q:ℝ)^7) := by field_simp
      _ ≤ 4*(q:ℝ)^9 := by
        have hp := one_le_pow₀ hq1 (n := 7)
        nlinarith [mul_nonneg (sq_nonneg (q:ℝ)) (sub_nonneg.mpr hp)]
  have hsecond : 2*N^3/((d:ℝ)*((q^12:ℕ):ℝ)^2) ≤ 2*(q:ℝ)^9 := by
    have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
    calc
      _ ≤ 2*((q:ℝ)^11)^3/(1*((q:ℝ)^12)^2) := by push_cast; gcongr
      _ = _ := by field_simp
  exact hh.trans (by linarith)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSieveUniform
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform divisor-kernel errors on polynomial frequency ranges -/
namespace JointDickman

lemma mellin_integer_dyadic_scale (q : ℕ) (hq : 0 < q) :
    q^12 ≤ 2^(Nat.log 2 (q^3)+1)*q^9 ∧
      2^(Nat.log 2 (q^3)+1)*q^9 ≤ 2*q^12 := by
  have hlo := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (q^3)).le
  have hhi := Nat.pow_log_le_self 2 (pow_ne_zero 3 hq.ne')
  constructor
  · convert Nat.mul_le_mul_right (q^9) hlo using 1; ring
  · rw [pow_succ]
    have hh := Nat.mul_le_mul_right (2*q^9) hhi
    first | (convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

lemma mellin_integer_frequency_scale (q : ℕ) (hq : 16 ≤ q) {t : ℝ}
    (ht : (q:ℝ)^7 ≤ |t|) :
    (((2^(Nat.log 2 (q^3)+1)*q^9:ℕ):ℝ))^(1/2:ℝ) ≤ |t/(2*Real.pi)| := by
  have hqR : (16:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hs := (mellin_integer_dyadic_scale q (by omega)).2
  have hsR : (((2^(Nat.log 2 (q^3)+1)*q^9:ℕ):ℝ)) ≤ 2*(q:ℝ)^12 := by exact_mod_cast hs
  have hroot : (((2^(Nat.log 2 (q^3)+1)*q^9:ℕ):ℝ))^(1/2:ℝ) ≤ 2*(q:ℝ)^6 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
    nlinarith [pow_nonneg hq0.le 12]
  apply hroot.trans
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), le_div_iff₀ (by positivity)]
  have hp : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  have h1 : 2*(q:ℝ)^6*(2*Real.pi) ≤ 16*(q:ℝ)^6 := by nlinarith [pow_nonneg hq0.le 6]
  have h2 : 16*(q:ℝ)^6 ≤ (q:ℝ)^7 := by
    calc
      16*(q:ℝ)^6 ≤ (q:ℝ)*(q:ℝ)^6 := mul_le_mul_of_nonneg_right hqR (pow_nonneg hq0.le 6)
      _ = (q:ℝ)^7 := by ring
  exact h1.trans (h2.trans ht)

/-- A uniform divisor estimate up to `q` over a polynomial frequency range,
with explicit level-dependent error. -/
theorem mellinSieve_integer_scale_uniform (B : ℝ) (hB : 1 ≤ B) :
    ∃ A δ V : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (q d : ℕ), 16 ≤ q → 0 < d → d ≤ q → V ≤ (q:ℝ)^9 →
      ∀ (N t : ℝ), (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 → |t| ≤ (q:ℝ)^B →
      ‖mellinSieveDiscreteKernel (q^12) d N t-mellinSieveMainKernel N t/(d:ℂ)‖ ≤
        6*(q:ℝ)^9 + (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ) := by
  obtain ⟨A,δ,V,hA,hδ,hδ1,hhigh⟩ := mellinSieve_high_error B (by linarith)
  refine ⟨A,δ,V,hA,hδ,hδ1,?_⟩
  intro q d hq hd hdq hV N t hNlo hNhi ht
  have hqR : (16:ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hN : 0 < N := (pow_pos hq0 10).trans_le hNlo
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdR : (d:ℝ) ≤ q := by exact_mod_cast hdq
  have hdN : (d:ℝ) ≤ N := hdR.trans ((le_self_pow₀ hq1 (by norm_num : 10 ≠ 0)).trans hNlo)
  have hrest : 0 ≤ (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ) := by positivity
  by_cases htlow : |t| ≤ (q:ℝ)^7
  · exact (mellinSieve_integer_scale_low q d (by omega) hd hdq hNlo hNhi htlow).trans (le_add_of_nonneg_right hrest)
  have htbig : (q:ℝ)^7 ≤ |t| := le_of_not_ge htlow
  have hlo := mellin_integer_frequency_scale q hq htbig
  have hhi : |t/(2*Real.pi)| ≤ (((q^9:ℕ):ℝ))^B := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    apply (div_le_self (abs_nonneg t) (by linarith [Real.pi_gt_three] : 1 ≤ 2*Real.pi)).trans
    apply ht.trans
    exact Real.rpow_le_rpow hq0.le (by
      simpa only [Nat.cast_pow] using le_self_pow₀ hq1 (by norm_num : 9 ≠ 0)) (by linarith)
  have hk : q^12/d ≤ 2^(Nat.log 2 (q^3)+1)*q^9 :=
    (Nat.div_le_self _ _).trans (mellin_integer_dyadic_scale q (by omega)).1
  have hh := hhigh N t d (q^12) (q^9) (Nat.log 2 (q^3)+1) hd hdN
    (pow_pos (by omega : 0 < q) 9) (by simpa only [Nat.cast_pow] using hV) hk hlo hhi
  have hs : (d:ℝ)*((q^9:ℕ):ℝ)^2/N ≤ (q:ℝ)^9 := by
    calc
      _ ≤ (q:ℝ)*((q:ℝ)^9)^2/(q:ℝ)^10 := by push_cast; gcongr
      _ = _ := by field_simp
  have hm : 4*N/((d:ℝ)*(4+t^2)) ≤ (q:ℝ)^9 := by
    have ht2 : (q:ℝ)^14 ≤ t^2 := by
      have hp := pow_le_pow_left₀ (pow_nonneg hq0.le 7) htbig 2
      simpa only [sq_abs, ← pow_mul] using hp
    have hq3 : (4:ℝ) ≤ (q:ℝ)^3 := by nlinarith [one_le_pow₀ hq1 (n := 2)]
    have hq14 : 4*(q:ℝ)^11 ≤ (q:ℝ)^14 := by
      have hp := mul_le_mul_of_nonneg_left hq3 (pow_nonneg hq0.le 11)
      first | (convert hp using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hp.trans (le_of_eq (by ring)))
    have hx : 4*N ≤ (d:ℝ)*(4+t^2) := by nlinarith [hNhi, hd1, sq_nonneg t]
    exact ((div_le_one (by positivity)).mpr hx).trans (one_le_pow₀ hq1)
  have hp : (N/(d:ℝ))^(1-δ) ≤ N^(1-δ) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hN.le hd1) (by linarith)
  have hj : (Nat.log 2 (q^3)+1:ℕ)*A*(N/d)^(1-δ) ≤
      (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ) := mul_le_mul_of_nonneg_left hp (by positivity)
  exact hh.trans (by linarith [pow_nonneg hq0.le 9])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPrimeSamplingArithmetic
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime sampling with the divisor errors discharged -/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped Classical

/-- Sparse-prime sampling with explicit divisor-sum error bounds. -/
theorem mellin_prime_sampling_arithmetic_jd_oai (B : ℝ) (hB : 1 ≤ B) :
    ∃ C A δ V : ℝ, 0 < C ∧ 0 < A ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ (q Z : ℕ) (P Q : Finset ℕ) (N : ℝ) (S : Finset ℝ),
      16 ≤ q → 2 ≤ Z → Z ≤ q → V ≤ (q:ℝ)^9 →
      (q:ℝ)^10 ≤ N → N ≤ (q:ℝ)^11 →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z) →
      (∀ p ∈ Q, p.Prime ∧ Z < p ∧ N ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*N) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ (q:ℝ)^B) →
      ∀ a : ℕ → ℂ,
      (∑ t ∈ S, ‖mrtExponentialPolynomial Q a (fun n => -Real.log (n:ℝ)) t‖^2) ≤
        8*(32*C*N*(∏ p ∈ P, (1-1/(p:ℝ))) + (Z+1:ℕ)*
          (6*(q:ℝ)^9 + (Nat.log 2 (q^3)+1:ℕ)*A*N^(1-δ))*S.card)*
            ∑ p ∈ Q, ‖a p‖^2 := by
  obtain ⟨C,hC,hsample⟩ := mellin_prime_sampling
  obtain ⟨A,δ,V,hA,hδ,hδ1,hkernel⟩ := mellinSieve_integer_scale_uniform B hB
  refine ⟨C,A,δ,V,hC,hA,hδ,hδ1,?_⟩
  intro q Z P Q N S hq hZ hZq hV hNl hNu hP hQ hsep hdiam a
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hN : 0 < N := (pow_pos hq0 10).trans_le hNl
  have hQK : Q ⊆ Icc 1 (q^12) := by
    intro p hp
    apply mem_Icc.mpr
    refine ⟨(hQ p hp).1.one_le, ?_⟩
    have hq2 : (2:ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    have hcut : 2*N ≤ (q:ℝ)^12 := by
      apply (mul_le_mul_of_nonneg_left hNu (by norm_num : (0:ℝ) ≤ 2)).trans
      calc
        2*(q:ℝ)^11 ≤ (q:ℝ)*(q:ℝ)^11 := mul_le_mul_of_nonneg_right hq2 (pow_nonneg hq0.le 11)
        _ = _ := by ring
    exact_mod_cast (hQ p hp).2.2.2.trans hcut
  apply hsample (q^12) Z P Q N S _ hZ hN (by positivity) hP hQK
    (fun p hp => ⟨(hQ p hp).1, (hQ p hp).2.1⟩)
    (fun p hp => (hQ p hp).2.2) hsep _ a
  intro D hD x hx y hy
  have hDP : D ⊆ P := mem_powerset.mp (mem_filter.mp hD).1
  have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp => (hP p (hDP hp)).1.pos)
  have hdq : (∏ p ∈ D, p) ≤ q := (mem_filter.mp hD).2.trans hZq
  exact hkernel q (∏ p ∈ D, p) hq hd hdq hV N (x-y) hNl hNu (hdiam x hx y hy)

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.mellin_prime_sampling_arithmetic_jd_oai := @OAI.JointDickman.mellin_prime_sampling_arithmetic_jd_oai
