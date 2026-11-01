-- Prove2me | solution 1 for OAI.JointDickman.squarefreeRiesz_perron_expansion_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:17:28.095817+00:00
-- url     : https://prove2.me/submissions/ba85fe47-b07a-4a60-b12e-4e59f3861127

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.Auxiliary
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
### Auxiliary lemmas
-/

namespace Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x :=
  (hasDerivAt_ofReal x).differentiableAt

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt
end

section
-- module Solutions.OAIQ083_JD.EulerMaclaurin
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

section

open Finset Interval MeasureTheory


variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogProductBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_AnalyticLogBranch
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic logarithms on the zero-free contour domains -/
namespace JointDickman
open Filter Set
open scoped Topology

theorem analyticAt_of_continuousAt_exp {f : ℂ → ℂ} {x : ℂ}
    (hf : ContinuousAt f x) (he : AnalyticAt ℂ (fun y => Complex.exp (f y)) x) :
    AnalyticAt ℂ f x := by
  have hE : AnalyticAt ℂ Complex.exp (f x) := analyticAt_cexp
  have hd : deriv Complex.exp (f x) ≠ 0 := by
    rw [Complex.deriv_exp]
    exact Complex.exp_ne_zero _
  let r := hE.hasStrictDerivAt.localInverse _ _ _ hd
  have hr : AnalyticAt ℂ r (Complex.exp (f x)) := hE.analyticAt_localInverse hd
  have hi : (fun y => r (Complex.exp (f y))) =ᶠ[𝓝 x] f :=
    hf.eventually (hE.hasStrictDerivAt.eventually_left_inverse hd)
  have har : AnalyticAt ℂ (fun y => r (Complex.exp (f y))) x :=
    AnalyticAt.comp (f := fun y => Complex.exp (f y)) hr he
  exact har.congr hi

theorem exists_analytic_log_on {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∀ x ∈ U, g x ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ ∀ x ∈ U, Complex.exp (f x) = g x := by
  obtain ⟨f,hf,he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hg.continuousOn
    (by rintro ⟨x,hx,heq⟩; exact hne x hx heq)
  refine ⟨f,fun x hx => ?_,he⟩
  apply analyticAt_of_continuousAt_exp (hf.continuousAt (hUo.mem_nhds hx))
  apply (hg x hx).congr
  exact (Filter.eventuallyEq_of_mem (hUo.mem_nhds hx) (fun y hy => he hy)).symm

theorem exists_normalized_analytic_log_on {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) {x₀ : ℂ} (hx₀ : x₀ ∈ U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∀ x ∈ U, g x ≠ 0)
    (hg₀ : g x₀ = 1) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ f x₀ = 0 ∧
      ∀ x ∈ U, Complex.exp (f x) = g x := by
  obtain ⟨f,hf,he⟩ := exists_analytic_log_on hUc hUo hg hne
  refine ⟨fun x => f x-f x₀,fun x hx => (hf x hx).sub analyticAt_const,sub_self _,?_⟩
  intro x hx
  rw [Complex.exp_sub,he x hx,he x₀ hx₀,hg₀,div_one]

theorem normalized_log_eq_principal_near {f g : ℂ → ℂ} {x : ℂ}
    (hf : ContinuousAt f x) (hf₀ : f x = 0)
    (he : (fun y => Complex.exp (f y)) =ᶠ[𝓝 x] g) :
    f =ᶠ[𝓝 x] (fun y => Complex.log (g y)) := by
  have him : Tendsto (fun y => (f y).im) (𝓝 x) (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,hf₀,Complex.zero_im] using Complex.continuous_im.continuousAt.tendsto.comp hf
  have hstrip := him.eventually (Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos)
  filter_upwards [he,hstrip] with y hy hh
  rw [←hy,Complex.log_exp hh.1 hh.2.le]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_AnalyticLogUniqueness
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniqueness of normalized analytic logarithms -/
namespace JointDickman
open Set Filter
open scoped Topology

theorem analytic_log_unique {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : ∀ s ∈ U, Complex.exp (f s) = Complex.exp (g s))
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) (h₀ : f x₀ = g x₀) : EqOn f g U := by
  have hd : ∀ s ∈ U, deriv f s = deriv g s := by
    intro s hs
    have heq : (fun t => Complex.exp (f t)) =ᶠ[𝓝 s] (fun t => Complex.exp (g t)) := by
      filter_upwards [hU.mem_nhds hs] with t ht
      exact he t ht
    have hh := ((hf s hs).differentiableAt.hasDerivAt.cexp.congr_of_eventuallyEq heq.symm).unique
      (hg s hs).differentiableAt.hasDerivAt.cexp
    rw [he s hs] at hh
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hh
  exact hU.eqOn_of_deriv_eq hc hf.differentiableOn hg.differentiableOn hd hx₀ h₀

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

theorem exists_zetaPoleLog {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    (h1 : (1:ℂ) ∈ U) (hζ : ∀ s ∈ U, s ≠ 1 → riemannZeta s ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ f 1 = 0 ∧
      ∀ s ∈ U, Complex.exp (f s) = zetaPoleFactor s := by
  apply exists_normalized_analytic_log_on hUc hUo h1
    (fun s _ => zetaPoleFactor_differentiable.analyticAt s) _ zetaPoleFactor_one
  intro s hs
  by_cases he : s = 1
  · subst s
    simp only [zetaPoleFactor_one,ne_eq,one_ne_zero,not_false_eq_true]
  · rw [zetaPoleFactor_eq he]
    exact mul_ne_zero (sub_ne_zero.mpr he) (hζ s hs he)

theorem norm_exp_real_mul_of_exp_eq (z : ℝ) {w v : ℂ} (he : Complex.exp w = v) :
    ‖Complex.exp ((z:ℂ)*w)‖ = ‖v‖^z := by
  rw [←he,Complex.norm_exp,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,←Real.exp_mul]
  congr 1
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalPowerBoundary
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two boundary values on the fractional-power branch cut -/
namespace JointDickman
open Filter Set
open scoped Topology

theorem fractionalPower_boundary_value (z θ : ℝ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (-(z:ℂ)*((Real.log t:ℂ)+(θ:ℂ)*Complex.I)) =
      (t^(-z):ℝ)*Complex.exp ((-(z*θ):ℝ)*Complex.I) := by
  rw [Real.rpow_def_of_pos ht,Complex.ofReal_exp]
  push_cast
  rw [show -(z:ℂ)*((Real.log t:ℂ)+(θ:ℂ)*Complex.I) =
    (Real.log t:ℂ)*(-z) + -(z*θ)*Complex.I by ring,Complex.exp_add]

theorem fractionalPower_upper_cut (z : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fractionalPowerKernel z)
      (𝓝[{w : ℂ | 0 ≤ w.im}] (-(t:ℂ)))
      (𝓝 ((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I))) := by
  change Tendsto (fun w : ℂ => Complex.exp (-(z:ℂ)*Complex.log w)) _ _
  have hh := Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := -(t:ℂ)) (by simpa using neg_neg_of_pos ht) (by simp)
  have h := (hh.const_mul (-(z:ℂ))).cexp
  have hn : ‖-(t:ℂ)‖ = t := by simp [abs_of_pos ht]
  simpa only [hn,fractionalPower_boundary_value z Real.pi ht] using h

theorem fractionalPower_jump (z t : ℝ) :
    (t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I) -
      (t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I) =
      (2:ℂ)*Complex.I*(Real.sin (Real.pi*z):ℂ)*(t^(-z):ℝ) := by
  rw [←mul_sub,Complex.exp_mul_I,Complex.exp_mul_I]
  simp only [Complex.ofReal_neg,Complex.cos_neg,Complex.sin_neg]
  rw [←Complex.ofReal_sin]
  rw [mul_comm Real.pi z]
  ring

theorem fractionalPower_norm (z : ℝ) {w : ℂ} (hw : w ≠ 0) :
    ‖fractionalPowerKernel z w‖ = ‖w‖^(-z) := by
  unfold fractionalPowerKernel
  rw [show -(z:ℂ) = ((-z:ℝ):ℂ) by simp]
  exact norm_exp_real_mul_of_exp_eq (-z) (Complex.exp_log hw)

theorem fractionalPower_horizontal_bound {z : ℝ} (hz : 0 ≤ z) {u v : ℝ} (hu : u ≠ 0) :
    ‖fractionalPowerKernel z ((u:ℂ)+(v:ℂ)*Complex.I)‖ ≤ |u|^(-z) := by
  have hn : |u| ≤ ‖(u:ℂ)+(v:ℂ)*Complex.I‖ := by
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero] using
      Complex.abs_re_le_norm ((u:ℂ)+(v:ℂ)*Complex.I)
  have hw : (u:ℂ)+(v:ℂ)*Complex.I ≠ 0 := by
    intro he
    rw [he,norm_zero] at hn
    exact hu (abs_eq_zero.mp (le_antisymm hn (abs_nonneg u)))
  rw [fractionalPower_norm z hw]
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hu) hn (neg_nonpos.mpr hz)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalPowerHorizontal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Horizontal approach to the fractional-power cut and its integrable majorant -/
namespace JointDickman
open Filter Set MeasureTheory
open scoped Topology

theorem fractionalPower_upper_horizontal (z : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun ε : ℝ => fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*Complex.I)) (𝓝[>] 0)
      (𝓝 ((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I))) := by
  apply (fractionalPower_upper_cut z ht).comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have he : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [zero_mul,add_zero] using he.mul_const Complex.I |>.const_add (-(t:ℂ))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [Complex.add_im,Complex.neg_im,Complex.ofReal_im,neg_zero,
      Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,
      add_zero,zero_add] using hε.le

theorem fractionalPower_positive (z : ℝ) {t : ℝ} (ht : 0 < t) :
    fractionalPowerKernel z (t:ℂ) = (t^(-z):ℝ) := by
  rw [fractionalPowerKernel,←Complex.ofReal_log ht.le,Real.rpow_def_of_pos ht,
    Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  congr 1
  ring

theorem fractionalPower_continuousAt_positive (z : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fractionalPowerKernel z) (t:ℂ) := by
  change ContinuousAt (fun w : ℂ => Complex.exp (-(z:ℂ)*Complex.log w)) (t:ℂ)
  have hl := continuousAt_clog (Complex.ofReal_mem_slitPlane.mpr ht)
  exact (continuousAt_const.mul hl).cexp

theorem integrable_abs_rpow_on_bounded_interval {z a b : ℝ} (hz : z < 1) :
    IntegrableOn (fun u : ℝ => |u|^(-z)) (Icc a b) := by
  have hm : AEStronglyMeasurable (fun u : ℝ => |u|^(-z)) volume := by
    exact (continuous_abs.measurable.pow_const (-z)).aestronglyMeasurable
  have hb : IntegrableOn (fun u : ℝ => |u|^(-z)) (Metric.ball 0 (|a|+|b|+1)) := by
    apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := z) (by simp : 1 ≤ Module.finrank ℝ ℝ)
      (by simpa using hz) _ hm
    filter_upwards with u
    simp only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) _),one_mul]
    exact le_rfl
  apply hb.mono_set
  intro u hu
  rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs]
  have hua : -(|a|+|b|+1) < u := by linarith [neg_abs_le a,abs_nonneg b,hu.1]
  have hub : u < |a|+|b|+1 := by linarith [le_abs_self b,abs_nonneg a,hu.2]
  exact abs_lt.mpr ⟨hua,hub⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalCutIntegral
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dominated convergence on the integrable side of the fractional cut -/
namespace JointDickman
open Filter Set MeasureTheory
open scoped Topology

theorem fractionalCut_upper_integral {z η R : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (hη : 0 < η) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ in Ioc 0 η,
      F (-(t:ℂ)+(ε:ℂ)*Complex.I)*fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*Complex.I))
      (𝓝[>] 0) (𝓝 (∫ t : ℝ in Ioc 0 η,
        F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I)))) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hF
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hpath (ε : ℝ) : Continuous (fun t : ℝ => -(t:ℂ)+(ε:ℂ)*Complex.I) := by fun_prop
  have hmap (ε : ℝ) (hε : 0 < ε) (hεη : ε < η) (t : ℝ) (ht : t ∈ Ioc 0 η) :
      -(t:ℂ)+(ε:ℂ)*Complex.I ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall,dist_zero_right]
    calc
      _ ≤ ‖-(t:ℂ)‖+‖(ε:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = t+ε := by simp [abs_of_pos ht.1,abs_of_pos hε]
      _ ≤ R := by linarith [ht.2]
  have hpow : IntegrableOn (fun t : ℝ => t^(-z)) (Ioc 0 η) := by
    apply ((integrable_abs_rpow_on_bounded_interval (a := 0) (b := η) hz1).mono_set
      Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
    intro t ht
    dsimp only
    rw [abs_of_pos ht.1]
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => B*t^(-z))
  · filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
    have hFε : ContinuousOn (fun t : ℝ => F (-(t:ℂ)+(ε:ℂ)*Complex.I)) (Ioc 0 η) :=
      hF.comp' (hpath ε).continuousOn (hmap ε hε.1 hε.2)
    have hKε : ContinuousOn (fun t : ℝ => fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*Complex.I))
        (Ioc 0 η) := by
      intro t _
      have hslit : -(t:ℂ)+(ε:ℂ)*Complex.I ∈ Complex.slitPlane := by
        right
        simpa using hε.1.ne'
      have hk : ContinuousAt (fractionalPowerKernel z) (-(t:ℂ)+(ε:ℂ)*Complex.I) := by
        change ContinuousAt (fun w : ℂ => Complex.exp (-(z:ℂ)*Complex.log w)) _
        exact (continuousAt_const.mul (continuousAt_clog hslit)).cexp
      exact (ContinuousAt.comp (f := fun t : ℝ => -(t:ℂ)+(ε:ℂ)*Complex.I)
        hk (hpath ε).continuousAt).continuousWithinAt
    exact (hFε.mul hKε).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul]
    apply mul_le_mul (le_trans (hC _ (hmap ε hε.1 hε.2 t ht)) (le_max_left _ _))
      _ (norm_nonneg _) hB
    simpa only [Complex.ofReal_neg,abs_neg,abs_of_pos ht.1] using
      (fractionalPower_horizontal_bound hz (u := -t) (v := ε) (neg_ne_zero.mpr ht.1.ne'))
  · exact hpow.const_mul B
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htR : -(t:ℂ) ∈ Metric.ball 0 R := by
      simp only [Metric.mem_ball,dist_zero_right,norm_neg,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos ht.1]
      linarith [ht.2]
    have hc := hF.continuousAt (Metric.closedBall_mem_nhds_of_mem htR)
    have he : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hp : Tendsto (fun ε : ℝ => -(t:ℂ)+(ε:ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (-(t:ℂ))) := by
      simpa only [zero_mul,add_zero] using he.mul_const Complex.I |>.const_add (-(t:ℂ))
    exact (hc.tendsto.comp hp).mul (fractionalPower_upper_horizontal z ht.1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalCutJump
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The lower side and the sine jump of the local contour integral -/
namespace JointDickman
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology

theorem fractionalPower_conj (z : ℝ) {w : ℂ} (hw : w.im ≠ 0) :
    conj (fractionalPowerKernel z w) = fractionalPowerKernel z (conj w) := by
  have ha : w.arg ≠ Real.pi := Complex.slitPlane_arg_ne_pi (Or.inr hw)
  rw [fractionalPowerKernel,fractionalPowerKernel,Complex.log_conj w ha,←Complex.exp_conj]
  simp only [map_mul,map_neg,Complex.conj_ofReal]

theorem fractionalCut_lower_integral {z η R : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (hη : 0 < η) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ in Ioc 0 η,
      F (-(t:ℂ)-(ε:ℂ)*Complex.I)*fractionalPowerKernel z (-(t:ℂ)-(ε:ℂ)*Complex.I))
      (𝓝[>] 0) (𝓝 (∫ t : ℝ in Ioc 0 η,
        F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I)))) := by
  let G : ℂ → ℂ := fun w => conj (F (conj w))
  have hG : ContinuousOn G (Metric.closedBall 0 R) := by
    apply Complex.continuous_conj.comp_continuousOn
    apply hF.comp Complex.continuous_conj.continuousOn
    intro w hw
    simpa only [Metric.mem_closedBall,dist_zero_right,Complex.norm_conj] using hw
  have h := (Complex.continuous_conj.tendsto _).comp (fractionalCut_upper_integral hz hz1 hη hR hG)
  have hvalue : conj (∫ t : ℝ in Ioc 0 η,
      G (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I))) =
      ∫ t : ℝ in Ioc 0 η,
        F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I)) := by
    rw [←integral_conj]
    apply integral_congr_ae
    filter_upwards with t
    simp only [G,map_mul,map_neg,Complex.conj_ofReal,starRingEnd_self_apply,←Complex.exp_conj,
      Complex.conj_I,Complex.ofReal_neg,neg_mul,mul_neg,neg_neg]
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_apply]
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  have him : (-(t:ℂ)+(ε:ℂ)*Complex.I).im ≠ 0 := by
    simpa using (show 0 < ε from hε).ne'
  rw [map_mul,fractionalPower_conj z him]
  simp only [G,map_add,map_mul,map_neg,Complex.conj_ofReal,starRingEnd_self_apply,
    Complex.conj_I,sub_eq_add_neg,mul_neg]

theorem fractionalCut_boundary_integral_phase (z η θ : ℝ) (F : ℂ → ℂ) :
    (∫ t : ℝ in Ioc 0 η, F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp ((θ:ℂ)*Complex.I))) =
      (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ)))*Complex.exp ((θ:ℂ)*Complex.I) := by
  rw [←integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  rw [Complex.real_smul]
  ring

theorem fractionalCut_boundary_difference (z η : ℝ) (F : ℂ → ℂ) :
    (1/(2*(Real.pi:ℂ)*Complex.I)) *
      ((∫ t : ℝ in Ioc 0 η, F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp (((z*Real.pi):ℝ)*Complex.I))) -
       (∫ t : ℝ in Ioc 0 η, F (-(t:ℂ))*((t^(-z):ℝ)*Complex.exp ((-(z*Real.pi):ℝ)*Complex.I)))) =
      (Real.sin (Real.pi*z)/Real.pi) • (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))) := by
  rw [fractionalCut_boundary_integral_phase,fractionalCut_boundary_integral_phase,←mul_sub]
  have hp : Complex.exp (((z*Real.pi):ℝ)*Complex.I) -
      Complex.exp ((-(z*Real.pi):ℝ)*Complex.I) = (2:ℂ)*Complex.I*(Real.sin (Real.pi*z):ℂ) := by
    simpa only [Real.one_rpow,Complex.ofReal_one,one_mul,mul_one] using fractionalPower_jump z 1
  rw [hp,Complex.real_smul,Complex.ofReal_div]
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem fractionalCut_jump_integral {z η R : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (hη : 0 < η) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => (1/(2*(Real.pi:ℂ)*Complex.I)) *
      ((∫ t : ℝ in Ioc 0 η, F (-(t:ℂ)-(ε:ℂ)*Complex.I)*
        fractionalPowerKernel z (-(t:ℂ)-(ε:ℂ)*Complex.I)) -
       (∫ t : ℝ in Ioc 0 η, F (-(t:ℂ)+(ε:ℂ)*Complex.I)*
        fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*Complex.I))))
      (𝓝[>] 0) (𝓝 ((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))))) := by
  have h := ((fractionalCut_lower_integral hz hz1 hη hR hF).sub
    (fractionalCut_upper_integral hz hz1 hη hR hF)).const_mul (1/(2*(Real.pi:ℂ)*Complex.I))
  rwa [fractionalCut_boundary_difference] at h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.Rectangle
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}


lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔
      z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc

lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩

lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := ⟨right_mem_uIcc, right_mem_uIcc⟩

lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  use fun h ↦ ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  intro ⟨⟨⟨hz're_ge, hz're_le⟩, ⟨hz'im_ge, hz'im_le⟩⟩,
    ⟨⟨hw're_ge, hw're_le⟩, ⟨hw'im_ge, hw'im_le⟩⟩⟩ x
    ⟨⟨hxre_ge, hxre_le⟩, ⟨hxim_ge, hxim_le⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_inf hz're_ge hw're_ge).trans hxre_ge
  · exact (le_sup_iff.mp hxre_le).casesOn (fun h ↦ h.trans hz're_le)
      (fun h ↦ h.trans hw're_le)
  · exact (le_inf hz'im_ge hw'im_ge).trans hxim_ge
  · exact (le_sup_iff.mp hxim_le).casesOn (fun h ↦ h.trans hz'im_le)
      (fun h ↦ h.trans hw'im_le)

set_option linter.style.multiGoal false in
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁)
    (x₁_le_x₂ : x₁ ≤ x₂) (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁)
    (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆
      Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff, mem_Rect, mem_Rect]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simpa using by linarith
end

section
-- module Solutions.OAIQ083_JD.ResidueCalcOnRectangles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

lemma verticalIntegral_split_three (a b : ℝ)
    (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ =
      I • (∫ t in Iic a, f (σ + t * I)) + VIntegral f σ a b +
      I • ∫ t in Ici b, f (σ + t * I) := by
  simp_rw [VerticalIntegral, VIntegral, ← smul_add]
  congr
  rw [← integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel,
    integral_Iic_eq_integral_Iio, integral_Iio_add_Ici hf.restrict hf.restrict]

theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalContourRectangles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite rectangles on either side of the fractional-power cut -/
namespace JointDickman
open Complex Set

theorem fractionalPower_differentiableAt (z : ℝ) {w : ℂ} (hw : w ∈ slitPlane) :
    DifferentiableAt ℂ (fractionalPowerKernel z) w := by
  change DifferentiableAt ℂ (fun w : ℂ => exp (-(z:ℂ)*log w)) w
  exact ((differentiableAt_const _).mul (Complex.differentiableAt_log hw)).cexp

theorem fractionalContour_rectangles {z η c T ε : ℝ}
    (hη : 0 < η) (hc : 0 < c) (hε : 0 < ε) (hεT : ε < T)
    {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I))) :
    (VIntegral (fractionalContourIntegrand z F) c ε T +
       VIntegral (fractionalContourIntegrand z F) c (-T) (-ε)) -
      (VIntegral (fractionalContourIntegrand z F) (-η) ε T +
       VIntegral (fractionalContourIntegrand z F) (-η) (-T) (-ε)) =
      HIntegral (fractionalContourIntegrand z F) (-η) c T -
      HIntegral (fractionalContourIntegrand z F) (-η) c (-T) +
      HIntegral (fractionalContourIntegrand z F) (-η) c (-ε) -
      HIntegral (fractionalContourIntegrand z F) (-η) c ε := by
  have hηc : -η ≤ c := by linarith
  have hT : 0 < T := lt_trans hε hεT
  have hupper : Rectangle (-(η:ℂ)+(ε:ℂ)*I) ((c:ℂ)+(T:ℂ)*I) ⊆
      Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I) := by
    simpa only [Complex.ofReal_neg,sub_eq_add_neg,neg_mul] using
      (RectSubRect (x₀ := -η) (x₁ := -η) (x₂ := c) (x₃ := c)
        (y₀ := -T) (y₁ := ε) (y₂ := T) (y₃ := T)
        le_rfl hηc le_rfl (by linarith) hεT.le le_rfl)
  have hlower : Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)-(ε:ℂ)*I) ⊆
      Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I) := by
    simpa only [Complex.ofReal_neg,sub_eq_add_neg,neg_mul] using
      (RectSubRect (x₀ := -η) (x₁ := -η) (x₂ := c) (x₃ := c)
        (y₀ := -T) (y₁ := -T) (y₂ := -ε) (y₃ := T)
        le_rfl hηc le_rfl le_rfl (by linarith) (by linarith))
  have hu : RectangleIntegral (fractionalContourIntegrand z F)
      (-(η:ℂ)+(ε:ℂ)*I) ((c:ℂ)+(T:ℂ)*I) = 0 := by
    apply HolomorphicOn.vanishesOnRectangle (U := Rectangle _ _) _ subset_rfl
    apply (hF.mono hupper).mul
    intro w hw
    apply (fractionalPower_differentiableAt z (Or.inr ?_)).differentiableWithinAt
    have him := (mem_Rect (by simpa using hηc) (by simpa using hεT.le) w).mp hw
    have : ε ≤ w.im := by simpa using him.2.2.1
    linarith
  have hl : RectangleIntegral (fractionalContourIntegrand z F)
      (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)-(ε:ℂ)*I) = 0 := by
    apply HolomorphicOn.vanishesOnRectangle (U := Rectangle _ _) _ subset_rfl
    apply (hF.mono hlower).mul
    intro w hw
    apply (fractionalPower_differentiableAt z (Or.inr ?_)).differentiableWithinAt
    have him := (mem_Rect (by simpa using hηc) (by simpa using neg_le_neg hεT.le) w).mp hw
    have : w.im ≤ -ε := by simpa using him.2.2.2
    linarith
  simp only [RectangleIntegral,add_re,sub_re,neg_re,ofReal_re,ofReal_im,
    I_re,I_im,mul_re,mul_im,neg_zero,mul_zero,mul_one,zero_add,
    add_zero,sub_zero,zero_sub,add_im,sub_im,neg_im] at hu hl
  linear_combination hu + hl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalPositiveIntegral
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common boundary value to the right of the branch point -/
namespace JointDickman
open Filter Set MeasureTheory
open scoped Topology

theorem fractionalPositive_integral {z c R : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (hc : 0 < c) (hR : 2*c < R) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => ∫ t : ℝ in Ioc 0 c,
      F ((t:ℂ)+(ε:ℂ)*Complex.I)*fractionalPowerKernel z ((t:ℂ)+(ε:ℂ)*Complex.I))
      (𝓝 0) (𝓝 (∫ t : ℝ in Ioc 0 c, F (t:ℂ)*(t^(-z):ℝ))) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hF
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hpath (ε : ℝ) : Continuous (fun t : ℝ => (t:ℂ)+(ε:ℂ)*Complex.I) := by fun_prop
  have hmap (ε : ℝ) (hε : |ε| < c) (t : ℝ) (ht : t ∈ Ioc 0 c) :
      (t:ℂ)+(ε:ℂ)*Complex.I ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall,dist_zero_right]
    calc
      _ ≤ ‖(t:ℂ)‖+‖(ε:ℂ)*Complex.I‖ := norm_add_le _ _
      _ = t+|ε| := by simp [abs_of_pos ht.1]
      _ ≤ R := by linarith [ht.2]
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0, |ε| < c := by
    filter_upwards [Ioo_mem_nhds (by linarith : -c < 0) hc] with ε hε
    exact abs_lt.mpr hε
  have hpow : IntegrableOn (fun t : ℝ => t^(-z)) (Ioc 0 c) := by
    apply ((integrable_abs_rpow_on_bounded_interval (a := 0) (b := c) hz1).mono_set
      Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
    intro t ht
    dsimp only
    rw [abs_of_pos ht.1]
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => B*t^(-z))
  · filter_upwards [hsmall] with ε hε
    have hFε : ContinuousOn (fun t : ℝ => F ((t:ℂ)+(ε:ℂ)*Complex.I)) (Ioc 0 c) :=
      hF.comp' (hpath ε).continuousOn (hmap ε hε)
    have hKε : ContinuousOn (fun t : ℝ => fractionalPowerKernel z ((t:ℂ)+(ε:ℂ)*Complex.I))
        (Ioc 0 c) := by
      intro t ht
      have hslit : (t:ℂ)+(ε:ℂ)*Complex.I ∈ Complex.slitPlane := by
        left
        simpa using ht.1
      have hk : ContinuousAt (fractionalPowerKernel z) ((t:ℂ)+(ε:ℂ)*Complex.I) := by
        change ContinuousAt (fun w : ℂ => Complex.exp (-(z:ℂ)*Complex.log w)) _
        exact (continuousAt_const.mul (continuousAt_clog hslit)).cexp
      exact (ContinuousAt.comp (f := fun t : ℝ => (t:ℂ)+(ε:ℂ)*Complex.I)
        hk (hpath ε).continuousAt).continuousWithinAt
    exact (hFε.mul hKε).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [hsmall] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul]
    apply mul_le_mul (le_trans (hC _ (hmap ε hε t ht)) (le_max_left _ _))
      _ (norm_nonneg _) hB
    simpa only [abs_of_pos ht.1] using fractionalPower_horizontal_bound hz (v := ε) ht.1.ne'
  · exact hpow.const_mul B
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htR : (t:ℂ) ∈ Metric.ball 0 R := by
      simp only [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
      linarith [ht.2]
    have hp : Tendsto (fun ε : ℝ => (t:ℂ)+(ε:ℂ)*Complex.I) (𝓝 0) (𝓝 (t:ℂ)) := by
      simpa only [Complex.ofReal_zero,zero_mul,add_zero] using
        ((Complex.continuous_ofReal.tendsto 0).mul_const Complex.I).const_add (t:ℂ)
    have hlim := ((hF.continuousAt (Metric.closedBall_mem_nhds_of_mem htR)).tendsto.comp hp).mul
      ((fractionalPower_continuousAt_positive z ht.1).tendsto.comp hp)
    rwa [fractionalPower_positive z ht.1] at hlim

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalHorizontalJump
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The horizontal contour jump is the local Hankel integral -/
namespace JointDickman
open Filter Set MeasureTheory Complex
open scoped Topology

theorem fractionalContour_horizontal_split {z η c R ε : ℝ}
    (hη : 0 < η) (hc : 0 < c) (hcη : c ≤ η) (hR : 2*η < R)
    (hε : ε ≠ 0) (hεη : |ε| < η) {F : ℂ → ℂ}
    (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    HIntegral (fractionalContourIntegrand z F) (-η) c ε =
      (∫ t : ℝ in Ioc 0 η, F (-(t:ℂ)+(ε:ℂ)*I)*fractionalPowerKernel z (-(t:ℂ)+(ε:ℂ)*I)) +
      (∫ t : ℝ in Ioc 0 c, F ((t:ℂ)+(ε:ℂ)*I)*fractionalPowerKernel z ((t:ℂ)+(ε:ℂ)*I)) := by
  have hηc : -η ≤ c := by linarith
  have hpath : Continuous (fun t : ℝ => (t:ℂ)+(ε:ℂ)*I) := by fun_prop
  have hmap (t : ℝ) (ht : t ∈ Icc (-η) c) :
      (t:ℂ)+(ε:ℂ)*I ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall,dist_zero_right]
    have htη : |t| ≤ η := abs_le.mpr ⟨ht.1,ht.2.trans hcη⟩
    calc
      _ ≤ ‖(t:ℂ)‖+‖(ε:ℂ)*I‖ := norm_add_le _ _
      _ = |t|+|ε| := by simp
      _ ≤ R := by linarith
  have hcon : ContinuousOn (fun t : ℝ => fractionalContourIntegrand z F ((t:ℂ)+(ε:ℂ)*I))
      (Icc (-η) c) := by
    apply (hF.comp' hpath.continuousOn hmap).mul
    intro t _
    apply (ContinuousAt.comp (f := fun t : ℝ => (t:ℂ)+(ε:ℂ)*I)
      (fractionalPower_differentiableAt z (Or.inr (by simpa using hε))).continuousAt
      hpath.continuousAt).continuousWithinAt
  have hi := hcon.intervalIntegrable_of_Icc (μ := volume) hηc
  have h0 : (0:ℝ) ∈ uIcc (-η) c := by rw [uIcc_of_le hηc]; exact ⟨by linarith,hc.le⟩
  have his := (IntervalIntegrable.trans_iff h0).mp hi
  rw [HIntegral,←intervalIntegral.integral_add_adjacent_intervals his.1 his.2]
  congr 1
  · have hn := intervalIntegral.integral_comp_neg (fun t : ℝ =>
        fractionalContourIntegrand z F ((t:ℂ)+(ε:ℂ)*I)) (a := 0) (b := η)
    simp only [neg_zero] at hn
    rw [←hn]
    simp only [intervalIntegral.integral_of_le hη.le,Complex.ofReal_neg,
      fractionalContourIntegrand]
  · rw [intervalIntegral.integral_of_le hc.le]
    rfl

theorem fractionalContour_horizontal_jump {z η c R : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hη : 0 < η) (hc : 0 < c) (hcη : c ≤ η)
    (hR : 2*η < R) {F : ℂ → ℂ} (hF : ContinuousOn F (Metric.closedBall 0 R)) :
    Tendsto (fun ε : ℝ => (1/(2*(Real.pi:ℂ)*I)) *
      (HIntegral (fractionalContourIntegrand z F) (-η) c (-ε) -
       HIntegral (fractionalContourIntegrand z F) (-η) c ε))
      (𝓝[>] 0) (𝓝 ((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))))) := by
  have hp := fractionalPositive_integral hz hz1 hc (lt_of_le_of_lt (by linarith) hR) hF
  have hpu := hp.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  have hpl := hp.comp hneg
  have hzero := ((hpl.sub hpu).const_mul (1/(2*(Real.pi:ℂ)*I)))
  simp only [sub_self,mul_zero] at hzero
  have hsum := (fractionalCut_jump_integral hz hz1 hη hR hF).add hzero
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
  rw [fractionalContour_horizontal_split hη hc hcη hR (neg_ne_zero.mpr hε.1.ne')
      (by simpa [abs_of_pos hε.1] using hε.2) hF,
    fractionalContour_horizontal_split hη hc hcη hR hε.1.ne'
      (by simpa [abs_of_pos hε.1] using hε.2) hF]
  simp only [Complex.ofReal_neg,Function.comp_apply]
  simp only [sub_eq_add_neg]
  ring_nf

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalVerticalIntegral
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability and removal of the middle gaps on the vertical sides -/
namespace JointDickman
open Filter Set MeasureTheory Complex
open scoped Topology

theorem fractionalContour_vertical_integrable {z x a b : ℝ}
    (hz : 0 ≤ z) (hx : x ≠ 0) {F : ℂ → ℂ}
    (hF : ContinuousOn (fun t : ℝ => F ((x:ℂ)+(t:ℂ)*I)) (Icc a b)) :
    IntegrableOn (fun t : ℝ => fractionalContourIntegrand z F ((x:ℂ)+(t:ℂ)*I)) (Icc a b) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  have hK : Measurable (fun t : ℝ => fractionalPowerKernel z ((x:ℂ)+(t:ℂ)*I)) := by
    apply Complex.continuous_exp.measurable.comp
    apply measurable_const.mul
    apply Complex.measurable_log.comp
    fun_prop
  apply (integrableOn_const (C := max C 0 * |x|^(-z)) (s := Icc a b) (μ := volume) (by simp)).mono'
    ((hF.aestronglyMeasurable measurableSet_Icc).mul hK.aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change ‖F _ * fractionalPowerKernel z _‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul ((hC t ht).trans (le_max_left _ _))
    (fractionalPower_horizontal_bound hz hx) (norm_nonneg _) (le_max_right _ _)

theorem VIntegral_remove_middle_gap {f : ℂ → ℂ} {x T : ℝ} (hT : 0 < T)
    (hf : IntervalIntegrable (fun t : ℝ => f ((x:ℂ)+(t:ℂ)*I)) volume (-T) T) :
    Tendsto (fun ε : ℝ => VIntegral f x ε T + VIntegral f x (-T) (-ε))
      (𝓝[>] 0) (𝓝 (VIntegral f x (-T) T)) := by
  have h0 : (0:ℝ) ∈ uIcc (-T) T := by
    rw [uIcc_of_le (by linarith)]
    exact ⟨by linarith,hT.le⟩
  have hnhds : uIcc (-T) T ∈ 𝓝 (0:ℝ) := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_mem_nhds (by linarith) hT
  have hu : ContinuousAt (fun ε : ℝ => ∫ t in ε..T, f ((x:ℂ)+(t:ℂ)*I)) 0 :=
    (intervalIntegral.continuousOn_primitive_interval_left ((intervalIntegrable_iff').mp hf)).continuousAt hnhds
  have hl : ContinuousAt (fun ε : ℝ => ∫ t in (-T)..ε, f ((x:ℂ)+(t:ℂ)*I)) 0 :=
    (intervalIntegral.continuousOn_primitive_interval ((intervalIntegrable_iff').mp hf)).continuousAt hnhds
  have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0:ℝ)
  have h := (hu.tendsto.const_smul I).add ((hl.tendsto.comp hneg).const_smul I)
  have hs := (IntervalIntegrable.trans_iff h0).mp hf
  have heq : VIntegral f x 0 T + VIntegral f x (-T) 0 = VIntegral f x (-T) T := by
    simp only [VIntegral,←smul_add]
    rw [add_comm,intervalIntegral.integral_add_adjacent_intervals hs.1 hs.2]
  change Tendsto (fun ε : ℝ => VIntegral f x ε T + VIntegral f x (-T) (-ε))
    (𝓝 0) (𝓝 (VIntegral f x 0 T + VIntegral f x (-T) 0)) at h
  rw [heq] at h
  exact h.mono_left (nhdsWithin_le_nhds (s := Ioi 0))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FractionalContourShift
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite contour shift through an integrable fractional pole -/
namespace JointDickman
open Filter Set MeasureTheory Complex
open scoped Topology

theorem fractionalContourShift_of_integrable {z η c T R : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hη : 0 < η) (hc : 0 < c)
    (hcη : c ≤ η) (hT : 0 < T) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I)))
    (hFlocal : ContinuousOn F (Metric.closedBall 0 R))
    (hleft : IntervalIntegrable (fun t : ℝ => fractionalContourIntegrand z F (-(η:ℂ)+(t:ℂ)*I)) volume (-T) T)
    (hright : IntervalIntegrable (fun t : ℝ => fractionalContourIntegrand z F ((c:ℂ)+(t:ℂ)*I)) volume (-T) T) :
    (1/(2*(Real.pi:ℂ)*I)) * VIntegral (fractionalContourIntegrand z F) c (-T) T =
      (1/(2*(Real.pi:ℂ)*I)) *
        (VIntegral (fractionalContourIntegrand z F) (-η) (-T) T +
         HIntegral (fractionalContourIntegrand z F) (-η) c T -
         HIntegral (fractionalContourIntegrand z F) (-η) c (-T)) +
      (Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))) := by
  have hvl := VIntegral_remove_middle_gap (x := -η) hT (by simpa only [ofReal_neg] using hleft)
  have hvr := VIntegral_remove_middle_gap hT hright
  have hlim := (((hvr.sub hvl).sub_const
    (HIntegral (fractionalContourIntegrand z F) (-η) c T -
      HIntegral (fractionalContourIntegrand z F) (-η) c (-T))).const_mul (1/(2*(Real.pi:ℂ)*I)))
  have hj := fractionalContour_horizontal_jump hz hz1 hη hc hcη hR hFlocal
  have he : (fun ε : ℝ => (1/(2*(Real.pi:ℂ)*I)) *
      ((VIntegral (fractionalContourIntegrand z F) c ε T +
        VIntegral (fractionalContourIntegrand z F) c (-T) (-ε)) -
       (VIntegral (fractionalContourIntegrand z F) (-η) ε T +
        VIntegral (fractionalContourIntegrand z F) (-η) (-T) (-ε)) -
       (HIntegral (fractionalContourIntegrand z F) (-η) c T -
        HIntegral (fractionalContourIntegrand z F) (-η) c (-T)))) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => (1/(2*(Real.pi:ℂ)*I)) *
        (HIntegral (fractionalContourIntegrand z F) (-η) c (-ε) -
         HIntegral (fractionalContourIntegrand z F) (-η) c ε)) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with ε hε
    have heq := fractionalContour_rectangles (z := z) hη hc hε.1 hε.2 hF
    rw [heq]
    ring
  have hv := tendsto_nhds_unique hlim (hj.congr' he.symm)
  calc
    _ = (1/(2*(Real.pi:ℂ)*I)) *
          (VIntegral (fractionalContourIntegrand z F) (-η) (-T) T +
           HIntegral (fractionalContourIntegrand z F) (-η) c T -
           HIntegral (fractionalContourIntegrand z F) (-η) c (-T)) +
        (1/(2*(Real.pi:ℂ)*I)) *
          (VIntegral (fractionalContourIntegrand z F) c (-T) T -
           VIntegral (fractionalContourIntegrand z F) (-η) (-T) T -
           (HIntegral (fractionalContourIntegrand z F) (-η) c T -
            HIntegral (fractionalContourIntegrand z F) (-η) c (-T))) := by ring
    _ = _ := by rw [hv]

theorem fractionalContourShift {z η c T R : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hη : 0 < η) (hc : 0 < c)
    (hcη : c ≤ η) (hT : 0 < T) (hR : 2*η < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Rectangle (-(η:ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I)))
    (hFlocal : ContinuousOn F (Metric.closedBall 0 R)) :
    (1/(2*(Real.pi:ℂ)*I)) * VIntegral (fractionalContourIntegrand z F) c (-T) T =
      (1/(2*(Real.pi:ℂ)*I)) *
        (VIntegral (fractionalContourIntegrand z F) (-η) (-T) T +
         HIntegral (fractionalContourIntegrand z F) (-η) c T -
         HIntegral (fractionalContourIntegrand z F) (-η) c (-T)) +
      (Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z):ℝ) • F (-(t:ℂ))) := by
  have hline (x : ℝ) (hx : -η ≤ x ∧ x ≤ c) :
      ContinuousOn (fun t : ℝ => F ((x:ℂ)+(t:ℂ)*I)) (Icc (-T) T) := by
    have hp : Continuous (fun t : ℝ => (x:ℂ)+(t:ℂ)*I) := by fun_prop
    apply hF.continuousOn.comp' hp.continuousOn
    intro t ht
    have hRe : (-(η:ℂ)-(T:ℂ)*I).re ≤ ((c:ℂ)+(T:ℂ)*I).re := by
      simp only [sub_re,neg_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_re,add_zero]
      linarith
    have hIm : (-(η:ℂ)-(T:ℂ)*I).im ≤ ((c:ℂ)+(T:ℂ)*I).im := by
      simp only [sub_im,neg_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_one,mul_zero,
        zero_add,zero_sub,neg_zero,add_im]
      linarith
    apply (mem_Rect hRe hIm _).mpr
    simpa only [sub_re,neg_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_re,add_zero,sub_im,neg_im,mul_im,mul_one,zero_add,zero_sub,neg_zero,add_im]
      using And.intro hx.1 (And.intro hx.2 (And.intro ht.1 ht.2))
  have hleft : IntervalIntegrable
      (fun t : ℝ => fractionalContourIntegrand z F ((-η:ℝ)+(t:ℂ)*I)) volume (-T) T := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -T ≤ T)).mpr
    exact fractionalContour_vertical_integrable hz (neg_ne_zero.mpr hη.ne')
      (hline (-η) ⟨le_rfl,by linarith⟩)
  have hright : IntervalIntegrable
      (fun t : ℝ => fractionalContourIntegrand z F ((c:ℂ)+(t:ℂ)*I)) volume (-T) T := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -T ≤ T)).mpr
    exact fractionalContour_vertical_integrable hz hc.ne' (hline c ⟨by linarith,le_rfl⟩)
  apply fractionalContourShift_of_integrable hz hz1 hη hc hcη hT hR hF hFlocal
  · simpa only [Complex.ofReal_neg] using hleft
  · exact hright

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HankelGammaCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Laplace moments of the fractional-power jump

For the two squarefree exponents, `0 < z < 1`. The upper/lower boundary
values of a power on the negative real axis give the sine factor below.
Euler reflection turns each Laplace moment into the required reciprocal
Gamma coefficient.
-/
namespace JointDickman
open MeasureTheory Set

 theorem gamma_sub_nat_ne_zero {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (j : ℕ) :
    Real.Gamma (z-j) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m he
  rcases lt_or_ge m j with hmj | hjm
  · have hh : (m:ℝ)+1 ≤ j := by exact_mod_cast hmj
    linarith
  · have hh : (j:ℝ) ≤ m := by exact_mod_cast hjm
    linarith

 theorem gamma_reflection_coefficient {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (j : ℕ) :
    Real.sin (Real.pi*(z-j))/Real.pi * Real.Gamma ((j:ℝ)+1-z) = 1/Real.Gamma (z-j) := by
  have ha := gamma_sub_nat_ne_zero hz hz1 j
  have hb : 0 < Real.Gamma ((j:ℝ)+1-z) := Real.Gamma_pos_of_pos (by have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have hr := Real.Gamma_mul_Gamma_one_sub (z-j)
  rw [show 1-(z-j) = (j:ℝ)+1-z by ring] at hr
  have hs : Real.sin (Real.pi*(z-j)) ≠ 0 := by
    intro he
    rw [he,div_zero] at hr
    exact (mul_ne_zero ha hb.ne') hr
  apply (eq_div_iff ha).mpr
  calc
    _ = (Real.Gamma (z-j)*Real.Gamma ((j:ℝ)+1-z))*Real.sin (Real.pi*(z-j))/Real.pi := by ring
    _ = 1 := by rw [hr]; field_simp

 theorem fractional_laplace_integrable {z L : ℝ} (hz1 : z < 1) (hL : 0 < L) (j : ℕ) :
    IntegrableOn (fun t : ℝ => t^((j:ℝ)-z)*Real.exp (-(L*t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (j:ℝ)-z)
    (by have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith) (by norm_num) hL
  simpa only [Real.rpow_one,neg_mul] using h

 theorem fractional_laplace_gamma {z L : ℝ} (hz1 : z < 1) (hL : 0 < L) (j : ℕ) :
    (∫ t : ℝ in Ioi 0, t^((j:ℝ)-z)*Real.exp (-(L*t))) =
      L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j:ℝ)+1-z)
    (by have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith) hL
  have hp : (1/L)^((j:ℝ)+1-z) = L^(z-j-1) := by
    rw [one_div,Real.inv_rpow hL.le,← Real.rpow_neg hL.le]
    congr 1
    ring
  simpa only [show (j:ℝ)+1-z-1 = j-z by ring,hp] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponentially small tails of the Laplace moments -/
namespace JointDickman
open MeasureTheory Set Filter

 theorem fractional_laplace_tail_bound {z L η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (hη : 0 ≤ η) (j : ℕ) :
    (∫ t : ℝ in Ioi η, t^((j:ℝ)-z)*Real.exp (-(L*t))) ≤
      Real.exp (-(L*η/2))*(L/2)^(z-j-1)*Real.Gamma ((j:ℝ)+1-z) := by
  have hL2 : 0 < L/2 := by linarith
  have hg := fractional_laplace_integrable hz1 hL2 j
  have hdom : IntegrableOn
      (fun t : ℝ => Real.exp (-(L*η/2))*(t^((j:ℝ)-z)*Real.exp (-((L/2)*t)))) (Ioi 0) :=
    hg.const_mul _
  have hsub : Ioi η ⊆ Ioi (0:ℝ) := fun t ht => lt_of_le_of_lt hη ht
  calc
    _ ≤ ∫ t : ℝ in Ioi η,
        Real.exp (-(L*η/2))*(t^((j:ℝ)-z)*Real.exp (-((L/2)*t))) := by
      apply integral_mono_ae (IntegrableOn.mono_set (fractional_laplace_integrable hz1 hL j) hsub)
        (IntegrableOn.mono_set hdom hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htt : η < t := ht
      have ht0 : 0 < t := hη.trans_lt htt
      have he : Real.exp (-((L/2)*t)) ≤ Real.exp (-(L*η/2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hsplit : Real.exp (-(L*t)) = Real.exp (-((L/2)*t))*Real.exp (-((L/2)*t)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      calc
        _ = (t^((j:ℝ)-z)*Real.exp (-((L/2)*t)))*Real.exp (-((L/2)*t)) := by ring
        _ ≤ (t^((j:ℝ)-z)*Real.exp (-((L/2)*t)))*Real.exp (-(L*η/2)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)
        _ = _ := by ring
    _ ≤ ∫ t : ℝ in Ioi 0,
        Real.exp (-(L*η/2))*(t^((j:ℝ)-z)*Real.exp (-((L/2)*t))) := by
      apply setIntegral_mono_set hdom
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ht
        positivity
      · exact Eventually.of_forall (fun _ ht => hsub ht)
    _ = _ := by rw [integral_const_mul,fractional_laplace_gamma hz1 hL2 j]; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a fixed upper cutoff from Laplace moments -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics
open scoped Topology

 theorem fractional_laplace_tail_isBigO {z η : ℝ} (hz1 : z < 1) (hη : 0 ≤ η) (j : ℕ) :
    (fun L : ℝ => ∫ t : ℝ in Ioi η, t^((j:ℝ)-z)*Real.exp (-(L*t)))
      =O[atTop] (fun L => Real.exp (-(η/2)*L)) := by
  refine isBigO_iff.mpr ⟨Real.Gamma ((j:ℝ)+1-z),?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hn : 0 ≤ ∫ t : ℝ in Ioi η, t^((j:ℝ)-z)*Real.exp (-(L*t)) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hη.trans ht.le) _) (Real.exp_pos _).le
  have hg : 0 ≤ Real.Gamma ((j:ℝ)+1-z) :=
    (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)).le
  rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(L*η/2))*(L/2)^(z-j-1)*Real.Gamma ((j:ℝ)+1-z) :=
      fractional_laplace_tail_bound hz1 hL0 hη j
    _ ≤ Real.exp (-(L*η/2))*1*Real.Gamma ((j:ℝ)+1-z) := by
      apply mul_le_mul_of_nonneg_right _ hg
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
    _ = _ := by rw [show -(L*η/2) = -(η/2)*L by ring]; ring

 theorem fractional_laplace_tail_isLittleO {z η : ℝ} (hz1 : z < 1) (hη : 0 < η) (j : ℕ) (b : ℝ) :
    (fun L : ℝ => ∫ t : ℝ in Ioi η, t^((j:ℝ)-z)*Real.exp (-(L*t)))
      =o[atTop] (fun L => L^b) :=
  (fractional_laplace_tail_isBigO hz1 hη.le j).trans_isLittleO
    (isLittleO_exp_neg_mul_rpow_atTop (by linarith : 0 < η/2) b)

 theorem fractional_laplace_cutoff_error {z η : ℝ} (hz1 : z < 1) (hη : 0 < η) (j : ℕ) (b : ℝ) :
    (fun L : ℝ => (∫ t : ℝ in Ioc 0 η, t^((j:ℝ)-z)*Real.exp (-(L*t))) -
      L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) =o[atTop] (fun L => L^b) := by
  apply ((fractional_laplace_tail_isLittleO hz1 hη j b).neg_left).congr' _ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have he := intervalIntegral.integral_Ioi_sub_Ioi (fractional_laplace_integrable hz1 hL j) hη.le
  rw [intervalIntegral.integral_of_le hη.le,fractional_laplace_gamma hz1 hL j] at he
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceRemainder
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A local Taylor error remains one order smaller after Laplace integration -/
namespace JointDickman
open MeasureTheory Set Filter

 theorem laplace_remainder_bound {z L C η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (hC : 0 ≤ C) (k : ℕ) (f : ℝ → ℂ)
    (hf : ∀ t ∈ Ioc 0 η, ‖f t‖ ≤ C*t^k) :
    ‖∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • f t‖ ≤
      C*L^(z-k-1)*Real.Gamma ((k:ℝ)+1-z) := by
  have hg := (fractional_laplace_integrable hz1 hL k).const_mul C
  have hnorm (t : ℝ) (ht : t ∈ Ioc 0 η) :
      ‖(t^(-z)*Real.exp (-(L*t))) • f t‖ ≤ C*(t^((k:ℝ)-z)*Real.exp (-(L*t))) := by
    have ht0 : 0 < t := ht.1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
      _ ≤ (t^(-z)*Real.exp (-(L*t)))*(C*t^k) :=
        mul_le_mul_of_nonneg_left (hf t ht) (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast,show (k:ℝ)-z = -z+k by ring,Real.rpow_add ht0]
        ring
  calc
    _ ≤ ∫ t : ℝ in Ioc 0 η, C*(t^((k:ℝ)-z)*Real.exp (-(L*t))) := by
      apply norm_integral_le_of_norm_le (IntegrableOn.mono_set hg Ioc_subset_Ioi_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hnorm t ht
    _ ≤ ∫ t : ℝ in Ioi 0, C*(t^((k:ℝ)-z)*Real.exp (-(L*t))) := by
      apply setIntegral_mono_set hg
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)
      · exact Eventually.of_forall (fun _ ht => Ioc_subset_Ioi_self ht)
    _ = _ := by rw [integral_const_mul,fractional_laplace_gamma hz1 hL k]; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceIntegrability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability for the locally bounded Laplace remainders -/
namespace JointDickman
open MeasureTheory Set

 theorem laplace_weighted_integrable {z L C η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (k : ℕ) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 η)))
    (hbound : ∀ t ∈ Ioc 0 η, ‖f t‖ ≤ C*t^k) :
    IntegrableOn (fun t => (t^(-z)*Real.exp (-(L*t))) • f t) (Ioc 0 η) := by
  have hg : IntegrableOn (fun t : ℝ => C*(t^((k:ℝ)-z)*Real.exp (-(L*t)))) (Ioc 0 η) :=
    IntegrableOn.mono_set ((fractional_laplace_integrable hz1 hL k).const_mul C) Ioc_subset_Ioi_self
  have hw : Measurable (fun t : ℝ => t^(-z)*Real.exp (-(L*t))) := by fun_prop
  apply hg.mono' (hw.aestronglyMeasurable.smul hf)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  change ‖(t^(-z)*Real.exp (-(L*t))) • f t‖ ≤ C*(t^((k:ℝ)-z)*Real.exp (-(L*t)))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (t^(-z)*Real.exp (-(L*t)))*(C*t^k) :=
      mul_le_mul_of_nonneg_left (hbound t ht) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast,show (k:ℝ)-z = -z+k by ring,Real.rpow_add ht0]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceMonomial
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the monomials in the analytic singular factor -/
namespace JointDickman
open MeasureTheory Set

 theorem laplace_monomial_eq {z L t : ℝ} (ht : 0 < t) (j : ℕ) (a : ℂ) :
    (t^(-z)*Real.exp (-(L*t))) • (a*(t:ℂ)^j) =
      (t^((j:ℝ)-z)*Real.exp (-(L*t))) • a := by
  have he : t^((j:ℝ)-z)*Real.exp (-(L*t)) = (t^(-z)*Real.exp (-(L*t)))*t^j := by
    rw [show (j:ℝ)-z = -z+j by ring,Real.rpow_add ht,Real.rpow_natCast]
    ring
  rw [he]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

 theorem laplace_monomial_integrable {z L : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (j : ℕ) (a : ℂ) {S : Set ℝ} (hSm : MeasurableSet S) (hS : S ⊆ Ioi 0) :
    IntegrableOn (fun t : ℝ => (t^(-z)*Real.exp (-(L*t))) • (a*(t:ℂ)^j)) S := by
  have h := (fractional_laplace_integrable hz1 hL j).smul_const a
  apply (IntegrableOn.mono_set h hS).congr_fun _ hSm
  intro t ht
  exact (laplace_monomial_eq (hS ht) j a).symm

 theorem laplace_monomial_integral {z L : ℝ} (j : ℕ) (a : ℂ) {S : Set ℝ}
    (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0) :
    (∫ t : ℝ in S, (t^(-z)*Real.exp (-(L*t))) • (a*(t:ℂ)^j)) =
      (∫ t : ℝ in S, t^((j:ℝ)-z)*Real.exp (-(L*t))) • a := by
  calc
    _ = ∫ t : ℝ in S, (t^((j:ℝ)-z)*Real.exp (-(L*t))) • a := by
      apply setIntegral_congr_fun hS
      intro t ht
      exact laplace_monomial_eq (hS0 ht) j a
    _ = _ := integral_smul_const _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceMovingCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Laplace tails with the shrinking cutoff of the zero-free contour -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics
open scoped Topology

theorem stretched_exp_isLittleO_rpow {a α : ℝ} (ha : 0 < a) (hα : 0 < α) (b : ℝ) :
    (fun L : ℝ => Real.exp (-a*L^α)) =o[atTop] (fun L => L^b) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop ha (b/α)).comp_tendsto
    (tendsto_rpow_atTop hα)
  apply h.congr' (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  dsimp only [Function.comp_apply]
  rw [←Real.rpow_mul hL.le]
  congr 1
  field_simp

theorem fractional_laplace_moving_tail_isBigO {z : ℝ} (hz1 : z < 1)
    {η : ℝ → ℝ} (hη : ∀ᶠ L in atTop, 0 ≤ η L) (j : ℕ) :
    (fun L : ℝ => ∫ t : ℝ in Ioi (η L), t^((j:ℝ)-z)*Real.exp (-(L*t)))
      =O[atTop] (fun L => Real.exp (-(L*η L/2))) := by
  refine isBigO_iff.mpr ⟨Real.Gamma ((j:ℝ)+1-z),?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),hη] with L hL hηL
  have hL0 : 0 < L := by linarith
  have hn : 0 ≤ ∫ t : ℝ in Ioi (η L), t^((j:ℝ)-z)*Real.exp (-(L*t)) := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (hηL.trans ht.le) _) (Real.exp_pos _).le
  have hg : 0 ≤ Real.Gamma ((j:ℝ)+1-z) :=
    (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith)).le
  rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-(L*η L/2))*(L/2)^(z-j-1)*Real.Gamma ((j:ℝ)+1-z) :=
      fractional_laplace_tail_bound hz1 hL0 hηL j
    _ ≤ Real.exp (-(L*η L/2))*1*Real.Gamma ((j:ℝ)+1-z) := by
      apply mul_le_mul_of_nonneg_right _ hg
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
    _ = _ := by ring

theorem fractional_laplace_moving_tail_isLittleO {z a α : ℝ} (hz1 : z < 1)
    (ha : 0 < a) (hα : 0 < α) {η : ℝ → ℝ}
    (hη : ∀ᶠ L in atTop, 0 ≤ η L)
    (hgrowth : ∀ᶠ L in atTop, a*L^α ≤ L*η L/2) (j : ℕ) (b : ℝ) :
    (fun L : ℝ => ∫ t : ℝ in Ioi (η L), t^((j:ℝ)-z)*Real.exp (-(L*t)))
      =o[atTop] (fun L => L^b) := by
  apply (fractional_laplace_moving_tail_isBigO hz1 hη j).trans_isLittleO
  apply IsBigO.trans_isLittleO (g := fun L : ℝ => Real.exp (-a*L^α)) _
    (stretched_exp_isLittleO_rpow ha hα b)
  apply isBigO_iff.mpr ⟨1,?_⟩
  filter_upwards [hgrowth] with L hL
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul]
  exact Real.exp_le_exp.mpr (by linarith)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceMovingLocal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing a fixed local Hankel cutoff by the moving contour width -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics
open scoped Topology

theorem laplace_cutoff_difference_bound {z L C r δ : ℝ}
    (hz1 : z < 1) (hL : 0 < L) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hδr : δ ≤ r)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 r)))
    (hbound : ∀ t ∈ Ioc 0 r, ‖f t‖ ≤ C) :
    ‖(∫ t : ℝ in Ioc 0 r, (t^(-z)*Real.exp (-(L*t))) • f t) -
      (∫ t : ℝ in Ioc 0 δ, (t^(-z)*Real.exp (-(L*t))) • f t)‖ ≤
      C*(∫ t : ℝ in Ioi δ, t^(-z)*Real.exp (-(L*t))) := by
  let W : ℝ → ℂ := fun t => (t^(-z)*Real.exp (-(L*t))) • f t
  have h0r := laplace_weighted_integrable hz1 hL 0 f hf
    (by simpa only [pow_zero,mul_one] using hbound)
  have h0δ : IntegrableOn W (Ioc 0 δ) :=
    h0r.mono_set (Ioc_subset_Ioc_right hδr)
  have hδr' : IntegrableOn W (Ioc δ r) :=
    h0r.mono_set (Ioc_subset_Ioc_left hδ)
  have heq : (∫ t : ℝ in Ioc 0 r, W t) - (∫ t : ℝ in Ioc 0 δ, W t) =
      ∫ t : ℝ in Ioc δ r, W t := by
    have hs := intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ).mpr h0δ)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδr).mpr hδr')
    simp only [intervalIntegral.integral_of_le hδ,intervalIntegral.integral_of_le hδr,
      intervalIntegral.integral_of_le (hδ.trans hδr)] at hs
    exact sub_eq_of_eq_add' hs.symm
  change ‖(∫ t : ℝ in Ioc 0 r, W t) - (∫ t : ℝ in Ioc 0 δ, W t)‖ ≤ _
  rw [heq]
  have hmajor : IntegrableOn (fun t : ℝ => C*(t^(-z)*Real.exp (-(L*t)))) (Ioi δ) := by
    have hmajor0 : IntegrableOn (fun t : ℝ => C*(t^(-z)*Real.exp (-(L*t)))) (Ioi 0) := by
      simpa only [IntegrableOn,Nat.cast_zero,zero_sub] using
        (fractional_laplace_integrable hz1 hL 0).const_mul C
    exact hmajor0.mono_set (Ioi_subset_Ioi hδ)
  calc
    _ ≤ ∫ t : ℝ in Ioc δ r, C*(t^(-z)*Real.exp (-(L*t))) := by
      apply norm_integral_le_of_norm_le (hmajor.mono_set Ioc_subset_Ioi_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := hδ.trans_lt ht.1
      have hweight : 0 ≤ t^(-z)*Real.exp (-(L*t)) :=
        mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le
      dsimp only [W]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hweight]
      calc
        _ ≤ (t^(-z)*Real.exp (-(L*t)))*C :=
          mul_le_mul_of_nonneg_left (hbound t ⟨hδ.trans_lt ht.1,ht.2⟩) hweight
        _ = _ := mul_comm _ _
    _ ≤ ∫ t : ℝ in Ioi δ, C*(t^(-z)*Real.exp (-(L*t))) := by
      apply setIntegral_mono_set hmajor
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := hδ.trans_lt ht
        exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)
      · exact Eventually.of_forall (fun t ht => ht.1)
    _ = _ := integral_const_mul C _

theorem laplace_moving_local_isLittleO {z C r a α : ℝ} (hz1 : z < 1)
    (hC : 0 ≤ C) (ha : 0 < a) (hα : 0 < α)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 r)))
    (hbound : ∀ t ∈ Ioc 0 r, ‖f t‖ ≤ C) {η : ℝ → ℝ}
    (hη : ∀ᶠ L in atTop, 0 ≤ η L ∧ η L ≤ r)
    (hgrowth : ∀ᶠ L in atTop, a*L^α ≤ L*η L/2) (b : ℝ) :
    (fun L : ℝ => (∫ t : ℝ in Ioc 0 r, (t^(-z)*Real.exp (-(L*t))) • f t) -
      (∫ t : ℝ in Ioc 0 (η L), (t^(-z)*Real.exp (-(L*t))) • f t))
      =o[atTop] (fun L => L^b) := by
  apply IsBigO.trans_isLittleO (g := fun L : ℝ =>
    ∫ t : ℝ in Ioi (η L), t^(-z)*Real.exp (-(L*t))) _
    (by simpa only [Nat.cast_zero,zero_sub] using
      fractional_laplace_moving_tail_isLittleO hz1 ha hα (hη.mono fun _ h => h.1) hgrowth 0 b)
  apply isBigO_iff.mpr ⟨C,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),hη] with L hL hηL
  exact (laplace_cutoff_difference_bound hz1 hL hC hηL.1 hηL.2 f hf hbound).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) hC)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplacePolynomial
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Taylor polynomials under a truncated Laplace integral -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem laplace_polynomial_integrable {z L η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (a : ℕ → ℂ) (H : ℕ) :
    IntegrableOn (fun t : ℝ => (t^(-z)*Real.exp (-(L*t))) •
      (∑ j ∈ range (H+1), a j*(t:ℂ)^j)) (Ioc 0 η) := by
  have h := integrable_finsetSum (range (H+1)) (fun j _ =>
    laplace_monomial_integrable hz1 hL j (a j) (S := Ioc 0 η) measurableSet_Ioc Ioc_subset_Ioi_self)
  simpa only [IntegrableOn,smul_sum] using h

theorem laplace_polynomial_integral {z L η : ℝ} (hz1 : z < 1) (hL : 0 < L)
    (a : ℕ → ℂ) (H : ℕ) :
    (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
      (∑ j ∈ range (H+1), a j*(t:ℂ)^j)) =
      ∑ j ∈ range (H+1), (∫ t : ℝ in Ioc 0 η,
        t^((j:ℝ)-z)*Real.exp (-(L*t))) • a j := by
  simp_rw [smul_sum]
  rw [integral_finsetSum (range (H+1)) (fun j _ =>
    laplace_monomial_integrable hz1 hL j (a j) measurableSet_Ioc Ioc_subset_Ioi_self)]
  exact sum_congr rfl (fun j _ => laplace_monomial_integral j (a j)
    measurableSet_Ioc Ioc_subset_Ioi_self)

theorem laplace_polynomial_cutoff_error {z η : ℝ} (hz1 : z < 1) (hη : 0 < η)
    (a : ℕ → ℂ) (H : ℕ) (b : ℝ) :
    (fun L : ℝ => (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
      (∑ j ∈ range (H+1), a j*(t:ℂ)^j)) -
      ∑ j ∈ range (H+1), (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • a j)
      =o[atTop] (fun L => L^b) := by
  have h (j : ℕ) : (fun L : ℝ => ((∫ t : ℝ in Ioc 0 η,
      t^((j:ℝ)-z)*Real.exp (-(L*t))) -
        L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • a j) =o[atTop] (fun L => L^b) := by
    have hc := (Complex.isLittleO_ofReal_left.mpr
      (fractional_laplace_cutoff_error hz1 hη j b)).const_mul_left (a j)
    simpa only [Complex.real_smul,mul_comm] using hc
  apply (IsLittleO.sum (s := range (H+1)) (fun j _ => h j)).congr' _
    (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [laplace_polynomial_integral hz1 hL a H]
  simp only [Finset.sum_apply,sub_smul,sum_sub_distrib]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceTaylor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed-order Watson estimate for a locally controlled Taylor remainder -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem laplace_taylor_isBigO {z η C : ℝ} (hz1 : z < 1) (hη : 0 < η) (hC : 0 ≤ C)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 η)))
    (a : ℕ → ℂ) (H : ℕ)
    (hb : ∀ t ∈ Ioc 0 η, ‖f t - ∑ j ∈ range (H+1), a j*(t:ℂ)^j‖ ≤ C*t^(H+1)) :
    (fun L : ℝ => (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • f t) -
      ∑ j ∈ range (H+1), (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • a j)
      =O[atTop] (fun L => L^(z-H-2)) := by
  let p : ℝ → ℂ := fun t => ∑ j ∈ range (H+1), a j*(t:ℂ)^j
  have hpmeas : AEStronglyMeasurable p (volume.restrict (Ioc 0 η)) := by
    have hpcont : Continuous p := by unfold p; fun_prop
    exact hpcont.aestronglyMeasurable
  have hR : (fun L : ℝ => ∫ t : ℝ in Ioc 0 η,
      (t^(-z)*Real.exp (-(L*t))) • (f t-p t)) =O[atTop] (fun L => L^(z-H-2)) := by
    refine isBigO_iff.mpr ⟨C*Real.Gamma ((H:ℝ)+2-z),?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    have hh := laplace_remainder_bound hz1 hL hC (H+1) (fun t => f t-p t) hb
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hL _)]
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast <;> ring_nf)
  have hP := (laplace_polynomial_cutoff_error hz1 hη a H (z-H-2)).isBigO
  apply (hR.add hP).congr' _ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have hr := laplace_weighted_integrable hz1 hL (H+1) (fun t => f t-p t)
    (hf.sub hpmeas) hb
  have hp := laplace_polynomial_integrable (η := η) hz1 hL a H
  have he : (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • f t) =
      (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • (f t-p t)) +
      (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • p t) := by
    rw [← integral_add hr hp]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by dsimp only; rw [smul_sub]; dsimp only [p]; abel)
  rw [he]
  dsimp only [p]
  abel

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.Mathlib_Analysis_SpecialFunctions_Log_Basic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith
end

section
-- module Solutions.OAIQ083_JD.ZetaBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


open Complex Topology Filter Interval Set Asymptotics

lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]

lemma one_div_cpow_eq_cpow_neg (x s : ℂ) : 1 / x ^ s = x ^ (-s) := by
  convert div_cpow_eq_cpow_neg 1 x s using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]

lemma div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by
  rw [div_eq_mul_inv, Real.rpow_neg hx, Real.rpow_neg hy, Real.div_rpow hy hx]; field_simp

lemma div_rpow_eq_rpow_div_neg {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ s / y ^ s = (y / x) ^ (-s) := by
  convert div_rpow_neg_eq_rpow_div (s := -s) hx hy using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [neg_neg])

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta




theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz

theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt


/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg] <;> ring

-- move near `Real.differentiableAt_rpow_const_of_ne`
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])

lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]

lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  all_goals try with_reducible_and_instances rfl
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring


lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast <;> ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx

set_option backward.isDefEq.respectTransparency false in
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ'] <;> ring_nf

lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x :=
  lt_of_lt_of_le apos hx.1

lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1

lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]

lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩

lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp

lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s

lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (ZetaSum_aux1_1' apos h)

lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| ZetaSum_aux1_1' apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [ZetaSum_aux1_1' apos hx]

open MeasureTheory in
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

open MeasureTheory in
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub

lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply ZetaSum_aux1_5b apos a_lt_b σpos |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num

lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact ZetaSum_aux1_5a apos
  · exact ZetaSum_aux1_5d apos a_lt_b σpos
  · exact ZetaSum_aux1_5b apos a_lt_b σpos

lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine ZetaSum_aux1_2 (c := s.re) apos a_lt_b ⟨ne_of_gt σpos, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| ZetaSum_aux1_1 apos a_lt_b h

lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma Finset.Icc_eq_Ico (M N : ℕ) : Finset.Icc N M = Finset.Ico N (M + 1) := by
  ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega

lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith

lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re] <;> linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]

lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop

lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3

lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]

lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real] <;> simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor

lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop

open MeasureTheory in
lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      all_goals try with_reducible_and_instances rfl
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]

lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by
  rw [norm_mul, mul_div_assoc]
  rw [Set.mem_Ioc] at hσ
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [Complex.norm_of_nonneg hσ.1.le, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    mul_one]
  linarith [hσ.2]

lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)

open MeasureTheory in
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1

open MeasureTheory in
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane] <;> linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq] <;> linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real] <;> simp

open MeasureTheory in
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_ofPred_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    all_goals try with_reducible_and_instances rfl
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    all_goals try with_reducible_and_instances rfl
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    all_goals try with_reducible_and_instances rfl
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
    all_goals try with_reducible_and_instances rfl
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    all_goals try with_reducible_and_instances rfl
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f] <;> ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f] <;> ring_nf

lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  all_goals try with_reducible_and_instances rfl
  simp [mul_comm]

lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero

lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1
    all_goals try with_reducible_and_instances rfl

lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`
lemma HolomorphicOn_riemannZeta :
    HolomorphicOn ζ {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_ofPred_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt

lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq, mem_ofPred_eq] at hw
  by_cases w_im : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_ofPred_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, w_im] using h, w_im⟩
      · by_cases hxx : x = 0
        · simp only [hxx] <;> linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx] <;> linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity

lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by
  let f := riemannZeta
  let g := ζ₀ N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, ofPred_subset_ofPred, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected isOpen_aux).mpr isPathConnected_aux
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [ofPred_subset_ofPred, imp_self, forall_const, mem_ofPred_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast

lemma DerivZeta0EqDerivZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re)
    (s_ne_one : s ≠ 1) :
    deriv (ζ₀ N) s = ζ' s := by
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have {x : ℂ} (hx : x ∈ U) : ζ₀ N x = ζ x := by
    simp only [mem_ofPred_eq, U] at hx; exact Zeta0EqZeta (N := N) N_pos hx.2 hx.1
  refine deriv_eqOn isOpen_aux ?_ (by simp [s_ne_one, reS_pos])
  intro x hx
  have hζ := HolomorphicOn_riemannZeta.mono (by aesop)|>.hasDerivAt (s := U) <|
    isOpen_aux.mem_nhds hx
  exact hζ.hasDerivWithinAt.congr (fun y hy ↦ this hy) (this hx)

lemma le_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a ≤ b → b ≤ c → c ≤ d → a ≤ d :=
  fun hab hbc hcd ↦ le_trans (le_trans hab hbc) hcd

lemma norm_add₅_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  apply le_trans <| norm_add_le (a + b + c + d) e
  simp only [add_le_add_iff_right]; apply norm_add₄_le

lemma norm_add₆_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E)
    (f : E) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  apply le_trans <| norm_add_le (a + b + c + d + e) f
  simp only [add_le_add_iff_right]; apply norm_add₅_le

lemma ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ |t|)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * Real.exp A := by
  set s := σ + t * I
  by_cases n0 : n = 0
  · simp_rw [n0, CharP.cast_eq_zero, inv_zero, zero_mul]
    rw [Complex.zero_cpow ?_]
    · simp
    · exact fun h ↦ σpos.ne' <| zero_eq_neg.mp <| zero_re ▸ h ▸ (by simp [s])
  have n_gt_0 : 0 < n := Nat.pos_of_ne_zero n0
  have n_gt_0' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n_gt_0
  have n_ge_1 : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr <| Nat.succ_le_of_lt n_gt_0
  calc
    _ = |((n : ℝ) ^ (-σ))| := ?_
    _ ≤ Real.exp (Real.log n * -σ) := Real.abs_rpow_le_exp_log_mul (n : ℝ) (-σ)
    _ ≤ Real.exp (Real.log n *  -(1 - A / Real.log t)) := ?_
    _ ≤ Real.exp (- Real.log n + A) := Real.exp_le_exp_of_le ?_
    _ ≤ _ := by rw [Real.exp_add, Real.exp_neg, Real.exp_log n_gt_0']
  · have : ‖(n : ℂ) ^ (-s)‖ = n ^ (-s.re) := norm_cpow_eq_rpow_re_of_pos n_gt_0' (-s)
    rw [this, abs_eq_self.mpr <| Real.rpow_nonneg n_gt_0'.le _]; simp [s]
  · apply Real.exp_le_exp_of_le <| mul_le_mul_of_nonneg_left _ <| Real.log_nonneg n_ge_1
    rw [neg_sub, neg_le_sub_iff_le_add, add_comm, ← Real.log_abs]; linarith
  · simp only [neg_sub, le_neg_add_iff_add_le]
    ring_nf
    conv => rw [mul_comm, ← mul_assoc, ← Real.log_abs]; rhs; rw [← one_mul A]
    gcongr
    by_cases ht1 : |t| = 1
    · simp [ht1]
    apply (inv_mul_le_iff₀ ?_).mpr
    · convert! Real.log_le_log n_gt_0' n_le_t using 1; rw [mul_one]
    · exact Real.log_pos <| lt_of_le_of_ne (le_trans n_ge_1 n_le_t) <| fun t ↦ ht1 (t.symm)

lemma logt_gt_one {t : ℝ} (t_ge : 3 ≤ t) : 1 < Real.log t :=
  (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])

lemma UpperBnd_aux {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / Real.log |t| ≤ σ) :
    let N := ⌊|t|⌋₊;
    0 < N ∧ N ≤ |t| ∧ 1 < Real.log |t| ∧ 1 - A < σ ∧ 0 < σ ∧ σ + t * I ≠ 1 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  have logt_gt := logt_gt_one t_gt.le
  have σ_gt : 1 - A < σ := by
    apply lt_of_lt_of_le ((sub_lt_sub_iff_left (a := 1)).mpr ?_) σ_ge
    exact (div_lt_iff₀ (by linarith)).mpr <| lt_mul_right hA.1 logt_gt
  refine ⟨Npos, N_le_t, logt_gt, σ_gt, by linarith [hA.2], ?_⟩
  contrapose! t_gt
  simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im] at t_gt
  norm_num [t_gt.2]

lemma UpperBnd_aux2 {A σ t : ℝ} (t_ge : 3 < |t|) (σ_ge : 1 - A / Real.log |t| ≤ σ) :
      |t| ^ (1 - σ) ≤ Real.exp A := by
  have : |t| ^ (1 - σ) ≤ |t| ^ (A / Real.log |t|) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  apply le_trans this ?_
  conv => lhs; lhs; rw [← Real.exp_log (by linarith : 0 < |t|)]
  rw [div_eq_mul_inv, Real.rpow_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, mul_comm,
    ← mul_assoc, inv_mul_cancel₀, one_mul]
  apply Real.log_ne_zero.mpr; split_ands <;> linarith

lemma riemannZeta0_zero_aux (N : ℕ) (Npos : 0 < N) :
    ∑ x ∈ Finset.Ico 0 N, ((x : ℝ))⁻¹ = ∑ x ∈ Finset.Ico 1 N, ((x : ℝ))⁻¹ := by
  have : Finset.Ico 1 N ⊆ Finset.Ico 0 N := by
    intro x hx
    simp only [Finset.mem_Ico, Nat.Ico_zero_eq_range, Finset.mem_range] at hx ⊢
    exact hx.2
  rw [← Finset.sum_sdiff (s₁ := Finset.Ico 1 N) (s₂ := Finset.Ico 0 N) this]
  have : Finset.Ico 0 N \ Finset.Ico 1 N = Finset.range 1 := by
    ext a
    simp only [Nat.Ico_zero_eq_range, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico, not_and,
      not_lt, Finset.range_one, Finset.mem_singleton]
    exact ⟨fun _ ↦ by omega, fun ha ↦ ⟨by simp [ha, Npos], by omega⟩⟩
  rw [this]; simp

lemma UpperBnd_aux3 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(σ + t * I))‖ ≤
      Real.exp A * C * Real.log |t| := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have (n : ℕ) (hn : n ∈ Finset.range (N + 1)) := ZetaBnd_aux2 (n := n) hA.1 σPos ?_ σ_ge
  · replace := norm_sum_le_of_le (Finset.range (N + 1)) this
    rw [← Finset.sum_mul, mul_comm _ (Real.exp A)] at this
    rw [mul_assoc]
    apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
    have : 1 + Real.log (N : ℝ) ≤ C * Real.log |t| := by
      by_cases hN : N = 1
      · simp only [hN, Nat.cast_one, Real.log_one, add_zero]
        have : 2 * 1 ≤ C * Real.log |t| := mul_le_mul hC logt_gt.le (by linarith) (by linarith)
        linarith
      · rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
          ← one_mul <| Real.log (N: ℝ)]
        apply add_le_add logt_gt.le
        refine mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
        exact Real.log_le_log (by positivity) N_le_t
    refine le_trans ?_ this
    convert! harmonic_eq_sum_Icc ▸ harmonic_le_one_add_log N
    · simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.range_eq_Ico]
      rw [riemannZeta0_zero_aux (N + 1) (by linarith)]; congr! 1
  · simp only [Finset.mem_range] at hn
    linarith [(by exact_mod_cast (by omega : n ≤ N) : (n : ℝ) ≤ N)]

lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  constructor
  · apply le_div_iff₀ (by simp [Npos]) |>.mpr; simp [N_le_t]
  · apply div_le_iff₀ (by positivity) |>.mpr
    suffices |t| < N + 1 by linarith [(by exact_mod_cast (by omega) : 1 ≤ (N : ℝ))]
    apply Nat.lt_floor_add_one

lemma UpperBnd_aux5 {σ t : ℝ} (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by
  obtain ⟨h₁, h₂⟩ := Nat.self_div_floor_bound (by linarith)
  calc _ ≤ ((|t| / ↑⌊|t|⌋₊) ^ (2 : ℝ)) := by gcongr
       _ ≤ (2 : ℝ) ^ (2 : ℝ) := by gcongr
       _ = 4 := by norm_num

lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by
  have bnd := UpperBnd_aux5 t_ge hσ.2
  have bnd' : (|t| / ⌊|t|⌋₊) ^ σ ≤ 2 * |t| := by linarith
  split_ands
  · apply (div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm).mpr
    conv => rw [mul_assoc]; rhs; rw [mul_comm]
    apply (div_le_iff₀ <| Real.rpow_pos_of_pos (by linarith) _).mp
    rw [div_rpow_eq_rpow_div_neg (by positivity) (by positivity), neg_sub]
    refine le_trans₄ ?_ bnd' ?_
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_div (by positivity) |>.mpr N_le_t) (by simp)
    · apply (mul_le_mul_iff_right₀ (by norm_num)).mpr; simpa using abs_im_le_norm (1 - (σ + t * I))
  · apply div_le_iff₀ (by norm_num) |>.mpr
    rw [Real.rpow_sub (by linarith), Real.rpow_one, div_mul_eq_mul_div, mul_comm]
    apply div_le_iff₀ (by positivity) |>.mp
    convert! bnd' using 1
    all_goals try with_reducible_and_instances rfl
    rw [← Real.rpow_neg (by linarith), div_rpow_neg_eq_rpow_div (by positivity) (by positivity)]
  · apply div_le_iff₀ (by linarith [hσ.1]) |>.mpr
    rw [mul_assoc, mul_comm, mul_assoc]
    apply div_le_iff₀' (by positivity) |>.mp
    apply le_trans ?_ (by linarith [hσ.1] : 4 ≤ σ * 8)
    convert! bnd using 1; exact div_rpow_neg_eq_rpow_div (by positivity) (by positivity)

lemma ZetaUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * (5 + 8 * 2); -- the 2 comes from ZetaBnd_aux1
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖
    + ‖(N : ℂ) ^ (-s) / 2‖
    + ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
    ≤ C * Real.log |t| := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, σPos, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      ‖s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ = Real.exp A * 2 * Real.log |t| + N ^ (1 - σ) / ‖(1 - s)‖ + N ^ (-σ) / 2 +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + |t| ^ (1 - σ) * 2 +
        |t| ^ (1 - σ) + 2 * |t| * (8 * |t| ^ (-σ)) := ?_
    _ = Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * |t| ^ (1 - σ) := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * 1 := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * Real.log |t| := ?_
    _ = _ := by ring
  · simp only [add_le_add_iff_right, one_div_cpow_eq_cpow_neg]
    convert UpperBnd_aux3 (C := 2) hA hσ.1 t_gt le_rfl using 1
  · simp only [add_le_add_iff_left]; exact ZetaBnd_aux1 N (by linarith) ⟨σPos, hσ.2⟩ (by linarith)
  · simp only [norm_div, RCLike.norm_ofNat, s]
    congr <;> (convert norm_natCast_cpow_of_pos Npos _; simp)
  · have ⟨h₁, h₂, h₃⟩ := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t
    gcongr
    rw [mul_div_assoc]
    gcongr
  · ring_nf; conv => lhs; rhs; lhs; rw [mul_comm |t|]
    rw [← Real.rpow_add_one (by positivity)]; ring_nf
  · simp only [Real.log_abs, add_le_add_iff_left, mul_one]
    exact mul_le_mul_iff_right₀ (by positivity) |>.mpr <| UpperBnd_aux2 t_gt hσ.1
  · simp only [add_le_add_iff_left]
    apply mul_le_mul_iff_right₀ (by norm_num [Real.exp_pos]) |>.mpr <| logt_gt.le

lemma ZetaUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖ζ (σ + t * I)‖ ≤ C * Real.log |t| := by
  let A := (1 / 2 : ℝ)
  let C := Real.exp A * (5 + 8 * 2) -- the 2 comes from ZetaBnd_aux1
  refine ⟨A, ⟨by norm_num, by norm_num⟩, C, (by positivity), ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ := UpperBnd_aux ⟨by norm_num, by norm_num⟩ t_gt σ_ge
  rw [← Zeta0EqZeta Npos (by simp [σPos]) neOne]
  apply le_trans (by apply norm_add₄_le) ?_
  convert! ZetaUpperBnd' ⟨by norm_num, le_rfl⟩ t_gt ⟨σ_ge, σ_le⟩ using 1; simp

lemma norm_complex_log_ofNat (n : ℕ) : ‖(n : ℂ).log‖ = (n : ℝ).log := by
  have := Complex.ofReal_log (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [(by simp : ((n : ℝ) : ℂ) = (n : ℂ))] at this
  rw [← this, Complex.norm_of_nonneg]
  exact Real.log_natCast_nonneg n

lemma Finset.Icc0_eq (N : ℕ) : Finset.Icc 0 N = {0} ∪ Finset.Icc 1 N := by
  refine Finset.ext_iff.mpr ?_
  intro a
  cases a
  · simp only [Finset.mem_Icc, le_refl, zero_le, and_self, Finset.mem_union, Finset.mem_singleton,
    nonpos_iff_eq_zero, one_ne_zero, and_true, or_false]
  · simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, true_and, Finset.mem_union,
    Finset.mem_singleton, add_eq_zero, one_ne_zero, and_false, false_or]

lemma harmonic_eq_sum_Icc0_aux (N : ℕ) :
    ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
  rw [Finset.Icc0_eq, Finset.sum_union]
  · simp only [Finset.sum_singleton, CharP.cast_eq_zero, inv_zero, zero_add]
  · simp only [Finset.disjoint_singleton_left, Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero,
    zero_le, and_true, not_false_eq_true]

lemma harmonic_eq_sum_Icc0 (N : ℕ) : ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc0_aux, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma DerivUpperBnd_aux1 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2 := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have logN_pos : 0 ≤ Real.log N := Real.log_nonneg (by norm_cast)
  have fact0 {n : ℕ} (hn : n ≤ N) : n ≤ |t| := by linarith [(by exact_mod_cast hn : (n : ℝ) ≤ N)]
  have fact1 {n : ℕ} (hn : n ≤ N) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * A.exp := ZetaBnd_aux2 hA.1 σPos (fact0 hn) σ_ge
  have fact2 {n : ℕ} (hn : n ≤ N) : Real.log n ≤ Real.log |t| := by
    cases n
    · simp only [CharP.cast_eq_zero, Real.log_zero] <;> linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.add_one_pos _) (fact0 hn)
  have fact3 (n : ℕ) (hn : n ≤ N) :
    ‖-1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖ ≤ (n : ℝ)⁻¹ * Real.exp A * (Real.log |t|) := by
    convert! mul_le_mul (fact1 hn) (fact2 hn) (Real.log_natCast_nonneg n) (by positivity)
    simp only [norm_mul, norm_div, norm_neg, norm_one, one_div, natCast_log, ← norm_inv, cpow_neg]
    congr; exact norm_complex_log_ofNat n
  have := norm_sum_le_of_le (Finset.range (N + 1))
    (by simp only [Finset.mem_range, Nat.lt_succ_iff]; exact fact3)
  rw [← Finset.sum_mul, ← Finset.sum_mul, mul_comm _ A.exp, mul_assoc] at this
  rw [mul_assoc]
  apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
  rw [pow_two, ← mul_assoc, Finset.range_eq_Ico, ← Finset.Icc_eq_Ico, harmonic_eq_sum_Icc0]
  apply le_trans (mul_le_mul (h₁ := harmonic_le_one_add_log (n := N)) (le_refl (Real.log |t|))
    (by linarith) (by linarith))
  apply (mul_le_mul_iff_left₀ (by linarith)).mpr
  rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
      ← one_mul <| Real.log (N: ℝ)]
  refine add_le_add logt_gt.le <| mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
  exact Real.log_le_log (by positivity) N_le_t

lemma DerivUpperBnd_aux2 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 →
    1 / 2 < σ → ‖-↑N ^ (1 - s) / (1 - s) ^ 2‖ ≤ A.exp * 2 * (1 / 3) := by
  intro N s Npos N_le_t neOne σ_gt
  dsimp only [s]
  simp_rw [norm_div, norm_neg, norm_pow, norm_natCast_cpow_of_pos Npos _,
    sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero]
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
  rw [(by ring_nf : N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ ^ 2 =
          N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ * 1 / ‖1 - (↑σ + ↑t * I)‖)]
  apply mul_le_mul ?_ ?_ (inv_nonneg.mpr <| norm_nonneg _) ?_
  · rw [mul_one]; exact le_trans h (by gcongr; exact UpperBnd_aux2 t_gt hσ.1)
  · rw [inv_eq_one_div, div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm,
        mul_comm, ← mul_div_assoc, mul_one, le_div_iff₀ (by norm_num), one_mul]
    apply le_trans t_gt.le ?_
    rw [← abs_neg]; convert! abs_im_le_norm (1 - (σ + t * I)); simp
  · exact mul_nonneg (Real.exp_nonneg _) (by norm_num)

theorem DerivUpperBnd_aux3 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * ↑N ^ (1 - s) / (1 - s)‖ ≤ A.exp * 2 * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
    convert le_trans h ?_ using 1
    · simp [s, norm_natCast_cpow_of_pos Npos _, N]
    · gcongr; exact UpperBnd_aux2 t_gt hσ.1
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t

theorem DerivUpperBnd_aux4 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * (N : ℂ) ^ (-s) / 2‖ ≤ A.exp * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm, RCLike.norm_ofNat]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.1
    convert le_trans h (UpperBnd_aux2 t_gt hσ.1) using 1
    all_goals try with_reducible_and_instances rfl
    simp [s, norm_natCast_cpow_of_pos Npos _, N]
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t

theorem DerivUpperBnd_aux5 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → 1 / 2 < σ →
    ‖1 * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1)‖ ≤
    1 / 3 * (2 * |t| * ↑N ^ (-σ) / σ) := by
  intro N s Npos σ_gt
  have neZero : s ≠ 0 := by
    contrapose! σ_gt
    simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, zero_re, add_im, mul_im, zero_add, zero_im, s] at σ_gt
    linarith
  have : 1 = 1 / s * s := by field_simp
  nth_rewrite 1 [this]
  rw [mul_assoc, norm_mul]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · simp only [s, norm_div, norm_one]
    apply one_div_le_one_div (norm_pos_iff.mpr neZero) (by norm_num) |>.mpr
    apply le_trans t_gt.le ?_
    convert! abs_im_le_norm (σ + t * I); simp
  · have hσ : σ ∈ Ioc 0 2 := ⟨(by linarith), hσ.2⟩
    simp only [s]
    have := ZetaBnd_aux1 N (by omega) hσ (by linarith)
    simp only [div_cpow_eq_cpow_neg] at this
    convert! this using 1; congr; funext x; ring_nf

theorem DerivUpperBnd_aux6 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    0 < N → ↑N ≤ |t| → ↑σ + ↑t * I ≠ 1 → 1 / 2 < σ →
    2 * |t| * ↑N ^ (-σ) / σ ≤ 2 * (8 * A.exp) := by
  intro N Npos N_le_t neOne σ_gt
  rw [mul_div_assoc, mul_assoc]
  apply mul_le_mul_iff_right₀ (by norm_num) |>.mpr
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.2
  apply le_trans (mul_le_mul_iff_right₀ (a := |t|) (by positivity) |>.mpr h) ?_
  rw [← mul_assoc, mul_comm _ 8, mul_assoc]
  gcongr
  convert! UpperBnd_aux2 t_gt hσ.1 using 1
  all_goals try with_reducible_and_instances rfl
  rw [mul_comm, ← Real.rpow_add_one (by positivity)]; ring_nf

lemma DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
  have xpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have : ‖(x.log : ℂ)‖ = x.log := Complex.norm_of_nonneg <| Real.log_nonneg hx
  simp [← norm_real, this, Complex.norm_cpow_eq_rpow_re_of_pos xpos, ← Real.norm_eq_abs, ← ofReal_ofNat,
    ← ofReal_inv, ← ofReal_add, ← ofReal_sub, ← ofReal_intCast, one_div]

lemma DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by
  rw [← one_mul (x ^ (-σ - 1) * Real.log x), mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by bound)
  exact le_trans (ZetaSum_aux1_3 x) (by norm_num)

lemma DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl xpos.ne.symm)
  have h2 := h1.const_mul (1 / σ^2)
  have cancel : 1 / σ^2 * σ = 1 / σ := by field_simp
  rw [neg_mul, mul_neg, ← mul_assoc, cancel] at h2
  have h3 := Real.hasDerivAt_log xpos.ne.symm
  have h4 := HasDerivAt.mul (h1.const_mul (1 / σ)) h3
  have cancel := Real.rpow_add xpos (-σ) (-1)
  have : -σ + -1 = -σ - 1 := by rfl
  rw [← Real.rpow_neg_one x, mul_assoc (1 / σ) (x ^ (-σ)), ← cancel, this] at h4
  convert! h2.add h4 |>.neg using 1
  all_goals try with_reducible_and_instances rfl
  field_simp <;> ring

lemma DerivUpperBnd_aux7_3' {a σ : ℝ} (apos : 0 < a) (σnz : σ ≠ 0) :
    ∀ x ∈ Ici a, HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  intro x hx
  simp at hx
  exact DerivUpperBnd_aux7_3 (by linarith) σnz

lemma DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by
  intro x hx
  simp at hx
  bound

lemma DerivUpperBnd_aux7_tendsto {σ : ℝ} (σpos : 0 < σ) :
    Tendsto (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_neg_atTop σpos
  have h2 := h1.const_mul (1 / σ^2)
  have h3 : Tendsto (fun t : ℝ ↦ t ^ (-σ) * Real.log t) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_pow_atTop σ 1 σpos
    simp only [Real.rpow_one] at this
    apply Tendsto.congr' _ this
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [mul_comm]
    apply div_rpow_eq_rpow_neg _ _ _ hx
  have h4 := h3.const_mul (1 / σ)
  have h5 := (h2.add h4).neg
  convert h5 using 1
  · ext; ring
  simp


open MeasureTheory in
lemma DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (l := 0)
  · exact DerivUpperBnd_aux7_3' (by linarith) (by linarith)
  · exact DerivUpperBnd_aux7_nonneg ha
  · exact DerivUpperBnd_aux7_tendsto σpos

open MeasureTheory in
lemma DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x)
      (Ioi a) volume := by
  simp_rw [mul_assoc]
  apply Integrable.bdd_mul (c := 1 / 2) <| DerivUpperBnd_aux7_4 σpos ha
  · exact Measurable.aestronglyMeasurable <| Measurable.abs measurable_floor_add_half_sub
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs, _root_.abs_abs]
  exact  ZetaSum_aux1_3 x

open MeasureTheory in
lemma DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x =
      1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a := by
  convert integral_Ioi_of_hasDerivAt_of_nonneg'
    (DerivUpperBnd_aux7_3' (by linarith) (by linarith))
    (DerivUpperBnd_aux7_nonneg ha) (DerivUpperBnd_aux7_tendsto σpos) using 1
  all_goals try with_reducible_and_instances rfl
  ring

open MeasureTheory in
theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  have σpos : 0 < σ := lt_trans (by norm_num) σ_gt
  rw [norm_mul, (by ring : 6 * |t| * ↑N ^ (-σ) / σ * Real.log |t| = (2 * |t|) * (3 * ↑N ^ (-σ) / σ * Real.log |t|))]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply le_trans (by apply norm_add_le)
    simp [abs_of_pos σpos]
    linarith [hσ.2]
  apply le_trans (by apply norm_integral_le_integral_norm)
  calc ∫ (x : ℝ) in Ioi (N : ℝ), ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖
    _ = ∫ (x : ℝ) in Ioi (N : ℝ), |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
      apply setIntegral_congr_fun (by measurability)
      intro x hx
      simp only [mem_Ioi] at hx
      exact DerivUpperBnd_aux7_1 (lt_of_le_of_lt (mod_cast Npos) hx).le
    _ ≤ ∫ (x : ℝ) in Ioi (N : ℝ), x ^ (-σ - 1) * x.log := by
      apply setIntegral_mono_on _ _ (by measurability)
      · intro x hx
        exact DerivUpperBnd_aux7_2 (lt_of_le_of_lt (mod_cast Npos) hx).le
      · apply DerivUpperBnd_aux7_5 σpos (mod_cast Npos)
      apply DerivUpperBnd_aux7_4 σpos (mod_cast Npos)
    _ = 1 / σ^2 * N ^ (-σ) + 1 / σ * N ^ (-σ) * Real.log N :=
      DerivUpperBnd_aux7_integral_eq (mod_cast Npos) σpos
    _ ≤ 3 * ↑N ^ (-σ) / σ * |t|.log := by
      have h2 : 1 / σ * ↑N ^ (-σ) * Real.log ↑N ≤ ↑N ^ (-σ) / σ * Real.log |t| := calc
        _ = ↑N ^ (-σ) / σ * Real.log N := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.log_le_log (mod_cast Npos) N_le_t
      have : 2 ≤ 2 * Real.log |t| := by
        nth_rewrite 1  [← mul_one 2]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact logt_gt_one t_gt.le |>.le
      have h1 : 1 / σ^2 * ↑N ^ (-σ) ≤ 2 * ↑N ^ (-σ) / σ * Real.log |t| := calc
        1 / σ^2 * ↑N ^ (-σ) = (↑N ^ (-σ) / σ) * (1 / σ) := by ring
        _ ≤ ↑N ^ (-σ) / σ * (2 * Real.log |t|):= by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply le_trans _ this
          exact (one_div_le σpos (by norm_num)).mpr σ_gt.le
        _ = _ := by ring
      convert! add_le_add h1 h2 using 1
      all_goals try with_reducible_and_instances rfl
      ring


lemma ZetaDerivUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * 59;
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * (Real.log n)‖ +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖
        ≤ C * Real.log |t| ^ 2 := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, _, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux1 hA hσ.1 t_gt (by simp : (2 : ℝ) ≤ 2)
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux2 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux3 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux4 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * |t| * N ^ (-σ) / σ) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux5 t_gt hσ Npos σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖ := by
        gcongr; exact DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * |t| * N ^ (-σ) / σ) * (Real.log |t|) := by
        gcongr; exact DerivUpperBnd_aux7 t_gt hσ Npos N_le_t neOne σ_gt
    _ ≤ Real.exp A * 2 * (Real.log |t|) ^ 2 +
      Real.exp A * 2 * (1 / 3) +
      Real.exp A * 2 * (Real.log |t|) +
      Real.exp A * (Real.log |t|) +
      1 / 3 * (2 * (8 * Real.exp A)) +
      (6 * (8 * Real.exp A)) * (Real.log |t|) := by
        gcongr; convert mul_le_mul_of_nonneg_left (DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt) (by norm_num : (0 : ℝ) ≤ 3) using 1 <;> first | (with_reducible_and_instances rfl) | ring
    _ ≤ _ := by
      simp only [C]
      ring_nf
      rw [(by ring : A.exp * |t|.log ^ 2 * 59 = A.exp * |t|.log ^ 2 * 6 + A.exp * |t|.log ^ 2 * 51 +
        A.exp * |t|.log ^ 2 * 2)]
      nth_rewrite 1 [← mul_one A.exp]
      gcongr
      swap
      · nth_rewrite 1 [← mul_one |t|.log, (by ring : |t|.log ^ 2 = |t|.log * |t|.log)]
        gcongr
      nlinarith

lemma ZetaDerivUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2),
    ‖ζ' (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
  obtain ⟨A, hA, _, _, _⟩ := ZetaUpperBnd
  let C := Real.exp A * 59
  refine ⟨A, hA, C, by positivity, ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, N_le_t, _, _, σPos, neOne⟩ := UpperBnd_aux hA t_gt σ_ge
  rw [← DerivZeta0EqDerivZeta Npos (by simp [σPos]) neOne]
  set N : ℕ := ⌊|t|⌋₊
  rw [(HasDerivAtZeta0 Npos (s := σ + t * I) (by simp [σPos]) neOne).deriv]
  dsimp only [ζ₀']
  rw [← add_assoc]
  set aa := ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)
  set bb := -(N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I)) ^ 2
  set cc := (Real.log N) * (N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I))
  set dd := (Real.log N) * (N : ℂ) ^ (-(σ + t * I)) / 2
  set ee := 1 * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1)
  set ff := (σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1) * -(Real.log x)
  rw [(by ring : aa + (bb + cc) + dd + ee + ff = aa + bb + cc + dd + ee + ff)]
  apply le_trans (by apply norm_add₆_le) ?_
  convert ZetaDerivUpperBnd' hA t_gt ⟨σ_ge, σ_le⟩

lemma Tendsto_nhdsWithin_punctured_map_add {f : ℝ → ℝ} (a x : ℝ)
    (f_mono : StrictMono f) (f_iso : Isometry f) :
    Tendsto (fun y ↦ f y + a) (𝓝[>] x) (𝓝[>] (f x + a)) := by
  refine tendsto_iff_forall_eventually_mem.mpr ?_
  intro v hv
  simp only [mem_nhdsWithin] at hv
  obtain ⟨u, hu, hu2, hu3⟩ := hv
  let t := {x | f x + a ∈ u}
  have : t ∩ Ioi x ∈ 𝓝[>] x := by
    simp only [mem_nhdsWithin]
    use t
    simp only [subset_inter_iff, inter_subset_left, inter_subset_right, and_self,
      and_true, t, mem_ofPred_eq]
    refine ⟨?_, by simp [hu2]⟩
    simp only [Metric.isOpen_iff, gt_iff_lt, mem_ofPred_eq] at hu ⊢
    intro x hx
    obtain ⟨ε, εpos, hε⟩ := hu (f x + a) hx
    simp only [Metric.ball, ofPred_subset_ofPred] at hε ⊢
    exact ⟨ε, εpos, fun _ hy ↦ hε (by simp [isometry_iff_dist_eq.mp f_iso, hy])⟩
  filter_upwards [this]
  intro b hb
  simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, t] at hb
  refine hu3 ?_
  simp only [mem_inter_iff, mem_Ioi, add_lt_add_iff_right]
  exact ⟨hb.1, f_mono hb.2⟩

lemma Tendsto_nhdsWithin_punctured_add (a x : ℝ) :
    Tendsto (fun y ↦ y + a) (𝓝[>] x) (𝓝[>] (x + a)) :=
  Tendsto_nhdsWithin_punctured_map_add a x strictMono_id isometry_id

lemma riemannZeta_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ ζ (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x) := by
  have : (fun w : ℂ ↦ ζ (1 + w)) =O[𝓝[≠] 0] (1 / ·) := by
    have H : Tendsto (fun w ↦ w * ζ (1 + w)) (𝓝[≠] 0) (𝓝 1) := by
      convert Tendsto.comp (f := fun w ↦ 1 + w) riemannZeta_residue_one ?_ using 1
      · ext w
        simp only [Function.comp_apply, add_sub_cancel_left]
      · refine tendsto_iff_comap.mpr <| map_le_iff_le_comap.mp <| Eq.le ?_
        convert Homeomorph.map_punctured_nhds_eq (Homeomorph.addLeft (1 : ℂ)) 0 using 2 <;> first | (with_reducible_and_instances rfl) | (simp)
    exact ((Asymptotics.isBigO_mul_iff_isBigO_div eventually_mem_nhdsWithin).mp <|
      Tendsto.isBigO_one ℂ H).trans <| Asymptotics.isBigO_refl ..
  exact (isBigO_comp_ofReal_nhds_ne this).mono <| nhdsGT_le_nhdsNE 0


lemma ZetaNear1BndFilter :
    (fun σ : ℝ ↦ ζ σ) =O[𝓝[>](1 : ℝ)] (fun σ ↦ (1 : ℂ) / (σ - 1)) := by
  have := Tendsto_nhdsWithin_punctured_add (a := -1) (x := 1)
  simp only [add_neg_cancel, ← sub_eq_add_neg] at this
  have := riemannZeta_isBigO_near_one_horizontal.comp_tendsto this
  convert this using 1 <;> first | (with_reducible_and_instances rfl) | ({ext; simp})

lemma ZetaNear1BndExact :
    ∃ (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (_ : σ ∈ Ioc 1 2), ‖ζ σ‖ ≤ c / (σ - 1) := by
  have := ZetaNear1BndFilter
  rw [Asymptotics.isBigO_iff] at this
  obtain ⟨c, U, hU, V, hV, h⟩ := this
  obtain ⟨T, hT, T_open, h1T⟩ := mem_nhds_iff.mp hU
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.mp T_open 1 h1T
  simp only [Metric.ball] at hε
  replace hε : Ico 1 (1 + ε) ⊆ U := by
    refine subset_trans (subset_trans ?_ hε) hT
    intro x hx
    simp only [mem_Ico] at hx
    simp only [dist, abs_lt]
    exact ⟨by linarith, by linarith⟩
  let W := Icc (1 + ε) 2
  have W_compact : IsCompact {ofReal z | z ∈ W} :=
    IsCompact.image isCompact_Icc continuous_ofReal
  have cont : ContinuousOn ζ {ofReal z | z ∈ W} := by
    apply HasDerivAt.continuousOn (f' := ζ')
    intro σ hσ
    exact (differentiableAt_riemannZeta (by contrapose! hσ; simp [W, hσ, εpos])).hasDerivAt
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn W_compact cont
  let C' := max (C + 1) 1
  replace hC : ∀ (σ : ℝ), σ ∈ W → ‖ζ σ‖ < C' := by
    intro σ hσ
    simp only [lt_max_iff, C']
    have := hC σ
    simp only [mem_ofPred_eq, ofReal_inj, exists_eq_right] at this
    exact Or.inl <| lt_of_le_of_lt (this hσ) (by norm_num)
  have Cpos : 0 < C' := by simp [C']
  use max (2 * C') c, (by simp [Cpos])
  intro σ ⟨σ_ge, σ_le⟩
  by_cases hσ : σ ∈ U ∩ V
  · simp only [← h, mem_ofPred_eq] at hσ
    apply le_trans hσ ?_
    norm_cast
    have : 0 ≤ 1 / (σ - 1) := by apply one_div_nonneg.mpr; linarith
    simp only [Real.norm_eq_abs, abs_eq_self.mpr this, mul_div, mul_one]
    exact div_le_div₀ (by simp [Cpos.le]) (by simp) (by linarith) (by rfl)
  · replace hσ : σ ∈ W := by
      simp only [mem_inter_iff, hV σ_ge, and_true] at hσ
      simp only [mem_Icc, σ_le, and_true, W]
      contrapose! hσ; exact hε ⟨σ_ge.le, hσ⟩
    apply le_trans (hC σ hσ).le ((le_div_iff₀ (by linarith)).mpr ?_)
    rw [le_max_iff, mul_comm 2]; exact Or.inl <| mul_le_mul_of_nonneg_left (by linarith) Cpos.le

/-- For positive `x` and nonzero `y` we have that
$|\zeta(x)^3 \cdot \zeta(x+iy)^4 \cdot \zeta(x+2iy)| \ge 1$. -/
lemma norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖ζ (1 + x) ^ 3 * ζ (1 + x + I * y) ^ 4 * ζ (1 + x + 2 * I * y)‖ ≥ 1 := by
  have h₀ : 1 < ( 1 + x : ℂ).re := by simp[hx]
  have h₁ : 1 < (1 + x + I * y).re := by simp [hx]
  have h₂ : 1 < (1 + x + 2 * I * y).re := by simp [hx]
  simpa only [one_pow, norm_mul, norm_pow, DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta, h₀, h₁, h₂] using
    DirichletCharacter.norm_LSeries_product_ge_one (1 : DirichletCharacter ℂ 1) hx y


theorem ZetaLowerBound1_aux1 {σ t : ℝ} (this : 1 ≤ ‖ζ σ‖ ^ (3 : ℝ) * ‖ζ (σ + I * t)‖ ^ (4 : ℝ) * ‖ζ (σ + 2 * I * t)‖) :
  ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1 := by
  use (one_le_pow_iff_of_nonneg (by bound) four_ne_zero).1 (by_contra (this.not_gt ∘ ?_))
  simp_rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num [mul_right_comm, mul_comm (t : ℂ), mul_pow]

lemma ZetaLowerBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1 := by
  -- Start with the fundamental identity
  have := norm_zeta_product_ge_one (x := σ - 1) (by linarith) t
  simp_rw [ge_iff_le, norm_mul, norm_pow, ofReal_sub, ofReal_one, add_sub_cancel, ← Real.rpow_natCast]
    at this
  apply ZetaLowerBound1_aux1 this

lemma ZetaLowerBound2 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / (‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4)) ≤ ‖ζ (σ + t * I)‖ := by
  have := ZetaLowerBound1 (t := t) σ_gt
  exact (div_le_iff₀' (pos_of_mul_pos_left (one_pos.trans_le this) (norm_nonneg _) ) ).mpr this

theorem ZetaLowerBound3_aux1 (A : ℝ) (ha : A ∈ Ioc 0 (1 / 2)) (t : ℝ)
  (ht_2 : 3 < |2 * t|) : 0 < A / Real.log |2 * t| := by
  exact div_pos ha.1 <| Real.log_pos (by linarith)

theorem ZetaLowerBound3_aux2 {C : ℝ}
  {σ t : ℝ}
  (ζ_2t_bound : ‖ζ (σ + (2 * t) * I)‖ ≤ C * Real.log |2 * t|) :
  ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤ (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
  bound

theorem ZetaLowerBound3_aux3 (C : ℝ) (c_near : ℝ) {σ : ℝ} (t : ℝ) (σ_gt : 1 < σ) :
  c_near ^ ((3 : ℝ) / 4) * ((-1 + σ) ^ ((3 : ℝ) / 4))⁻¹ * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) =
    c_near ^ ((3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) * (-1 + σ) ^ (-(3 : ℝ) / 4) := by
  exact (symm) (.trans (by rw [neg_div, Real.rpow_neg (by linarith)]) (by ring))

theorem ZetaLowerBound3_aux4 (C : ℝ) (hC : 0 < C)
  (c_near : ℝ) (hc_near : 0 < c_near) {σ : ℝ} (t : ℝ) (ht : 3 < |t|)
  (σ_gt : 1 < σ)
   :
  0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |2 * t| ^ ((1 : ℝ) / 4) := by
  match sub_pos.mpr σ_gt with | S => match Real.log_pos (by simp; linarith : abs (2 *t) > 1) with | S => positivity

theorem ZetaLowerBound3_aux5
  {σ : ℝ} (t : ℝ)
  (this : ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1) :
  0 < ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) :=
  pos_of_mul_pos_left (this.trans_lt' zero_lt_one) (norm_nonneg _)

lemma ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖ζ (σ + t * I)‖ := by
  obtain ⟨A, ha, C, hC, h_upper⟩ := ZetaUpperBnd
  obtain ⟨c_near, hc_near, h_near⟩ := ZetaNear1BndExact

  use 1 / (c_near ^ ((3 : ℝ) / 4) * (2 * C) ^ ((1 : ℝ) / 4)), by positivity
  intro σ hσ t ht
  obtain ⟨σ_gt, σ_le⟩ := hσ

  -- Use ZetaLowerBound2
  have lower := ZetaLowerBound2 (t := t) σ_gt
  apply le_trans _ lower

  -- Now we need to bound the denominator from above
  -- This will give us a lower bound on the whole expression

  -- Upper bound on ‖ζ σ‖ from ZetaNear1BndExact
  have ζ_σ_bound : ‖ζ σ‖ ≤ c_near / (σ - 1) := by
    exact h_near σ ⟨σ_gt, σ_le⟩

  have ht_2 : 3 < |2 * t| := by simp only [abs_mul, Nat.abs_ofNat]; linarith

  -- Upper bound on ‖ζ (σ + 2*t * I)‖ from ZetaUpperBnd

  have σ_in_range : σ ∈ Icc (1 - A / Real.log |2 * t|) 2 := by
    constructor
    · -- σ ≥ 1 - A / Real.log |2*t|
      have : 0 < A / Real.log |2 * t| := by
        exact ZetaLowerBound3_aux1 A ha t ht_2
      nlinarith
    · exact σ_le

  have ζ_2t_bound := h_upper σ (2 * t) ht_2 σ_in_range

  -- Combine the bounds
  have denom_bound : ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤
      (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply mul_le_mul
    · apply Real.rpow_le_rpow (norm_nonneg _) ζ_σ_bound (by norm_num)
    · apply ZetaLowerBound3_aux2
      convert ζ_2t_bound
      norm_cast
    · apply Real.rpow_nonneg (norm_nonneg _)
    · apply Real.rpow_nonneg (div_nonneg (by linarith) (by linarith))

  -- Simplify the bound
  have : (c_near / (σ - 1)) ^ ((3 : ℝ) / 4) * (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) =
         c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    rw [Real.div_rpow (by linarith) (by linarith), Real.mul_rpow (by linarith) (Real.log_nonneg (by linarith))]
    ring_nf
    exact ZetaLowerBound3_aux3 _ _ _ σ_gt
  rw [this] at denom_bound

  -- Take reciprocal (flipping inequality)
  have pos_left : 0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * (Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
    apply ZetaLowerBound3_aux4 C hC c_near hc_near t ht σ_gt

  have pos_right : 0 < ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
    -- This follows from ZetaLowerBound1 - if either factor were zero, we'd get 0 ≥ 1
    apply ZetaLowerBound3_aux5 _ <| ZetaLowerBound1 (t := t) σ_gt


  use (div_le_div_of_nonneg_left zero_le_one pos_right denom_bound).trans' ?_
  simp_rw [abs_mul, abs_two, neg_div, Real.rpow_neg (sub_pos.2 σ_gt).le] at *
  have hlog : 0 < Real.log |t| := Real.log_pos <| ht.trans' <| by norm_num
  have : 0 < Real.log |t| ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hlog2 : 0 < Real.log (2 * |t|) := Real.log_pos <| ht_2.trans' <| by norm_num
  have : 0 < Real.log (2 * |t|) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hlog2 (1 / 4)
  field_simp
  rw [Real.mul_rpow two_pos.le hC.le]
  move_mul [C ^ (1 / 4)]
  rw [mul_le_mul_iff_left₀]
  swap
  · positivity
  rw [← Real.mul_rpow two_pos.le hlog.le]
  apply Real.rpow_le_rpow hlog2.le ?_ (by norm_num)
  rw [← Real.log_rpow (ht.trans' (by norm_num))]
  apply Real.log_le_log (ht_2.trans' (by norm_num))
  rw [Real.rpow_two, sq]
  gcongr
  exact ht.trans' (by norm_num) |>.le

set_option backward.isDefEq.respectTransparency false in
lemma deriv_fun_re {t : ℝ} {f : ℂ → ℂ} (diff : ∀ (σ : ℝ), DifferentiableAt ℂ f (↑σ + ↑t * I)) :
    (deriv fun {σ₂ : ℝ} ↦ f (σ₂ + t * I)) = fun (σ : ℝ) ↦ deriv f (σ + t * I) := by
  ext σ
  have := deriv_comp (h := fun (σ : ℝ) ↦ σ + t * I) (h₂ := f) σ (diff σ) ?_
  · simp only [deriv_add_const', _root_.deriv_ofReal, mul_one] at this
    exact this
  · apply DifferentiableAt.add_const _ <| differentiableAt_ofReal σ

set_option backward.isDefEq.respectTransparency false in
lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, ζ' (σ + t * I)) = ζ (σ₂ + t * I) - ζ (σ₁ + t * I) := by
  have diff : ∀ (σ : ℝ), DifferentiableAt ℂ ζ (σ + t * I) := by
    intro σ
    refine differentiableAt_riemannZeta ?_
    contrapose! t_ne_zero; apply And.right; simpa [Complex.ext_iff] using t_ne_zero
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact deriv_fun_re diff
  · intro s _
    apply DifferentiableAt.comp
    · exact (diff s).restrictScalars ℝ
    · exact DifferentiableAt.add_const (c := t * I) <| differentiableAt_ofReal _
  · apply ContinuousOn.comp (g := ζ') ?_ ?_ (mapsTo_image _ _)
    · apply HasDerivAt.continuousOn (f' := deriv <| ζ')
      intro x hx
      apply hasDerivAt_deriv_iff.mpr
      replace hx : x ≠ 1 := by
        contrapose! hx
        simp only [hx, mem_image, Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im, not_exists,
          not_and]
        exact fun _ _ _ ↦ t_ne_zero
      exact differentiableAt_deriv_riemannZeta hx
    · exact continuous_ofReal.continuousOn.add continuousOn_const

lemma Zeta_diff_Bnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ₁ σ₂ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : 1 - A / Real.log |t| ≤ σ₁) (_ : σ₂ ≤ 2) (_ : σ₁ < σ₂),
    ‖ζ (σ₂ + t * I) - ζ (σ₁ + t * I)‖ ≤  C * Real.log |t| ^ 2 * (σ₂ - σ₁) := by
  obtain ⟨A, hA, C, Cpos, hC⟩ := ZetaDerivUpperBnd
  refine ⟨A, hA, C, Cpos, ?_⟩
  intro σ₁ σ₂ t t_gt σ₁_ge σ₂_le σ₁_lt_σ₂
  have t_ne_zero : t ≠ 0 := by contrapose! t_gt; simp only [t_gt, abs_zero, Nat.ofNat_nonneg]
  rw [← Zeta_eq_int_derivZeta t_ne_zero]
  convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
  · congr; rw [_root_.abs_of_nonneg (by linarith)]
  · intro σ hσ; rw [uIoc_of_le σ₁_lt_σ₂.le, mem_Ioc] at hσ
    exact hC σ t t_gt ⟨le_trans σ₁_ge hσ.1.le, le_trans hσ.2 σ₂_le⟩

lemma ZetaLowerBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ (9 : ℝ)) 1),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖ζ (σ + t * I)‖ := by
  obtain ⟨C₁, C₁pos, hC₁⟩ := ZetaLowerBound3
  obtain ⟨A', hA', C₂, C₂pos, hC₂⟩ := Zeta_diff_Bnd

  -- Pick the right constants.
  -- Don't really like this because I can only do that after first finishing the proof.
  -- Is there a way to delay picking those
  let A := min A' ((C₁ / (4 * C₂)) ^ 4)
  have hA : A ∈ Ioc 0 (1 / 2) :=
    ⟨lt_min hA'.1 (by positivity), (min_le_left A' _).trans hA'.2⟩

  let C := C₁ * A ^ ((3:ℝ) /4) - 2 * C₂ * A
  have hc_pos : 0 < C := by
    have:= A.rpow_le_rpow hA.1.le (min_le_right _ _) (inv_pos.mpr four_pos).le
    erw [Real.pow_rpow_inv_natCast (div_pos C₁pos (mul_pos four_pos C₂pos)).le four_ne_zero,
      le_div_iff₀ (mul_pos four_pos C₂pos)] at this
    norm_num [mul_assoc, C, mul_left_comm, C₂pos, hA.1,
      (mul_le_mul_of_nonneg_right this (A.rpow_nonneg hA.1.le _)).trans_lt', ←A.rpow_add]

  refine ⟨A, hA, C, hc_pos, fun σ t L ⟨σ_low_bound, σ_le_one⟩=>?_⟩

  -- From here I followed the proof found in the blueprint
  let σ' := 1 + A / Real.log |t| ^  (9 : ℝ)

  have triangular :  ‖ζ (σ + t * I)‖ ≥  ‖ζ (σ' + t * I)‖ -  ‖ζ (σ + t * I) - ζ (σ' + t * I)‖ := by
    apply sub_le_iff_le_add.mpr.comp (sub_sub_self @_ (@_ : ℂ)▸norm_sub_le _ _).trans
      (by rw [add_comm])

  have one_leLogT : 1 ≤ Real.log |t| := (logt_gt_one L.le).le
  have one_half_le_log_pow : 1 / 2 ≤ Real.log |t| ^ 9 :=
    one_half_lt_one.le.trans <| one_le_pow₀ one_leLogT

  have σ'_ge : 1 ≤ σ' := by
    simp_all only [gt_iff_lt, mem_Ioc, Real.log_abs, one_div, and_imp, tsub_le_iff_right,
      lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos,
      and_self, inf_le_iff, true_or, sub_pos, mem_Ico, and_true, ofReal_add, ofReal_one,
      ofReal_div, ge_iff_le, le_add_iff_nonneg_right, A, C, σ']
    apply div_nonneg
    · apply le_min
      · linarith
      · have : (C₁ / (4 * C₂)) ^ 4 = ((C₁ / (4 * C₂)) ^ 2) ^ 2 := by ring
        rw [this]
        apply sq_nonneg
    · positivity

  have right_sub :  -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖ ≥ - C₂ * Real.log |t| ^ 2 * (σ' - σ) := by
    change - C₂ * Real.log |t| ^ 2 * (σ' - σ) ≤ -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖
    have := hC₂ σ σ' t L ?_ ?_ ?_
    · convert! neg_le_neg this using 1
      · ring
      · congr! 1
        have : ζ (↑σ + ↑t * I) - ζ (↑σ' + ↑t * I) =
            - (ζ (↑σ' + ↑t * I) - ζ (↑σ + ↑t * I)) := by ring
        rw [this, norm_neg]
    · have : 1 - A' / Real.log |t| ≤ (1 : ℝ) - A / (Real.log |t|) ^ (9 : ℝ) := by
        gcongr
        · exact hA'.1.le
        · bound
        · rw [← Real.rpow_one (Real.log |t|), ← Real.rpow_mul (by linarith), one_mul]
          exact Real.rpow_le_rpow_of_exponent_le one_leLogT Nat.one_le_ofNat
      linarith
    · have : σ' ≤ 1 + A := by
        simp_all only [gt_iff_lt, mem_Ioc, Real.log_abs, one_div, and_imp, tsub_le_iff_right,
          lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos, mul_pos_iff_of_pos_left, pow_pos,
          and_self, inf_le_iff, true_or, sub_pos, mem_Ico, and_true, ofReal_add, ofReal_one,
          ofReal_div, ge_iff_le, le_add_iff_nonneg_right, add_le_add_iff_left, le_inf_iff,
          σ', A, C]
        have : 1 ≤ Real.log t ^ (9 : ℝ) := Real.one_le_rpow one_leLogT (Nat.ofNat_nonneg' 9)
        refine ⟨?_, ?_⟩
        · rw [← min_div_div_right]
          · rw [min_le_iff]
            left
            bound
          · exact le_trans (zero_le_one) this
        · rw [← min_div_div_right]
          · rw [min_le_iff]
            right
            bound
          · exact le_trans (zero_le_one) this
      · bound [hA.2]
    · linarith

  have right' : -‖ζ (σ + t * I) -  ζ (σ' + t * I)‖   ≥ - C₂ * 2 * A / Real.log |t| ^ 7 := by
    have := (abs t).log_pos (by bound)
    refine right_sub.trans' ((div_le_iff₀ (pow_pos this 7)).2 @?_|>.trans
      (mul_le_mul_of_nonpos_left (sub_le_sub_left σ_low_bound (1+_) )
        (by ·linear_combination C₂*this*(.log |t|))))
    exact (mod_cast (by linear_combination (2 *_* A) *div_self ↑(pow_pos this 09).ne'))

  have left_sub : ‖ζ (σ' + t * I)‖ ≥ C₁ * (σ' - 1) ^ ((3:ℝ) /4) / Real.log |t| ^ 4 := by
    use (hC₁ ⟨lt_add_of_pos_right (1) (by bound[hA.1]),
      add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans (?_)))⟩ t L).trans' ?_
    · norm_num only [one_mul, Real.rpow_ofNat, one_half_le_log_pow]
    · simp_all only [gt_iff_lt, mem_Ioc, lt_inf_iff, div_pos_iff_of_pos_left, Nat.ofNat_pos,
        mul_pos_iff_of_pos_left, pow_pos, and_self, inf_le_iff, true_or, sub_pos, mem_Ico,
        ofReal_add, ofReal_one, ofReal_div, ge_iff_le, le_add_iff_nonneg_right, neg_mul,
        neg_le_neg_iff, add_sub_cancel_left, σ', A, C]
      gcongr
      have :  Real.log |t| ^ ((1 : ℝ) / 4) ≤ Real.log |t| ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_leLogT (by norm_num)
      exact_mod_cast this

  have left' : ‖ζ (σ' + t * I)‖ ≥ C₁ * A ^ ((3:ℝ) /4) / Real.log |t| ^ 7 := by
    contrapose! hC₁
    use σ', ⟨lt_add_of_pos_right 1<|by bound[hA'.1],
      add_le_of_le_sub_left ((div_le_iff₀ (by bound)).2 (hA.2.trans ?_))⟩, t, L, hC₁.trans_le ?_
    · norm_num only [one_mul, Real.rpow_ofNat, one_half_le_log_pow]
    · norm_num only [σ', add_sub_cancel_left, A.div_rpow hA.1.le, mul_div, pow_pos, L.trans',
        ←Real.rpow_natCast, ←Real.rpow_mul, le_of_lt, Real.log_pos, refl, div_div, ←Real.rpow_sub]
      rw [Real.div_rpow hA.1.le, ← Real.rpow_mul (by linarith), ← mul_div_assoc, div_div, ← Real.rpow_add (by linarith)]
      · norm_num
      · apply Real.rpow_nonneg (by linarith)
  have ineq : ‖ζ (σ + t * I)‖ ≥ (C₁ * A ^ ((3:ℝ) /4) - C₂ * 2 * A) / Real.log |t| ^ 7 := by
    linear_combination left'+triangular+right'

  rw [mul_comm C₂] at ineq
  exact_mod_cast ineq

-- **End collaboration 6/20/25**


lemma ZetaZeroFree9 : ZetaZeroFreeGenProp 9 := by
  obtain ⟨A, hA, c, hc, h_lower⟩ := ZetaLowerBnd

  -- Use the same A for our result
  refine ⟨A, hA, ?_⟩

  -- Now prove that ζ has no zeros in this region
  intro σ t ht hσ h_zero

  have := h_lower σ t ht hσ

  rw [h_zero, norm_zero] at this

  have pos_bound : 0 < c / (Real.log |t|) ^ (7 : ℝ) := by
    apply div_pos hc
    apply Real.rpow_pos_of_pos
    apply Real.log_pos
    linarith
  linarith


lemma ZetaNoZerosOn1Line (t : ℝ) : ζ (1 + t * I) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  simp

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

lemma ZetaCont : ContinuousOn ζ (univ \ {1}) := by
  apply continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  apply DifferentiableAt.continuousAt (𝕜 := ℂ)
  convert differentiableAt_riemannZeta ?_
  simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and] at hx
  exact hx


lemma ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  by_contra! h
  have hn (n : ℕ) := h (1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra! hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    use sub_zero (1: ℝ)▸tendsto_order.2 ⟨fun A B=>? _,fun A B=>?_⟩
    · apply (((tendsto_inv_atTop_nhds_zero_nat.comp
        (Filter.tendsto_add_atTop_nat (1))).congr (by norm_num)).const_sub 1).eventually_const_lt
          B|>.mono (hσ'_ge ·|>.trans_lt')
    · norm_num[(hσ'_le _).trans_lt, B.trans_le']

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by omega, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert hζ (subseq n) using 3
    all_goals try with_reducible_and_instances rfl
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      simp_all only [ge_iff_le, one_div, tsub_le_iff_right, Function.comp_def, ofReal_zero,
        mul_zero, add_zero, norm_eq_sqrt_real_inner, Complex.inner, mul_re, conj_re, conj_im,
        mul_neg, sub_neg_eq_add, Real.one_le_sqrt, eventually_nhdsWithin_iff, mem_compl_iff,
        mem_singleton_iff]
      contrapose! h
      simp_all only [ne_eq]
      delta abs at*
      exfalso
      simp_rw [Metric.nhds_basis_ball.frequently_iff]at*
      choose! I A B using h
      choose a s using exists_seq_strictAnti_tendsto (0: ℝ)
      apply ((isCompact_closedBall _ _).isSeqCompact
        fun and=>(A _ (s.2.1 and)).le.trans (s.2.2.bddAbove_range.some_mem ⟨and, rfl⟩)).elim
      simp only [Metric.mem_ball, dist_eq_norm_sub] at A
      refine fun and ⟨a, H, S, M⟩=> ?_
      refine absurd (tendsto_nhds_unique M (tendsto_sub_nhds_zero_iff.1
        (( squeeze_zero_norm fun and=>le_of_lt (A _ (s.2.1 _) ) )
          (s.2.2.comp S.tendsto_atTop)))) fun and=>?_
      norm_num[*,Function.comp_def] at M
      have:=@riemannZeta_residue_one
      use one_ne_zero (tendsto_nhds_unique (this.comp (tendsto_nhdsWithin_iff.2
        ⟨ M,.of_forall (by norm_num[*])⟩)) ( squeeze_zero_norm ?_
          ((M.sub_const 1).norm.trans (by rw [sub_self,norm_zero]))))
      use fun and =>.trans (norm_mul_le_of_le ↑(le_rfl) (Complex.norm_def _▸Real.sqrt_le_one.mpr
        (B ↑_ (s.2.1 ↑_)).right.le)) (by rw [mul_one])

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have cont := @ZetaCont
      use isClosed_singleton.isSeqClosed
        this
        (.comp
          (cont.continuousAt.comp (eventually_ne_nhds (by field_simp; simp [ht₀])).mono
            fun and=>.intro ⟨⟩)
          (ToOneT0.trans (inf_le_left)))

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero


-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaContourRegion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A quantitative zero-free region for the finite contour

The logarithmic ninth-power zero-free region suffices for fixed-order
contour estimates.
-/
namespace JointDickman
open Set

theorem zeta_contour_zero_free : ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧
    ∀ T : ℝ, 0 ≤ T → 0 < zetaContourWidth A T ∧ zetaContourWidth A T ≤ 1/4 ∧
      ∀ s : ℂ, 1-zetaContourWidth A T ≤ s.re → |s.im| ≤ T → riemannZeta s ≠ 0 := by
  obtain ⟨σ₀,hσ₀,hsmall⟩ := ZetaNoZerosInBox 3
  obtain ⟨A₀,hA₀,hlarge⟩ := ZetaZeroFree9
  let A := min (1/4:ℝ) (min (1-σ₀) A₀)
  have hA : 0 < A := lt_min (by norm_num) (lt_min (by linarith) hA₀.1)
  have hA4 : A ≤ 1/4 := min_le_left _ _
  have hAσ : A ≤ 1-σ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hAA : A ≤ A₀ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨A,hA,hA4,fun T hT => ?_⟩
  have hlog : 0 < Real.log (T+3) := Real.log_pos (by linarith)
  have hd : 0 < (1+Real.log (T+3))^9 := by positivity
  have hd1 : 1 ≤ (1+Real.log (T+3))^9 := one_le_pow₀ (by linarith)
  have hwA : zetaContourWidth A T ≤ A := by
    unfold zetaContourWidth
    exact div_le_self hA.le hd1
  refine ⟨div_pos hA hd,hwA.trans hA4,fun s hs ht => ?_⟩
  have hs0 : σ₀ ≤ s.re := by linarith
  have heq : (s.re:ℂ)+(s.im:ℂ)*Complex.I = s := Complex.re_add_im s
  rcases le_or_gt |s.im| 3 with ht3 | ht3
  · rw [←heq]
    exact hsmall s.im ht3 s.re hs0
  · rcases lt_or_ge s.re 1 with hs1 | hs1
    · have hltlog : 0 < Real.log |s.im| := Real.log_pos (by linarith)
      have hl : Real.log |s.im| ≤ 1+Real.log (T+3) := by
        have hh := Real.log_le_log (by positivity : 0 < |s.im|) (show |s.im| ≤ T+3 by linarith)
        linarith
      have hwidth : zetaContourWidth A T ≤ A₀/(Real.log |s.im|)^9 := by
        unfold zetaContourWidth
        exact div_le_div₀ hA₀.1.le hAA (by positivity) (pow_le_pow_left₀ hltlog.le hl 9)
      rw [←heq]
      apply hlarge s.re s.im ht3
      constructor
      · simpa only [show (9:ℝ) = (9:ℕ) by norm_num,Real.rpow_natCast] using
          (show 1-A₀/(Real.log |s.im|)^9 ≤ s.re by linarith)
      · exact hs1
    · rcases hs1.eq_or_lt with hs1 | hs1
      · rw [←heq,←hs1]
        exact ZetaNoZerosOn1Line s.im
      · exact riemannZeta_ne_zero_of_one_lt_re hs1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaPerronScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete height and width for fixed-order Perron estimates -/
namespace JointDickman

theorem perronScale_log_bound {q : ℝ} (hq : 2 ≤ q) :
    1+Real.log (Real.exp q+3) ≤ 2*q := by
  have he : 3 ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hlog : Real.log (Real.exp q+3) ≤ q+1 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    rw [Real.exp_add]
    nlinarith
  linarith

theorem perronScaleWidth_pos {A q : ℝ} (hA : 0 < A) : 0 < perronScaleWidth A q := by
  have hlog : 0 < Real.log (Real.exp q+3) := Real.log_pos (by linarith [Real.exp_pos q])
  unfold perronScaleWidth zetaContourWidth
  positivity

theorem perronScaleWidth_mul_lower {A q : ℝ} (hA : 0 < A) (hq : 2 ≤ q) :
    A/2048*q ≤ q^10*perronScaleWidth A q := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 < Real.log (Real.exp q+3) := Real.log_pos (by linarith [Real.exp_pos q])
  have hD : 0 < (1+Real.log (Real.exp q+3))^9 := by positivity
  have hDle := pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log (Real.exp q+3))
    (perronScale_log_bound hq) 9
  have hw : A/(4*(2*q)^9) ≤ perronScaleWidth A q := by
    unfold perronScaleWidth zetaContourWidth
    rw [div_div]
    apply div_le_div_of_nonneg_left hA.le (mul_pos hD (by norm_num))
    nlinarith
  calc
    A/2048*q = q^10*(A/(4*(2*q)^9)) := by
      field_simp
      ring
    _ ≤ q^10*perronScaleWidth A q := mul_le_mul_of_nonneg_left hw (pow_nonneg hq0.le _)

theorem perronScale_right_le_width {A q : ℝ} (hA : 0 < A)
    (hq : 2 ≤ q) (hqA : 2048/A ≤ q) :
    1/q^10 ≤ perronScaleWidth A q := by
  have hq0 : 0 < q := by linarith
  apply (div_le_iff₀ (pow_pos hq0 10)).mpr
  have hAq : 2048 ≤ q*A := (div_le_iff₀ hA).mp hqA
  have hlower := perronScaleWidth_mul_lower hA hq
  nlinarith

theorem perronScaleWidth_upper {A q : ℝ} (hA : 0 ≤ A) (hq : 2 ≤ q) :
    perronScaleWidth A q ≤ A/(4*q) := by
  have hq0 : 0 < q := by linarith
  have hlog : q ≤ Real.log (Real.exp q+3) := by
    have h := Real.log_le_log (Real.exp_pos q) (show Real.exp q ≤ Real.exp q+3 by linarith)
    simpa only [Real.log_exp] using h
  have hbase : 1 ≤ 1+Real.log (Real.exp q+3) := by linarith
  have hpow := le_self_pow₀ hbase (by norm_num : (9:ℕ) ≠ 0)
  unfold perronScaleWidth zetaContourWidth
  rw [div_div]
  apply div_le_div_of_nonneg_left hA (mul_pos (by norm_num) hq0)
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_PerronLeftDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial prefactors in the left-side Perron error -/
namespace JointDickman
open Filter Asymptotics
open scoped Topology

theorem fractional_ratio_power_bound {z C δ : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (C/δ)^z ≤ (1+C)/δ := by
  by_cases h : C/δ ≤ 1
  · calc
      _ ≤ 1 := Real.rpow_le_one (div_nonneg hC hδ.le) h hz
      _ ≤ (1+C)/δ := (le_div_iff₀ hδ).mpr (by linarith)
  · calc
      _ ≤ C/δ := Real.rpow_le_self_of_one_le (le_of_not_ge h) hz1
      _ ≤ (1+C)/δ := div_le_div_of_nonneg_right (by linarith) hδ.le

theorem perronScaleWidth_inverse_bound {A q : ℝ} (hA : 0 < A) (hq : 2 ≤ q) :
    1/perronScaleWidth A q ≤ (2048/A)*q^9 := by
  have hq0 : 0 < q := by linarith
  have hlow : A/2048 ≤ q^9*perronScaleWidth A q := by
    apply (mul_le_mul_iff_right₀ hq0).mp
    calc
      q*(A/2048) = (A/2048)*q := by ring
      _ ≤ q^10*perronScaleWidth A q := perronScaleWidth_mul_lower hA hq
      _ = q*(q^9*perronScaleWidth A q) := by ring
  apply (div_le_iff₀ (perronScaleWidth_pos hA)).mpr
  calc
    1 = (2048/A)*(A/2048) := by field_simp
    _ ≤ (2048/A)*(q^9*perronScaleWidth A q) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    _ = _ := by ring

theorem power9_exp_decay {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun q : ℝ => q^9*Real.exp (-a*q)) =o[atTop] (fun q => q^b) := by
  have h := (isBigO_refl (fun q : ℝ => q^(9:ℝ)) atTop).mul_isLittleO
    (isLittleO_exp_neg_mul_rpow_atTop ha (b-9))
  apply h.congr'
  · exact Eventually.of_forall (fun q => by
      change q^(9:ℝ)*Real.exp (-a*q) = q^9*Real.exp (-a*q)
      rw [Real.rpow_ofNat])
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with q hq
    rw [←Real.rpow_add hq]
    congr 1
    ring

theorem perronScale_left_scalar_decay {z C A : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hC : 0 ≤ C) (hA : 0 < A) (b : ℝ) :
    (fun q : ℝ => (C/perronScaleWidth A q)^z *
      Real.exp (-(q^10*perronScaleWidth A q))) =o[atTop] (fun q => q^b) := by
  apply IsBigO.trans_isLittleO (g := fun q : ℝ => q^9*Real.exp (-(A/2048)*q)) _
    (power9_exp_decay (div_pos hA (by norm_num)) b)
  refine isBigO_iff.mpr ⟨(1+C)*(2048/A),?_⟩
  filter_upwards [eventually_ge_atTop (max 2 A)] with q hq
  have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
  have hqA : A ≤ q := (le_max_right _ _).trans hq
  have hq0 : 0 < q := by linarith
  have hη := perronScaleWidth_pos hA (q := q)
  have hη1 : perronScaleWidth A q ≤ 1 := by
    apply (perronScaleWidth_upper hA.le hq2).trans
    apply (div_le_iff₀ (by positivity : 0 < 4*q)).mpr
    linarith
  have hp : (C/perronScaleWidth A q)^z ≤ (1+C)*(2048/A)*q^9 := by
    calc
      _ ≤ (1+C)/perronScaleWidth A q := fractional_ratio_power_bound hz hz1 hC hη hη1
      _ = (1+C)*(1/perronScaleWidth A q) := by ring
      _ ≤ (1+C)*((2048/A)*q^9) :=
        mul_le_mul_of_nonneg_left (perronScaleWidth_inverse_bound hA hq2) (by linarith)
      _ = _ := by ring
  have he : Real.exp (-(q^10*perronScaleWidth A q)) ≤ Real.exp (-(A/2048)*q) := by
    apply Real.exp_le_exp.mpr
    have h := perronScaleWidth_mul_lower hA hq2
    nlinarith
  have hl : 0 ≤ (C/perronScaleWidth A q)^z*Real.exp (-(q^10*perronScaleWidth A q)) :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg hC hη.le) _) (Real.exp_pos _).le
  have hr : 0 ≤ q^9*Real.exp (-(A/2048)*q) := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hl,Real.norm_eq_abs,abs_of_nonneg hr]
  calc
    _ ≤ ((1+C)*(2048/A)*q^9)*Real.exp (-(A/2048)*q) :=
      mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaRectangleLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized logarithms on the finite zero-free rectangles -/
namespace JointDickman
open Set

theorem zetaOpenRectangle_isOpen (δ T : ℝ) : IsOpen (zetaOpenRectangle δ T) :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem zetaOpenRectangle_convex (δ T : ℝ) : Convex ℝ (zetaOpenRectangle δ T) :=
  ((convex_Ioo _ _).linear_preimage Complex.reLm).inter
    ((convex_Ioo _ _).linear_preimage Complex.imLm)

theorem zetaOpenRectangle_one {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) :
    (1:ℂ) ∈ zetaOpenRectangle δ T := by
  change ((1:ℝ) ∈ Ioo (1-δ) 2) ∧ (0:ℝ) ∈ Ioo (-T) T
  constructor <;> constructor <;> linarith

theorem zeta_rectangle_log : ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧ ∀ T : ℝ, 0 < T →
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (zetaOpenRectangle (zetaContourWidth A T) T) ∧
      f 1 = 0 ∧ ∀ s ∈ zetaOpenRectangle (zetaContourWidth A T) T,
        Complex.exp (f s) = zetaPoleFactor s := by
  obtain ⟨A,hA,hA4,hzero⟩ := zeta_contour_zero_free
  refine ⟨A,hA,hA4,fun T hT => ?_⟩
  obtain ⟨hδ,_,hzeta⟩ := hzero T hT.le
  have h1 := zetaOpenRectangle_one hδ hT
  let : ContractibleSpace (zetaOpenRectangle (zetaContourWidth A T) T) :=
    (zetaOpenRectangle_convex _ _).contractibleSpace ⟨1,h1⟩
  have hsimp : IsSimplyConnected (zetaOpenRectangle (zetaContourWidth A T) T) := by
    change SimplyConnectedSpace _
    infer_instance
  apply exists_zetaPoleLog hsimp (zetaOpenRectangle_isOpen _ _) h1
  intro s hs _
  exact hzeta s hs.1.1.le (abs_le.mpr ⟨hs.2.1.le,hs.2.2.le⟩)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_PerronScaleGeometry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible logarithms and geometry at the concrete Perron scale -/
namespace JointDickman
open Set Complex

theorem zeta_rectangle_log_below : ∃ A₀ : ℝ, 0 < A₀ ∧ A₀ ≤ 1/4 ∧
    ∀ A : ℝ, 0 < A → A ≤ A₀ → ∀ T : ℝ, 0 < T →
      ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (zetaOpenRectangle (zetaContourWidth A T) T) ∧
        f 1 = 0 ∧ ∀ s ∈ zetaOpenRectangle (zetaContourWidth A T) T,
          exp (f s) = zetaPoleFactor s := by
  obtain ⟨A₀,hA₀,hA₀4,hlog⟩ := zeta_rectangle_log
  refine ⟨A₀,hA₀,hA₀4,?_⟩
  intro A _ hAA T hT
  obtain ⟨f,hf,hf1,he⟩ := hlog T hT
  have hw : zetaContourWidth A T ≤ zetaContourWidth A₀ T := by
    unfold zetaContourWidth
    exact div_le_div_of_nonneg_right hAA (pow_nonneg (by
      have := Real.log_pos (show 1 < T+3 by linarith)
      linarith) _)
  have hsub : zetaOpenRectangle (zetaContourWidth A T) T ⊆
      zetaOpenRectangle (zetaContourWidth A₀ T) T := by
    intro s hs
    exact ⟨⟨by linarith [hs.1.1],hs.1.2⟩,hs.2⟩
  exact ⟨f,hf.mono hsub,hf1,fun s hs => he s (hsub hs)⟩

theorem perronScale_height_gt_three {q : ℝ} (hq : 8 ≤ q) :
    3 < Real.exp q/2 := by
  linarith [Real.add_one_le_exp q]

theorem perronScaleWidth_le_log_height {A q : ℝ} (hA : 0 < A) (hq : 8 ≤ q) :
    perronScaleWidth A q ≤ A/Real.log (Real.exp q/2) := by
  have hq0 : 0 < q := by linarith
  have hT := perronScale_height_gt_three hq
  have hlog : 0 < Real.log (Real.exp q/2) := Real.log_pos (by linarith)
  have hlogq : Real.log (Real.exp q/2) ≤ q := by
    calc
      _ ≤ Real.log (Real.exp q) := Real.log_le_log (by positivity) (by linarith [Real.exp_pos q])
      _ = q := Real.log_exp q
  apply (le_div_iff₀ hlog).mpr
  calc
    perronScaleWidth A q*Real.log (Real.exp q/2) ≤ perronScaleWidth A q*q :=
      mul_le_mul_of_nonneg_left hlogq (perronScaleWidth_pos hA).le
    _ ≤ (A/(4*q))*q :=
      mul_le_mul_of_nonneg_right (perronScaleWidth_upper hA.le (by linarith)) hq0.le
    _ = A/4 := by field_simp
    _ ≤ A := by linarith

theorem perronScaleWidth_four_le {A q : ℝ} (hA : 0 < A) (hq : 2 ≤ q) :
    4*perronScaleWidth A q ≤ A := by
  have hq0 : 0 < q := by linarith
  calc
    _ ≤ 4*(A/(4*q)) := mul_le_mul_of_nonneg_left (perronScaleWidth_upper hA.le hq) (by norm_num)
    _ = A/q := by ring
    _ ≤ A := div_le_self hA.le (by linarith)

theorem perron_inner_contour_mem {η c T : ℝ} (hη : 0 < η) (hη1 : η ≤ 1/4)
    (hc : c ≤ η) (hT : 0 < T) {w : ℂ}
    (hr : -η ≤ w.re ∧ w.re ≤ c) (hi : |w.im| ≤ T) :
    1+w ∈ zetaOpenRectangle (4*η) (2*T) := by
  have him := abs_le.mp hi
  change (1-4*η < (1+w).re ∧ (1+w).re < 2) ∧
    (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
  simp only [add_re,one_re,add_im,one_im,zero_add]
  constructor <;> constructor <;> linarith [hr.1,hr.2,him.1,him.2]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_PerronTailDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential decay of the truncated Perron tails -/
namespace JointDickman
open Filter Asymptotics
open scoped Topology

theorem perronScale_tail_scalar_decay (b : ℝ) :
    (fun q : ℝ => (Real.exp q/2)^(-1/2:ℝ)) =o[atTop] (fun q => q^b) := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0:ℝ) < 1/2) b).const_mul_left
    (1/(2:ℝ)^(-1/2:ℝ))
  apply h.congr_left
  intro q
  rw [Real.div_rpow (Real.exp_pos q).le (by norm_num),←Real.exp_mul]
  rw [show -(1/2:ℝ)*q = q*(-1/2) by ring]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact removal of the small prime factors

Removing a finite set of prime factors is an exact convolution identity.
The moving roughness cutoff is then controlled by Selberg–Delange estimates.
-/

namespace JointDickman

open ArithmeticFunction Finset

theorem squarefreeWeight_isMultiplicative (z : ℝ) :
    (squarefreeWeight z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨squarefreeWeight_one z, fun {m n} hm hn hmn => ?_⟩
  simp only [squarefreeWeight, coe_mk, Nat.squarefree_mul hmn,
    ite_zero_mul_ite_zero, cardFactors_mul hm hn, pow_add]

theorem squarefreeWeight_prime_pow (z : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    squarefreeWeight z (p ^ k) = if k = 1 then z else 0 := by
  by_cases hk1 : k = 1
  · simp [hk1, squarefreeWeight, hp.squarefree, cardFactors_apply_prime hp]
  · have hsq : ¬Squarefree (p ^ k) := by
      rw [Nat.squarefree_pow_iff hp.ne_one hk]
      simp [hk1]
    simp [squarefreeWeight, hsq, hk1]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of the squarefree Selberg–Delange Euler factor

Cancellation of the linear local logarithms proves absolute convergence.
This identifies the same Euler product used in the published leading
coefficient, without assuming its convergence as another input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem log_one_add_sub_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |-x| < 1 by rw [abs_neg, abs_of_nonneg hx]; linarith) 1
  have hbase : |Real.log (1 + x) - x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_neg, abs_of_nonneg hx, sub_neg_eq_add, sub_eq_add_neg, add_comm] using h
  apply hbase.trans
  apply (div_le_iff₀ (show 0 < 1 - x by linarith)).mpr
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem squarefreeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) {p : ℕ} (hp : p.Prime) :
    0 < squarefreeEulerFactor z p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  apply mul_pos
  · have h := div_nonneg hz hp0.le
    linarith
  · apply Real.rpow_pos_of_pos
    have h := (div_lt_one hp0).mpr hp1
    linarith

theorem squarefreeEulerFactor_log_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {p : ℕ} (hp : p.Prime) :
    |Real.log (squarefreeEulerFactor z p)| ≤ 4 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsub : 0 < 1 - 1 / (p : ℝ) := by
    have h := (div_lt_one hp0).mpr hp1
    linarith
  have hadd : 0 < 1 + z / (p : ℝ) := by positivity
  have hfrac : z / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hrec : 1 / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have h₁ := log_one_add_sub_error (div_nonneg hz hp0.le) hfrac
  have h₂ := log_one_sub_add_error (by positivity : (0 : ℝ) ≤ 1 / p) hrec
  have heq : Real.log (squarefreeEulerFactor z p) =
      (Real.log (1 + z / (p : ℝ)) - z / p) + z *
        (Real.log (1 - 1 / (p : ℝ)) + 1 / p) := by
    rw [squarefreeEulerFactor, Real.log_mul hadd.ne' (Real.rpow_pos_of_pos hsub z).ne',
      Real.log_rpow hsub]
    ring
  rw [heq]
  calc
    _ ≤ |Real.log (1 + z / (p : ℝ)) - z / p| +
        |z * (Real.log (1 - 1 / (p : ℝ)) + 1 / p)| := abs_add_le _ _
    _ ≤ 2 * (z / (p : ℝ)) ^ 2 + z * (2 * (1 / (p : ℝ)) ^ 2) := by
      rw [abs_mul, abs_of_nonneg hz]
      exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ hz)
    _ ≤ 4 / (p : ℝ) ^ 2 := by
      have hzsq : z ^ 2 ≤ 1 := by nlinarith
      field_simp
      nlinarith

theorem primeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 < primeEulerFactor z n := by
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn] using squarefreeEulerFactor_pos hz hn
  · simp [primeEulerFactor, hn]

theorem primeEulerFactor_log_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun n => Real.log (primeEulerFactor z n)) := by
  have hsum := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 4
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hsum
  intro n
  rw [Real.norm_eq_abs]
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn, mul_one_div] using squarefreeEulerFactor_log_bound hz hz1 hn
  · simp [primeEulerFactor, hn]

theorem squarefreeEulerProduct_pos {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < ∏' n : ℕ, primeEulerFactor z n := by
  rw [← Real.rexp_tsum_eq_tprod (primeEulerFactor_pos hz) (primeEulerFactor_log_summable hz hz1)]
  exact Real.exp_pos _

theorem squarefreeEulerProduct_eq (z : ℝ) :
    (∏' n : ℕ, primeEulerFactor z n) =
      ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p := by
  calc
    _ = ∏' n : ℕ, ({p : ℕ | p.Prime}.mulIndicator (squarefreeEulerFactor z)) n := by
      apply tprod_congr
      intro n
      by_cases hn : n.Prime <;> simp [primeEulerFactor, Set.mulIndicator, hn]
    _ = _ := (tprod_subtype {p : ℕ | p.Prime} (squarefreeEulerFactor z)).symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeDirichletSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The squarefree Dirichlet series and its Euler product

These identities begin the analytic discharge of the two fixed-exponent
Selberg–Delange expansions. They do not assume an asymptotic for the
coefficients.
-/
namespace JointDickman
open Finset ArithmeticFunction

 theorem squarefreeLeadingConstant_pos {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    0 < squarefreeLeadingConstant z := by
  unfold squarefreeLeadingConstant
  apply div_pos _ (Real.Gamma_pos_of_pos hz)
  change 0 < ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p
  rw [← squarefreeEulerProduct_eq]
  exact squarefreeEulerProduct_pos hz.le hz1

 theorem squarefreeWeight_abs_le_one_dup1 {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    |squarefreeWeight z n| ≤ 1 := by
  simp only [squarefreeWeight,coe_mk]
  split_ifs
  · rw [abs_of_nonneg (pow_nonneg hz _)]
    exact pow_le_one₀ hz hz1
  · norm_num

 theorem squarefreeDirichletSummand_term (z : ℝ) (s : ℂ) (n : ℕ) :
    squarefreeDirichletSummand z s n = LSeries.term (fun n => (squarefreeWeight z n : ℂ)) s n := by
  rw [LSeries.term_def₀ (by simp : (squarefreeWeight z 0 : ℂ) = 0)]
  rfl

 theorem squarefreeDirichletSummand_zero (z : ℝ) (s : ℂ) : squarefreeDirichletSummand z s 0 = 0 := by
  simp [squarefreeDirichletSummand]

 theorem squarefreeDirichletSummand_one (z : ℝ) (s : ℂ) : squarefreeDirichletSummand z s 1 = 1 := by
  simp [squarefreeDirichletSummand]

 theorem squarefreeDirichletSummand_mul (z : ℝ) (s : ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    squarefreeDirichletSummand z s (m*n) =
      squarefreeDirichletSummand z s m * squarefreeDirichletSummand z s n := by
  unfold squarefreeDirichletSummand
  rw [(squarefreeWeight_isMultiplicative z).2 hmn]
  push_cast
  rw [← Complex.ofReal_natCast m, ← Complex.ofReal_natCast n,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

 theorem squarefreeDirichletSummand_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (fun n => ‖squarefreeDirichletSummand z s n‖) := by
  have h : LSeriesSummable (fun n => (squarefreeWeight z n : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using squarefreeWeight_abs_le_one_dup1 hz hz1 n) hs
  simpa only [squarefreeDirichletSummand_term] using h.norm

 theorem squarefreeDirichletSummand_prime_tsum (z : ℝ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, squarefreeDirichletSummand z s (p^e)) = 1+(z:ℂ)*(p:ℂ)^(-s) := by
  have hpw : squarefreeWeight z p = z := by
    simpa only [pow_one,ite_true, if_true] using squarefreeWeight_prime_pow z hp (by omega : (1:ℕ) ≠ 0)
  rw [tsum_eq_sum (s := {0,1})]
  · simp [squarefreeDirichletSummand,hpw]
  · intro e he
    have he0 : e ≠ 0 := by intro h; apply he; simp [h]
    have he1 : e ≠ 1 := by intro h; apply he; simp [h]
    simp [squarefreeDirichletSummand,squarefreeWeight_prime_pow z hp he0,he1]

 theorem squarefreeDirichletSeries_eulerProduct {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1+(z:ℂ)*(p:ℂ)^(-s))
      (LSeries (fun n => (squarefreeWeight z n : ℂ)) s) := by
  have h := EulerProduct.eulerProduct_hasProd (squarefreeDirichletSummand_one z s)
    (fun {m n} hmn => squarefreeDirichletSummand_mul z s hmn)
    (squarefreeDirichletSummand_summable hz hz1 hs) (squarefreeDirichletSummand_zero z s)
  have he (p : Nat.Primes) : (∑' e : ℕ, squarefreeDirichletSummand z s (p.val^e)) =
      1+(z:ℂ)*(p:ℂ)^(-s) := squarefreeDirichletSummand_prime_tsum z s p.property
  have heq : (fun p : Nat.Primes => ∑' e : ℕ, squarefreeDirichletSummand z s (p.val^e)) =
      (fun p : Nat.Primes => 1+(z:ℂ)*(p:ℂ)^(-s)) := funext he
  rw [heq] at h
  simpa only [squarefreeDirichletSummand_term,LSeries] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

 theorem squarefreeEulerLog_norm_bound {z r : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hr : r < 1) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖squarefreeEulerLog z w‖ ≤ 2*‖w‖^2/(1-r) := by
  have hzw : ‖(z:ℂ)*w‖ ≤ ‖w‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
    exact mul_le_of_le_one_left (norm_nonneg _) hz1
  have hv := complex_log_error_bound hr (hzw.trans hw)
  have hm := complex_log_error_bound hr (show ‖-w‖ ≤ r by simpa only [norm_neg] using hw)
  have heq : squarefreeEulerLog z w = (Complex.log (1+(z:ℂ)*w)-(z:ℂ)*w)+
      (z:ℂ)*(Complex.log (1-w)+w) := by unfold squarefreeEulerLog; ring
  rw [heq]
  have hq : 0 ≤ ‖w‖^2/(1-r) := by positivity
  calc
    _ ≤ ‖Complex.log (1+(z:ℂ)*w)-(z:ℂ)*w‖+
        ‖(z:ℂ)*(Complex.log (1-w)+w)‖ := norm_add_le _ _
    _ ≤ ‖w‖^2/(1-r)+‖w‖^2/(1-r) := by
      apply add_le_add
      · exact hv.trans (div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hzw) (by linarith))
      · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
        have hm' : ‖Complex.log (1-w)+w‖ ≤ ‖w‖^2/(1-r) := by
          simpa only [norm_neg,sub_neg_eq_add,← sub_eq_add_neg] using hm
        exact (mul_le_mul_of_nonneg_left hm' hz).trans (mul_le_of_le_one_left hq hz1)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeEulerAnalytic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic Euler correction in the half-plane Re(s) > 1/2 -/
namespace JointDickman
open scoped Topology

 theorem prime_negative_cpow_norm_le {σ : ℝ} (hσ : 0 ≤ σ) {s : ℂ} (hs : σ ≤ s.re)
    (p : Nat.Primes) : ‖(p.val:ℂ)^(-s)‖ ≤ (2:ℝ)^(-σ) := by
  rw [Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.neg_re]
  calc
    _ ≤ (p.val:ℝ)^(-σ) := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast p.property.one_le) (by linarith)
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by exact_mod_cast p.property.two_le) (by linarith)

 theorem squarefreePrimeLog_uniform_bound {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖squarefreePrimeLog z s p‖ ≤ (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ) := by
  have hr : (2:ℝ)^(-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hn : ‖(p.val:ℂ)^(-s)‖ ≤ (p.val:ℝ)^(-σ) := by
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (by linarith)
  calc
    _ ≤ 2*‖(p.val:ℂ)^(-s)‖^2/(1-(2:ℝ)^(-σ)) :=
      squarefreeEulerLog_norm_bound hz hz1 hr (prime_negative_cpow_norm_le hσ.le hs p)
    _ ≤ 2*((p.val:ℝ)^(-σ))^2/(1-(2:ℝ)^(-σ)) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr hn) (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg p.val)]
      norm_num only [Nat.cast_ofNat]
      rw [show -σ*(2:ℝ) = -2*σ by ring]
      ring

 theorem squarefreePrimeLog_bound_summable {σ : ℝ} (hσ : 1/2 < σ) :
    Summable (fun p : Nat.Primes => (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ)) := by
  have hsum : Summable (fun n : ℕ => (n:ℝ)^(-2*σ)) := Real.summable_nat_rpow.mpr (by linarith)
  exact (hsum.subtype Nat.Prime).mul_left _

 theorem squarefreePrimeLog_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1/2 < s.re) : Summable (fun p : Nat.Primes => squarefreePrimeLog z s p) := by
  apply Summable.of_norm
  exact (squarefreePrimeLog_bound_summable hs).of_nonneg_of_le (fun p => norm_nonneg _)
    (fun p => squarefreePrimeLog_uniform_bound hz hz1 (by linarith) le_rfl p)

 theorem squarefreePrimeLog_differentiableAt {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 0 < s.re) (p : Nat.Primes) :
    DifferentiableAt ℂ (fun t => squarefreePrimeLog z t p) s := by
  have hw : ‖(p.val:ℂ)^(-s)‖ < 1 :=
    (prime_negative_cpow_norm_le hs.le le_rfl p).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hzw : ‖(z:ℂ)*(p.val:ℂ)^(-s)‖ < 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
    exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt hw
  have hp0 : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hf : DifferentiableAt ℂ (fun t : ℂ => (p.val:ℂ)^(-t)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hp0)
  have h₁ := ((differentiableAt_const (1:ℂ)).add ((differentiableAt_const (z:ℂ)).mul hf)).clog
    (Complex.mem_slitPlane_of_norm_lt_one hzw)
  have hslit : 1-(p.val:ℂ)^(-s) ∈ Complex.slitPlane := by
    have hh : ‖-((p.val:ℂ)^(-s))‖ < 1 := by simpa only [norm_neg] using hw
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hh
  have h₂ := ((differentiableAt_const (1:ℂ)).sub hf).clog hslit
  exact h₁.add ((differentiableAt_const (z:ℂ)).mul h₂)

 theorem squarefreeLogFactor_differentiableOn {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hσ : 1/2 < σ) : DifferentiableOn ℂ (squarefreeLogFactor z) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (squarefreePrimeLog_bound_summable hσ)
  · intro p s hs
    exact (squarefreePrimeLog_differentiableAt hz hz1 (by dsimp at hs <;> linarith) p).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact squarefreePrimeLog_uniform_bound hz hz1 (by linarith) hs.le p

 theorem squarefreeLogFactor_analyticOnNhd {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticOnNhd ℂ (squarefreeLogFactor z) {s : ℂ | 1/2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  have hσ : 1/2 < (s.re+1/2)/2 := by dsimp at hs <;> linarith
  have hmem : s ∈ {t : ℂ | (s.re+1/2)/2 < t.re} := by dsimp at hs ⊢; linarith
  have hopen : IsOpen {t : ℂ | (s.re+1/2)/2 < t.re} := isOpen_lt continuous_const Complex.continuous_re
  exact ((squarefreeLogFactor_differentiableOn hz hz1 hσ).differentiableAt (hopen.mem_nhds hmem)).differentiableWithinAt

 theorem squarefreeAnalyticFactor_analyticOnNhd {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticOnNhd ℂ (squarefreeAnalyticFactor z) {s : ℂ | 1/2 < s.re} :=
  (squarefreeLogFactor_analyticOnNhd hz hz1).cexp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerAtOne
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic Euler factor at the leading singularity -/
namespace JointDickman

 theorem squarefreePrimeLog_one {z : ℝ} (hz : 0 ≤ z) (p : Nat.Primes) :
    squarefreePrimeLog z 1 p = (Real.log (squarefreeEulerFactor z p.val) : ℂ) := by
  have hp0 : (0:ℝ) < p.val := by exact_mod_cast p.property.pos
  have hp1 : (1:ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hsub : 0 < 1-1/(p.val:ℝ) := by
    have := (div_lt_one hp0).mpr hp1
    linarith
  have hadd : 0 < 1+z/(p.val:ℝ) := by positivity
  rw [squarefreeEulerFactor,Real.log_mul hadd.ne' (Real.rpow_pos_of_pos hsub z).ne',Real.log_rpow hsub]
  rw [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_log hadd.le,Complex.ofReal_log hsub.le]
  simp only [squarefreePrimeLog,squarefreeEulerLog,Complex.cpow_neg_one]
  push_cast
  simp only [div_eq_mul_inv,one_mul]

 theorem squarefreeEuler_log_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun p : Nat.Primes => Real.log (squarefreeEulerFactor z p.val)) := by
  convert! (primeEulerFactor_log_summable hz hz1).subtype Nat.Prime using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [Function.comp_def,primeEulerFactor,p.property,ite_true, if_true]

 theorem squarefreeAnalyticFactor_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    squarefreeAnalyticFactor z 1 = (∏' p : Nat.Primes, squarefreeEulerFactor z p.val : ℝ) := by
  have heq : squarefreeLogFactor z 1 = (∑' p : Nat.Primes, Real.log (squarefreeEulerFactor z p.val) : ℝ) := by
    rw [squarefreeLogFactor,Complex.ofReal_tsum]
    exact tsum_congr (squarefreePrimeLog_one hz)
  rw [squarefreeAnalyticFactor,heq,← Complex.ofReal_exp,
    Real.rexp_tsum_eq_tprod (fun p : Nat.Primes => squarefreeEulerFactor_pos hz p.property)
      (squarefreeEuler_log_summable hz hz1)]

 theorem squarefreeAnalyticFactor_one_gamma {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    squarefreeAnalyticFactor z 1 = (squarefreeLeadingConstant z * Real.Gamma z : ℝ) := by
  rw [squarefreeAnalyticFactor_one hz.le hz1,squarefreeLeadingConstant,
    div_mul_cancel₀ _ (Real.Gamma_pos_of_pos hz).ne']
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerFactorization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factorization of the squarefree Dirichlet series -/
namespace JointDickman

 theorem primeZetaLog_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => -Complex.log (1-(p.val:ℂ)^(-s))) := by
  convert! (summable_riemannZetaSummand hs).of_norm.clog_one_sub.neg.subtype Nat.Prime using 1
  all_goals try with_reducible_and_instances rfl

 theorem primeZetaLog_exp {s : ℂ} (hs : 1 < s.re) : Complex.exp (primeZetaLog s) = riemannZeta s := by
  exact (EulerProduct.exp_tsum_primes_log_eq_tsum (summable_riemannZetaSummand hs)).trans
    (tsum_riemannZetaSummand hs)

 theorem squarefreeDirichletSeries_factorization {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (squarefreeWeight z n : ℂ)) s =
      squarefreeAnalyticFactor z s * Complex.exp ((z:ℂ)*primeZetaLog s) := by
  have hG := squarefreePrimeLog_summable hz hz1 (show 1/2 < s.re by linarith)
  have hZ := (primeZetaLog_summable hs).mul_left (z:ℂ)
  have hsum := (hG.add hZ).hasSum.cexp
  rw [Summable.tsum_add hG hZ,tsum_mul_left,Complex.exp_add] at hsum
  have heq (p : Nat.Primes) : Complex.exp (squarefreePrimeLog z s p+
      (z:ℂ)*(-Complex.log (1-(p.val:ℂ)^(-s)))) = 1+(z:ℂ)*(p.val:ℂ)^(-s) := by
    have hnorm : ‖(z:ℂ)*(p.val:ℂ)^(-s)‖ < 1 := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt
        ((Complex.norm_prime_cpow_le_one_half p hs).trans_lt (by norm_num))
    have hn : 1+(z:ℂ)*(p.val:ℂ)^(-s) ≠ 0 := by
      intro he
      have hh : (z:ℂ)*(p.val:ℂ)^(-s) = -1 := by linear_combination he
      rw [hh,norm_neg,norm_one] at hnorm
      exact (lt_irrefl _ hnorm)
    have hcancel : squarefreePrimeLog z s p+(z:ℂ)*(-Complex.log (1-(p.val:ℂ)^(-s))) =
        Complex.log (1+(z:ℂ)*(p.val:ℂ)^(-s)) := by
      unfold squarefreePrimeLog squarefreeEulerLog
      ring
    rw [hcancel,Complex.exp_log hn]
  have hp : HasProd (fun p : Nat.Primes => 1+(z:ℂ)*(p.val:ℂ)^(-s))
      (squarefreeAnalyticFactor z s*Complex.exp ((z:ℂ)*primeZetaLog s)) := by
    have hf : (Complex.exp ∘ (fun p : Nat.Primes => squarefreePrimeLog z s p+
        (z:ℂ)*(-Complex.log (1-(p.val:ℂ)^(-s))))) =
        (fun p : Nat.Primes => 1+(z:ℂ)*(p.val:ℂ)^(-s)) := funext heq
    rw [hf] at hsum
    simpa only [squarefreeAnalyticFactor,squarefreeLogFactor,primeZetaLog] using hsum
  exact (squarefreeDirichletSeries_eulerProduct hz hz1 hs).unique hp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_PrimeZetaLogAnalytic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analyticity of the Euler logarithm in the absolutely convergent half-plane -/
namespace JointDickman

theorem primeZetaLog_summand_bound {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re)
    (p : Nat.Primes) : ‖-Complex.log (1-(p.val:ℂ)^(-s))‖ ≤
      (3/2:ℝ)*(p.val:ℝ)^(-σ) := by
  have hhalf : ‖(p.val:ℂ)^(-s)‖ ≤ 1/2 := Complex.norm_prime_cpow_le_one_half p (hσ.trans_le hs)
  have hh := Complex.norm_log_one_add_half_le_self (z := -((p.val:ℂ)^(-s)))
    (by simpa only [norm_neg] using hhalf)
  rw [norm_neg]
  calc
    _ ≤ (3/2:ℝ)*‖(p.val:ℂ)^(-s)‖ := by simpa only [sub_eq_add_neg,norm_neg] using hh
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (by linarith)

theorem primeZetaLog_differentiableOn {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ primeZetaLog {s : ℂ | σ < s.re} := by
  have hsum : Summable (fun p : Nat.Primes => (3/2:ℝ)*(p.val:ℝ)^(-σ)) := by
    exact ((Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).subtype Nat.Prime).mul_left _
  apply Complex.differentiableOn_tsum_of_summable_norm hsum
  · intro p s hs
    have hw : ‖-((p.val:ℂ)^(-s))‖ < 1 := by
      rw [norm_neg]
      exact (Complex.norm_prime_cpow_le_one_half p (by dsimp at hs <;> linarith)).trans_lt (by norm_num)
    have hc : DifferentiableAt ℂ (fun t : ℂ => (p.val:ℂ)^(-t)) s :=
      differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast p.property.ne_zero))
    exact (((differentiableAt_const (1:ℂ)).sub hc).clog
      (by simpa only [Pi.add_apply,Pi.neg_apply,sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one hw)).neg.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact primeZetaLog_summand_bound hσ hs.le p

theorem primeZetaLog_analyticOnNhd : AnalyticOnNhd ℂ primeZetaLog {s : ℂ | 1 < s.re} := by
  intro s hs
  have hσ : 1 < (1+s.re)/2 := by dsimp at hs <;> linarith
  have hm : s ∈ {t : ℂ | (1+s.re)/2 < t.re} := by dsimp at hs ⊢; linarith
  exact (primeZetaLog_differentiableOn hσ).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re) s hm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_PrimeZetaLogReal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real branch of the logarithmic Euler product -/
namespace JointDickman

 theorem negative_real_log_im_zero {r : ℝ} (hr : r ≤ 1) :
    (-Complex.log (1-(r:ℂ))).im = 0 := by
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_log (sub_nonneg.mpr hr)]
  simp

 theorem primeZetaLog_im_eq_zero {σ : ℝ} (hσ : 1 < σ) : (primeZetaLog (σ:ℂ)).im = 0 := by
  rw [primeZetaLog,Complex.im_tsum (primeZetaLog_summable (by simpa using hσ))]
  calc
    _ = ∑' _p : Nat.Primes, (0:ℝ) := by
      apply tsum_congr
      intro p
      have hp0 : 0 < (p.val:ℝ) := by exact_mod_cast p.property.pos
      have hpow : (p.val:ℝ)^(-σ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by linarith)
      have heq : (p.val:ℂ)^(-(σ:ℂ)) = ((p.val:ℝ)^(-σ) : ℝ) := by
        simpa only [Complex.ofReal_neg,Complex.ofReal_natCast] using (Complex.ofReal_cpow hp0.le (-σ)).symm
      rw [heq]
      exact negative_real_log_im_zero hpow.le
    _ = 0 := by simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_PrimeZetaPoleLog
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euler logarithm of the pole-removed zeta function -/
namespace JointDickman

theorem primeZetaPoleLog_exp {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (primeZetaPoleLog s) = zetaPoleFactor s := by
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  rw [primeZetaPoleLog,Complex.exp_add,primeZetaLog_exp hs,
    Complex.exp_log (sub_ne_zero.mpr hs1),zetaPoleFactor_eq hs1,mul_comm]

theorem primeZetaPoleLog_analyticAt {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ primeZetaPoleLog s := by
  have hl : s-1 ∈ Complex.slitPlane := by
    left
    simpa only [Complex.sub_re,Complex.one_re,sub_pos] using hs
  exact (primeZetaLog_analyticOnNhd s hs).add ((analyticAt_id.sub analyticAt_const).clog hl)

theorem primeZetaPoleLog_real {σ : ℝ} (hσ : 1 < σ) :
    primeZetaPoleLog (σ:ℂ) = Complex.log (zetaPoleFactor (σ:ℂ)) := by
  have him : (primeZetaPoleLog (σ:ℂ)).im = 0 := by
    rw [primeZetaPoleLog,Complex.add_im,primeZetaLog_im_eq_zero hσ]
    have hh : (σ:ℂ)-1 = ((σ-1:ℝ):ℂ) := by push_cast; rfl
    rw [hh,←Complex.ofReal_log (by linarith : 0 ≤ σ-1),Complex.ofReal_im,add_zero]
  rw [←primeZetaPoleLog_exp (by simpa only [Complex.ofReal_re] using hσ)]
  symm
  apply Complex.log_exp <;> rw [him] <;> linarith [Real.pi_pos]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszDenominatorBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform integrable bounds for the Riesz--Perron denominator -/
namespace JointDickman

theorem rieszDenominator_im_lower_bound (s : ℂ) :
    s.im^2 ≤ ‖s‖*‖s+1‖ := by
  have h1 := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ ‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have h := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs s.im]

theorem rieszDenominator_lower_bound {s : ℂ} (hs : 1/2 ≤ s.re) :
    (1+s.im^2)/5 ≤ ‖s‖*‖s+1‖ := by
  have h1 : (1/2:ℝ) ≤ ‖s‖ := hs.trans ((le_abs_self _).trans (Complex.abs_re_le_norm s))
  have h2 : (1/2:ℝ) ≤ ‖s+1‖ := by
    have h := Complex.abs_re_le_norm (s+1)
    have hle := le_abs_self (s+1).re
    simp only [Complex.add_re,Complex.one_re] at h hle
    linarith
  have hprod : (1/2:ℝ)*(1/2) ≤ ‖s‖*‖s+1‖ :=
    mul_le_mul h1 h2 (by norm_num) (norm_nonneg _)
  nlinarith [rieszDenominator_im_lower_bound s]

theorem rieszDenominator_inv_bound {s : ℂ} (hs : 1/2 ≤ s.re) :
    1/(‖s‖*‖s+1‖) ≤ 5/(1+s.im^2) := by
  have hp : 0 < (1+s.im^2)/5 := by positivity
  have h := one_div_le_one_div_of_le hp (rieszDenominator_lower_bound hs)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the Euler correction on the shifted contour -/
namespace JointDickman

theorem squarefreeAnalyticFactor_uniform_bound {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hσ : 1/2 < σ) : ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, σ ≤ s.re → ‖squarefreeAnalyticFactor z s‖ ≤ C := by
  let b : Nat.Primes → ℝ := fun p => (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ)
  have hb : Summable b := squarefreePrimeLog_bound_summable hσ
  refine ⟨Real.exp (∑' p, b p),Real.exp_pos _,fun s hs => ?_⟩
  have hf := squarefreePrimeLog_summable hz hz1 (hσ.trans_le hs)
  have hl : ‖squarefreeLogFactor z s‖ ≤ ∑' p, b p := by
    calc
      _ ≤ ∑' p, ‖squarefreePrimeLog z s p‖ := norm_tsum_le_tsum_norm hf.norm
      _ ≤ _ := hf.norm.tsum_le_tsum
        (fun p => squarefreePrimeLog_uniform_bound hz hz1 (by linarith) hs p) hb
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hl)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeSingularFactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic factor determining the Selberg–Delange coefficients -/
namespace JointDickman

 theorem squarefreeSingularFactor_analyticAt_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticAt ℂ (squarefreeSingularFactor z) 1 := by
  have hG := squarefreeAnalyticFactor_analyticOnNhd hz hz1 (1:ℂ) (by norm_num)
  have hH : AnalyticAt ℂ (fun s => Complex.log (zetaPoleFactor s)) 1 :=
    zetaPoleFactor_analyticAt_one.clog (by simp only [zetaPoleFactor_one]; exact Complex.one_mem_slitPlane)
  exact (hG.mul ((analyticAt_const.mul hH).cexp')).div analyticAt_id (by norm_num)

 theorem squarefreeSingularFactor_one {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    squarefreeSingularFactor z 1 = (squarefreeLeadingConstant z * Real.Gamma z : ℝ) := by
  simpa only [squarefreeSingularFactor,zetaPoleFactor_one,Complex.log_one,mul_zero,Complex.exp_zero,
    mul_one,div_one] using squarefreeAnalyticFactor_one_gamma hz hz1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeContourSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuation of the squarefree series on a slit zero-free rectangle -/
namespace JointDickman
open Set Filter
open scoped Topology

theorem squarefreeContourSeries_norm {z : ℝ} {f : ℂ → ℂ} {s : ℂ}
    (hs : s ≠ 1) (hf : Complex.exp (f s) = zetaPoleFactor s) :
    ‖squarefreeContourSeries z f s‖ = ‖squarefreeAnalyticFactor z s‖*‖riemannZeta s‖^z := by
  have he : Complex.exp (f s-Complex.log (s-1)) = riemannZeta s := by
    rw [Complex.exp_sub,hf,Complex.exp_log (sub_ne_zero.mpr hs),zetaPoleFactor_eq hs]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs)
  rw [squarefreeContourSeries,norm_mul,norm_exp_real_mul_of_exp_eq z he]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The analytic factor of the Riesz--Perron contour integrand -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem squarefreeRieszKernel_factorization (z L : ℝ) (f : ℂ → ℂ) (w : ℂ) :
    fractionalContourIntegrand z (squarefreeRieszKernel z L f) w =
      squarefreeContourSeries z f (1+w) * exp ((L:ℂ)*w) / ((1+w)*(2+w)) := by
  simp only [fractionalContourIntegrand,squarefreeRieszKernel,fractionalPowerKernel,
    squarefreeContourSeries,add_sub_cancel_left,mul_sub,Complex.exp_sub,Complex.exp_neg,neg_mul]
  ring

theorem squarefreeRieszKernel_analyticAt {z L : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f (1+w)) (hw : 1/2 < (1+w).re) :
    AnalyticAt ℂ (squarefreeRieszKernel z L f) w := by
  have hw1 : (1+w) ≠ 0 := by
    intro h
    rw [h] at hw
    norm_num at hw
  have hw2 : (2+w) ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    norm_num at he
    simp only [add_re,one_re] at hw
    linarith
  have ha : AnalyticAt ℂ (fun w : ℂ => 1+w) w := analyticAt_const.add analyticAt_id
  have hb : AnalyticAt ℂ (fun w : ℂ => 2+w) w := analyticAt_const.add analyticAt_id
  have hG := (squarefreeAnalyticFactor_analyticOnNhd hz hz1 (1+w) hw).comp ha
  have hlog := hf.comp ha
  exact (((hG.mul (analyticAt_const.mul hlog).cexp').mul
    (analyticAt_const.mul analyticAt_id).cexp').div (ha.mul hb) (mul_ne_zero hw1 hw2))

theorem squarefreeRieszKernel_norm {z L : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hw : w ≠ 0) (hf : exp (f (1+w)) = zetaPoleFactor (1+w)) :
    ‖fractionalContourIntegrand z (squarefreeRieszKernel z L f) w‖ =
      ‖squarefreeAnalyticFactor z (1+w)‖ * ‖riemannZeta (1+w)‖^z *
        Real.exp (L*w.re) / (‖1+w‖*‖2+w‖) := by
  have hw1 : (1+w) ≠ 1 := by intro h; apply hw; linear_combination h
  rw [squarefreeRieszKernel_factorization,norm_div,norm_mul,
    squarefreeContourSeries_norm hw1 hf,norm_mul,Complex.norm_exp]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_RieszContourBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrable majorants for the squarefree Riesz contour -/
namespace JointDickman
open Complex Set MeasureTheory

theorem squarefreeRieszKernel_bound {z L C B : ℝ} (hz : 0 ≤ z)
    {f : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0) (hs : 1/2 ≤ (1+w).re)
    (hf : exp (f (1+w)) = zetaPoleFactor (1+w))
    (hG : ‖squarefreeAnalyticFactor z (1+w)‖ ≤ C)
    (hζ : ‖riemannZeta (1+w)‖ ≤ B) :
    ‖fractionalContourIntegrand z (squarefreeRieszKernel z L f) w‖ ≤
      5*C*B^z*Real.exp (L*w.re)/(1+w.im^2) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hG
  have hB : 0 ≤ B := (norm_nonneg _).trans hζ
  have hden : 1/(‖1+w‖*‖2+w‖) ≤ 5/(1+w.im^2) := by
    simpa only [show (1:ℂ)+w+1 = 2+w by ring,add_im,one_im,zero_add] using
      rieszDenominator_inv_bound hs
  rw [squarefreeRieszKernel_norm hw hf,div_eq_mul_inv]
  calc
    _ ≤ (C*B^z*Real.exp (L*w.re))*(5/(1+w.im^2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul hG (Real.rpow_le_rpow (norm_nonneg _) hζ hz)
            (Real.rpow_nonneg (norm_nonneg _) _) hC) (Real.exp_pos _).le
      · simpa only [one_div] using hden
      · positivity
      · positivity
    _ = _ := by ring

theorem verticalIntegral_bound_by_cauchy {f : ℂ → ℂ} {σ T D : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Ioc (-T) T, ‖f ((σ:ℂ)+(t:ℂ)*I)‖ ≤ D/(1+t^2)) :
    ‖VIntegral f σ (-T) T‖ ≤ D*Real.pi := by
  have hi : Integrable (fun t : ℝ => D/(1+t^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul D
  rw [VIntegral,norm_smul,Complex.norm_I,one_mul,
    intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, D/(1+t^2) := by
      apply norm_integral_le_of_norm_le hi.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hf t ht
    _ ≤ ∫ t : ℝ, D/(1+t^2) := by
      apply setIntegral_le_integral hi
      filter_upwards with t
      positivity
    _ = D*Real.pi := by
      simp only [div_eq_mul_inv,integral_const_mul,integral_univ_inv_one_add_sq]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeContourIdentification
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Agreement of the continuation with the original squarefree series -/
namespace JointDickman
open Set Filter
open scoped Topology

theorem squarefreeContourSeries_eq_LSeries_on_right {z δ T : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : 0 < δ) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T)) (hf1 : f 1 = 0)
    (he : ∀ s ∈ zetaOpenRectangle δ T, Complex.exp (f s) = zetaPoleFactor s) :
    ∀ s ∈ zetaOpenRectangle 0 T,
      squarefreeContourSeries z f s = LSeries (fun n => (squarefreeWeight z n:ℂ)) s := by
  have h1 := zetaOpenRectangle_one hδ hT
  have hlocal := normalized_log_eq_principal_near (hf 1 h1).continuousAt hf1
    (Filter.eventuallyEq_of_mem ((zetaOpenRectangle_isOpen δ T).mem_nhds h1) he)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  let d := min ε 1 / 2
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hdε : d < ε := by dsimp [d]; have := min_le_left ε 1; linarith
  have hd1 : d < 1 := by dsimp [d]; have := min_le_right ε 1; linarith
  have hw : ((1+d:ℝ):ℂ) ∈ zetaOpenRectangle 0 T := by
    change (1+d ∈ Ioo (1-0) 2) ∧ (0:ℝ) ∈ Ioo (-T) T
    constructor <;> constructor <;> linarith
  have hsub : zetaOpenRectangle 0 T ⊆ zetaOpenRectangle δ T := by
    intro s hs
    exact ⟨⟨by have := hs.1.1; linarith,hs.1.2⟩,hs.2⟩
  have hbase : f ((1+d:ℝ):ℂ) = primeZetaPoleLog ((1+d:ℝ):ℂ) := by
    rw [primeZetaPoleLog_real (by linarith : 1 < 1+d)]
    apply hball
    rw [dist_eq_norm]
    have heq : (((1+d:ℝ):ℂ)-1) = (d:ℂ) := by push_cast <;> ring
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    exact hdε
  let : ContractibleSpace (zetaOpenRectangle 0 T) :=
    (zetaOpenRectangle_convex 0 T).contractibleSpace ⟨_,hw⟩
  have hsim : IsSimplyConnected (zetaOpenRectangle 0 T) := by
    change SimplyConnectedSpace _
    infer_instance
  have hg : AnalyticOnNhd ℂ primeZetaPoleLog (zetaOpenRectangle 0 T) := by
    intro s hs
    exact primeZetaPoleLog_analyticAt (by simpa only [sub_zero] using hs.1.1)
  have hsame := analytic_log_unique (zetaOpenRectangle_isOpen 0 T)
    hsim.isPathConnected.isConnected.isPreconnected (hf.mono hsub) hg
    (fun s hs => (he s (hsub hs)).trans (primeZetaPoleLog_exp
      (by simpa only [sub_zero] using hs.1.1)).symm) hw hbase
  intro s hs
  rw [squarefreeContourSeries,hsame hs,primeZetaPoleLog,add_sub_cancel_right]
  exact (squarefreeDirichletSeries_factorization hz hz1
    (by simpa only [sub_zero] using hs.1.1)).symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaContourBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
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

theorem zeta_fractional_power_high_bound : ∃ A C : ℝ,
    A ∈ Ioc 0 (1/2) ∧ 0 < C ∧
    ∀ (z σ t : ℝ), 0 ≤ z → z ≤ 1 → 3 < |t| → σ ∈ Icc (1-A/Real.log |t|) 2 →
      ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖^z ≤ C*|t|^(1/2:ℝ) := by
  obtain ⟨A,hA,C,hC,hb⟩ := ZetaUpperBnd
  refine ⟨A,max 1 (2*C),hA,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z σ t hz hz1 ht hσ
  have ht1 : 1 ≤ |t| := by linarith
  have hp : 1 ≤ |t|^(1/2:ℝ) := Real.one_le_rpow ht1 (by norm_num)
  by_cases hn : ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖ ≤ 1
  · calc
      _ ≤ 1 := Real.rpow_le_one (norm_nonneg _) hn hz
      _ ≤ |t|^(1/2:ℝ) := hp
      _ ≤ max 1 (2*C)*|t|^(1/2:ℝ) := by
        exact le_mul_of_one_le_left (Real.rpow_nonneg (abs_nonneg _) _) (le_max_left _ _)
  · calc
      _ ≤ ‖riemannZeta ((σ:ℂ)+(t:ℂ)*I)‖ := Real.rpow_le_self_of_one_le (le_of_not_ge hn) hz1
      _ ≤ C*Real.log |t| := hb σ t ht hσ
      _ ≤ C*(|t|^(1/2:ℝ)/(1/2)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (abs_nonneg _) (by norm_num)) hC.le
      _ = (2*C)*|t|^(1/2:ℝ) := by ring
      _ ≤ max 1 (2*C)*|t|^(1/2:ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _)

theorem zeta_left_contour_bound : ∃ A C : ℝ,
    A ∈ Ioc 0 (1/2) ∧ 0 < C ∧
    ∀ (δ T : ℝ), 0 < δ → δ ≤ 1/4 → 4 ≤ T → δ ≤ A/Real.log T →
      ∀ t : ℝ, |t| ≤ T → ‖riemannZeta (((1-δ:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ C/δ := by
  obtain ⟨A,hA,C₁,hC₁,hb⟩ := ZetaUpperBnd
  obtain ⟨C₀,hC₀,hcompact⟩ := zetaPole_compact_bound
  refine ⟨A,C₀+C₁,hA,add_pos hC₀ hC₁,?_⟩
  intro δ T hδ hδ4 hT hδA t htT
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hδlog : δ*Real.log T ≤ 1 := by
    have h := (le_div_iff₀ hlogT).mp hδA
    linarith [hA.2]
  by_cases ht : |t| ≤ 3
  · have hn : ‖(((1-δ:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ 6 := by
      have h := Complex.norm_le_abs_re_add_abs_im (((1-δ:ℝ):ℂ)+(t:ℂ)*I)
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,
        sub_zero,add_zero,add_im,mul_im,mul_one,zero_add] at h
      rw [abs_of_nonneg (by linarith : 0 ≤ 1-δ)] at h
      linarith
    have hs : (((1-δ:ℝ):ℂ)+(t:ℂ)*I) ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_zero,one_re] at hr
      linarith
    have hd : δ ≤ ‖(((1-δ:ℝ):ℂ)+(t:ℂ)*I)-1‖ := by
      have h := Complex.abs_re_le_norm ((((1-δ:ℝ):ℂ)+(t:ℂ)*I)-1)
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_zero,one_re,sub_sub_cancel_left,abs_neg,abs_of_pos hδ] at h
      exact h
    calc
      _ ≤ C₀/‖(((1-δ:ℝ):ℂ)+(t:ℂ)*I)-1‖ := hcompact _ hn hs
      _ ≤ C₀/δ := div_le_div_of_nonneg_left hC₀.le hδ hd
      _ ≤ (C₀+C₁)/δ := div_le_div_of_nonneg_right (by linarith) hδ.le
  · have ht3 : 3 < |t| := lt_of_not_ge ht
    have hlogt : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hlogs : Real.log |t| ≤ Real.log T := Real.log_le_log (by linarith) htT
    have hd : δ ≤ A/Real.log |t| := hδA.trans
      (div_le_div_of_nonneg_left hA.1.le hlogt hlogs)
    calc
      _ ≤ C₁*Real.log |t| := hb (1-δ) t ht3 ⟨by linarith,by linarith⟩
      _ ≤ C₁*Real.log T := mul_le_mul_of_nonneg_left hlogs hC₁.le
      _ ≤ C₁/δ := by
        apply (le_div_iff₀ hδ).mpr
        nlinarith
      _ ≤ (C₀+C₁)/δ := div_le_div_of_nonneg_right (by linarith) hδ.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeLSeriesBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the original squarefree Dirichlet series on the right -/
namespace JointDickman
open Complex Set

theorem squarefreeLSeries_norm {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (fun n => (squarefreeWeight z n:ℂ)) s‖ =
      ‖squarefreeAnalyticFactor z s‖*‖riemannZeta s‖^z := by
  rw [squarefreeDirichletSeries_factorization hz hz1 hs,norm_mul,
    norm_exp_real_mul_of_exp_eq z (primeZetaLog_exp hs)]

theorem squarefreeLSeries_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → 3 < |s.im| →
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)) s‖ ≤ C*|s.im|^(1/2:ℝ) := by
  obtain ⟨G,hG,hGb⟩ := squarefreeAnalyticFactor_uniform_bound hz hz1 (by norm_num : (1/2:ℝ) < 1)
  obtain ⟨A,C,hA,hC,hCb⟩ := zeta_fractional_power_high_bound
  refine ⟨G*C,mul_pos hG hC,?_⟩
  intro s hs hs2 ht
  have hlog : 0 < Real.log |s.im| := Real.log_pos (by linarith)
  have hlow : 1-A/Real.log |s.im| ≤ s.re := by
    have hp := div_pos hA.1 hlog
    linarith
  have hζ := hCb z s.re s.im hz hz1 ht ⟨hlow,hs2⟩
  rw [Complex.re_add_im] at hζ
  rw [squarefreeLSeries_norm hz hz1 hs]
  calc
    _ ≤ G*(C*|s.im|^(1/2:ℝ)) := mul_le_mul (hGb s hs.le) hζ
      (Real.rpow_nonneg (norm_nonneg _) _) hG.le
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreePerronBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decay of the original Perron integrand on the right-hand line -/
namespace JointDickman
open Complex

theorem squarefreeNormalizedPerron_norm (z L : ℝ) (w : ℂ) :
    ‖squarefreeNormalizedPerron z L w‖ =
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)) (1+w)‖ * Real.exp (L*w.re) /
        (‖1+w‖*‖2+w‖) := by
  simp only [squarefreeNormalizedPerron,norm_div,norm_mul,Complex.norm_exp,
    mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]

theorem squarefreeNormalizedPerron_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (w : ℂ), 0 < w.re → w.re ≤ 1 → 3 < |w.im| →
      ‖squarefreeNormalizedPerron z L w‖ ≤
        C*Real.exp (L*w.re)*|w.im|^(-3/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := squarefreeLSeries_high_bound hz hz1
  refine ⟨C,hC,?_⟩
  intro L w hw hw1 ht
  have ht0 : 0 < |w.im| := by linarith
  have hs := hb (1+w) (by simpa using hw) (by simp only [add_re,one_re] <;> linarith) (by simpa using ht)
  simp only [add_im,one_im,zero_add] at hs
  have hd : |w.im|^2 ≤ ‖1+w‖*‖2+w‖ := by
    simpa only [add_im,one_im,zero_add,sq_abs,
      show (1:ℂ)+w+1 = 2+w by ring] using rieszDenominator_im_lower_bound (1+w)
  have hp : |w.im|^(1/2:ℝ)/|w.im|^2 = |w.im|^(-3/2:ℝ) := by
    rw [←Real.rpow_ofNat,←Real.rpow_sub ht0]
    norm_num
  rw [squarefreeNormalizedPerron_norm]
  calc
    _ ≤ (C*|w.im|^(1/2:ℝ)*Real.exp (L*w.re))/|w.im|^2 := by
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_right hs (Real.exp_pos _).le) (pow_pos ht0 2) hd
    _ = C*Real.exp (L*w.re)*(|w.im|^(1/2:ℝ)/|w.im|^2) := by ring
    _ = _ := by rw [hp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreePerronIntegrable
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute integrability of the actual normalized Perron line -/
namespace JointDickman
open Complex MeasureTheory

theorem squarefreeLSeries_measurable (z : ℝ) :
    Measurable (LSeries (fun n => (squarefreeWeight z n:ℂ))) := by
  apply Measurable.tsum
  intro n
  apply Continuous.measurable
  exact continuous_iff_continuousAt.mpr (fun s => (LSeries.hasDerivAt_term _ n s).continuousAt)

theorem squarefreeLSeries_vertical_bound {z σ : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hσ : 1 < σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)) ((σ:ℂ)+(t:ℂ)*I)‖ ≤ M := by
  have hs (t : ℝ) : LSeriesSummable (fun n => (squarefreeWeight z n:ℂ)) ((σ:ℂ)+(t:ℂ)*I) :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using squarefreeWeight_abs_le_one_dup1 hz hz1 n)
      (by simpa using hσ)
  let M := ∑' n, ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)) ((σ:ℂ)+(0:ℂ)*I) n‖
  refine ⟨M,tsum_nonneg (fun _ => norm_nonneg _),fun t => ?_⟩
  calc
    _ ≤ ∑' n, ‖LSeries.term (fun n => (squarefreeWeight z n:ℂ)) ((σ:ℂ)+(t:ℂ)*I) n‖ :=
      norm_tsum_le_tsum_norm (hs t).norm
    _ = M := by
      apply tsum_congr
      intro n
      simp only [LSeries.norm_term_eq,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
        mul_zero,zero_mul,sub_zero,add_zero]

theorem squarefreeNormalizedPerron_integrable {z L c : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hc : 0 < c) :
    Integrable (fun t : ℝ => squarefreeNormalizedPerron z L ((c:ℂ)+(t:ℂ)*I)) := by
  obtain ⟨M,hM,hMb⟩ := squarefreeLSeries_vertical_bound hz hz1 (show 1 < 1+c by linarith)
  have hm : Measurable (fun t : ℝ => squarefreeNormalizedPerron z L ((c:ℂ)+(t:ℂ)*I)) := by
    unfold squarefreeNormalizedPerron
    exact ((squarefreeLSeries_measurable z).comp (by fun_prop)).mul (by fun_prop) |>.div (by fun_prop)
  have hi : Integrable (fun t : ℝ => (5*M*Real.exp (L*c))/(1+t^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (5*M*Real.exp (L*c))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards with t
  rw [squarefreeNormalizedPerron_norm]
  have hseries : ‖LSeries (fun n => (squarefreeWeight z n:ℂ)) (1+((c:ℂ)+(t:ℂ)*I))‖ ≤ M := by
    convert hMb t using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    push_cast
    ring
  have hden := rieszDenominator_inv_bound (s := 1+((c:ℂ)+(t:ℂ)*I)) (by simp <;> linarith)
  have hden' : 1/(‖1+((c:ℂ)+(t:ℂ)*I)‖*‖2+((c:ℂ)+(t:ℂ)*I)‖) ≤ 5/(1+t^2) := by
    simpa only [show (1:ℂ)+((c:ℂ)+(t:ℂ)*I)+1 = 2+((c:ℂ)+(t:ℂ)*I) by ring,
      add_im,one_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,zero_add,add_zero] using hden
  simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
  calc
    _ ≤ (M*Real.exp (L*c))*(5/(1+t^2)) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul (mul_le_mul_of_nonneg_right hseries (Real.exp_pos _).le)
        _ (by positivity) (by positivity)
      simpa only [one_div] using hden'
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreePerronNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized Perron inversion for the actual squarefree coefficients -/
namespace JointDickman
open Complex MeasureTheory

theorem squarefreeNormalizedPerron_eq_continuation {z L δ T : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : 0 < δ) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T)) (hf1 : f 1 = 0)
    (he : ∀ s ∈ zetaOpenRectangle δ T, exp (f s) = zetaPoleFactor s)
    {w : ℂ} (hw : 1+w ∈ zetaOpenRectangle 0 T) :
    squarefreeNormalizedPerron z L w =
      fractionalContourIntegrand z (squarefreeRieszKernel z L f) w := by
  rw [squarefreeRieszKernel_factorization,
    squarefreeContourSeries_eq_LSeries_on_right hz hz1 hδ hT hf hf1 he (1+w) hw]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreePerronTails
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two tails of the normalized squarefree Perron integral -/
namespace JointDickman
open Complex MeasureTheory Set

theorem squarefreeNormalizedPerron_tail_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L c T ε : ℝ), 0 < c → c ≤ 1 → 3 < T → |ε| = 1 →
      ‖∫ t : ℝ in Ioi T, squarefreeNormalizedPerron z L ((c:ℂ)+((ε*t:ℝ):ℂ)*I)‖ ≤
        2*C*Real.exp (L*c)*T^(-1/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := squarefreeNormalizedPerron_high_bound hz hz1
  refine ⟨C,hC,?_⟩
  intro L c T ε hc hc1 hT hε
  have hT0 : 0 < T := by linarith
  have hi : IntegrableOn (fun t : ℝ => C*Real.exp (L*c)*t^(-3/2:ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) hT0).const_mul _
  calc
    _ ≤ ∫ t : ℝ in Ioi T, C*Real.exp (L*c)*t^(-3/2:ℝ) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hT0.trans ht
      have hp := hb L ((c:ℂ)+((ε*t:ℝ):ℂ)*I)
        (by simpa using hc) (by simpa using hc1)
        (by simpa only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,
          zero_add,add_zero,abs_mul,hε,one_mul,abs_of_pos ht0] using hT.trans ht)
      simpa only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_zero,add_im,mul_im,mul_one,zero_add,add_zero,abs_mul,hε,one_mul,abs_of_pos ht0] using hp
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-3/2:ℝ) < -1) hT0]
      norm_num
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreePerronTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative truncation of the normalized squarefree Perron line -/
namespace JointDickman
open Complex MeasureTheory Set

theorem perron_normalization_norm :
    ‖(1/(2*(Real.pi:ℂ)*I):ℂ)‖ = 1/(2*Real.pi) := by
  simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]

theorem squarefreeNormalizedPerron_truncation_bound {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L c T : ℝ, 0 < c → c ≤ 1 → 3 < T →
      ‖VerticalIntegral' (squarefreeNormalizedPerron z L) c -
        (1/(2*(Real.pi:ℂ)*I))*VIntegral (squarefreeNormalizedPerron z L) c (-T) T‖ ≤
        C*Real.exp (L*c)*T^(-1/2:ℝ) := by
  obtain ⟨C,hC,hb⟩ := squarefreeNormalizedPerron_tail_bound hz hz1
  refine ⟨4*C/(2*Real.pi),by positivity,?_⟩
  intro L c T hc hc1 hT
  let P := squarefreeNormalizedPerron z L
  have hlo : ‖∫ t : ℝ in Iic (-T), P ((c:ℂ)+(t:ℂ)*I)‖ ≤
      2*C*Real.exp (L*c)*T^(-1/2:ℝ) := by
    rw [←integral_comp_neg_Ioi T (fun t : ℝ => P ((c:ℂ)+(t:ℂ)*I))]
    simpa only [neg_one_mul] using hb L c T (-1) hc hc1 hT (by norm_num)
  have hhi : ‖∫ t : ℝ in Ici T, P ((c:ℂ)+(t:ℂ)*I)‖ ≤
      2*C*Real.exp (L*c)*T^(-1/2:ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    simpa only [one_mul] using hb L c T 1 hc hc1 hT (by norm_num)
  have heq : VerticalIntegral' P c -
      (1/(2*(Real.pi:ℂ)*I))*VIntegral P c (-T) T =
      (1/(2*(Real.pi:ℂ)*I))*I*
        ((∫ t : ℝ in Iic (-T), P ((c:ℂ)+(t:ℂ)*I)) +
         (∫ t : ℝ in Ici T, P ((c:ℂ)+(t:ℂ)*I))) := by
    rw [VerticalIntegral',verticalIntegral_split_three (-T) T
      (squarefreeNormalizedPerron_integrable hz hz1 hc)]
    simp only [smul_eq_mul]
    ring
  rw [heq,norm_mul,norm_mul,perron_normalization_norm,norm_I,mul_one]
  calc
    _ ≤ (1/(2*Real.pi))*(
      ‖∫ t : ℝ in Iic (-T), P ((c:ℂ)+(t:ℂ)*I)‖ +
      ‖∫ t : ℝ in Ici T, P ((c:ℂ)+(t:ℂ)*I)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (1/(2*Real.pi))*(2*C*Real.exp (L*c)*T^(-1/2:ℝ) +
        2*C*Real.exp (L*c)*T^(-1/2:ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hlo hhi) (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszContourGeometry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interior geometry for the finite squarefree contour -/
namespace JointDickman
open Complex Set

theorem squarefreeRieszKernel_analytic_on_shifted_rectangle {z L δ T : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : δ ≤ 1/4)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T)))
    {w : ℂ} (hw : 1+w ∈ zetaOpenRectangle δ (2*T)) :
    AnalyticAt ℂ (squarefreeRieszKernel z L f) w := by
  apply squarefreeRieszKernel_analyticAt hz hz1 (hf (1+w) hw)
  have hs : 1-δ < (1+w).re := hw.1.1
  linarith

theorem squarefreeRieszKernel_contour_regular {z L δ c T : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (_hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    (hc : 0 < c) (hcδ : c ≤ δ/4) (hT : 1 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T))) :
    DifferentiableOn ℂ (squarefreeRieszKernel z L f)
      (Rectangle (-((δ/4:ℝ):ℂ)-(T:ℂ)*I) ((c:ℂ)+(T:ℂ)*I)) ∧
    ContinuousOn (squarefreeRieszKernel z L f) (Metric.closedBall 0 (3*δ/4)) := by
  constructor
  · intro w hw
    apply (squarefreeRieszKernel_analytic_on_shifted_rectangle hz hz1 hδ4 hf ?_).differentiableAt.differentiableWithinAt
    have hre : (-((δ/4:ℝ):ℂ)-(T:ℂ)*I).re ≤ ((c:ℂ)+(T:ℂ)*I).re := by
      simp only [sub_re,neg_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
        sub_zero,add_re,add_zero]
      linarith
    have him : (-((δ/4:ℝ):ℂ)-(T:ℂ)*I).im ≤ ((c:ℂ)+(T:ℂ)*I).im := by
      simp only [sub_im,neg_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_one,mul_zero,
        zero_add,zero_sub,neg_zero,add_im]
      linarith
    have hmem := (mem_Rect hre him w).mp hw
    simp only [sub_re,neg_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,
      sub_zero,add_re,add_zero,sub_im,neg_im,mul_im,mul_one,zero_add,zero_sub,neg_zero,add_im] at hmem
    change (1-δ < (1+w).re ∧ (1+w).re < 2) ∧ (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
    simp only [add_re,one_re,add_im,one_im,zero_add]
    constructor <;> constructor <;> linarith [hmem.1,hmem.2.1,hmem.2.2.1,hmem.2.2.2]
  · intro w hw
    apply (squarefreeRieszKernel_analytic_on_shifted_rectangle hz hz1 hδ4 hf ?_).continuousAt.continuousWithinAt
    have hn : ‖w‖ ≤ 3*δ/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    have hre := Complex.abs_re_le_norm w
    have him := Complex.abs_im_le_norm w
    have hr := abs_le.mp (hre.trans hn)
    have hi := abs_le.mp (him.trans hn)
    change (1-δ < (1+w).re ∧ (1+w).re < 2) ∧ (-(2*T) < (1+w).im ∧ (1+w).im < 2*T)
    simp only [add_re,one_re,add_im,one_im,zero_add]
    constructor <;> constructor <;> linarith [hr.1,hr.2,hi.1,hi.2]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszContourShift
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite contour shift for the actual normalized squarefree Perron integral -/
namespace JointDickman
open Complex Set MeasureTheory

theorem squarefreeRiesz_finite_contour_shift {z L δ c T : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    (hc : 0 < c) (hcδ : c ≤ δ/4) (hT : 1 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T))) (hf1 : f 1 = 0)
    (he : ∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = zetaPoleFactor s) :
    (1/(2*(Real.pi:ℂ)*I))*VIntegral (squarefreeNormalizedPerron z L) c (-T) T =
      (1/(2*(Real.pi:ℂ)*I)) *
        (VIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) (-T) T +
         HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) c T -
         HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) c (-T)) +
      (Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 (δ/4), (t^(-z):ℝ) • squarefreeRieszKernel z L f (-(t:ℂ))) := by
  obtain ⟨hrect,hlocal⟩ := squarefreeRieszKernel_contour_regular (L := L)
    hz hz1.le hδ hδ4 hc hcδ hT hf
  have hshift := fractionalContourShift hz hz1 (by linarith : 0 < δ/4) hc hcδ
    (by linarith : 0 < T) (by linarith : 2*(δ/4) < 3*δ/4) hrect hlocal
  have hright : VIntegral (squarefreeNormalizedPerron z L) c (-T) T =
      VIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) c (-T) T := by
    unfold VIntegral
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htt : -T ≤ t ∧ t ≤ T := by
      simpa only [uIcc_of_le (by linarith : -T ≤ T),mem_Icc] using ht
    apply squarefreeNormalizedPerron_eq_continuation hz hz1.le hδ (by linarith : 0 < 2*T) hf hf1 he
    change (1-0 < (1+((c:ℂ)+(t:ℂ)*I)).re ∧ (1+((c:ℂ)+(t:ℂ)*I)).re < 2) ∧
      (-(2*T) < (1+((c:ℂ)+(t:ℂ)*I)).im ∧ (1+((c:ℂ)+(t:ℂ)*I)).im < 2*T)
    simp only [sub_zero,add_re,add_im,one_re,one_im,ofReal_re,ofReal_im,mul_re,mul_im,
      I_re,I_im,mul_zero,mul_one,sub_zero,add_zero,zero_add]
    constructor <;> constructor <;> linarith [htt.1,htt.2]
  rw [←hright] at hshift
  simpa only [neg_div] using hshift

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszSingularFactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local analytic factor for the squarefree Riesz mean -/
namespace JointDickman
open Filter Finset Asymptotics
open scoped Topology

theorem squarefreeRieszSingularFactor_analyticAt_one {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticAt ℂ (squarefreeRieszSingularFactor z) 1 := by
  exact (squarefreeSingularFactor_analyticAt_one hz hz1).div
    (analyticAt_id.add analyticAt_const) (by norm_num)

theorem squarefreeRieszSingularFactor_one {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    squarefreeRieszSingularFactor z 1 =
      (squarefreeLeadingConstant z * Real.Gamma z / 2 : ℝ) := by
  rw [squarefreeRieszSingularFactor,squarefreeSingularFactor_one hz hz1]
  push_cast
  norm_num

theorem squarefreeRieszSingularFactor_taylor {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    ∃ a : ℕ → ℂ, a 0 = (squarefreeLeadingConstant z * Real.Gamma z / 2 : ℝ) ∧
      ∀ H : ℕ, (fun w : ℂ => squarefreeRieszSingularFactor z (1+w) -
        ∑ j ∈ range (H+1), a j*w^j) =O[𝓝 0] (fun w : ℂ => ‖w‖^(H+1)) := by
  obtain ⟨p,hp⟩ := squarefreeRieszSingularFactor_analyticAt_one hz.le hz1
  refine ⟨p.coeff,?_,?_⟩
  · exact (hp.coeff_zero (fun _ => 1)).trans (squarefreeRieszSingularFactor_one hz hz1)
  · intro H
    simpa only [FormalMultilinearSeries.partialSum,FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_eq_mul,mul_comm] using hp.isBigO_sub_partialSum_pow (H+1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszLaplaceExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local Laplace expansion for the squarefree Riesz mean -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem squarefreeRieszSingularFactor_laplace_expansion_below {z : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (r : ℝ) (hr : 0 < r) :
    ∃ a : ℕ → ℂ, a 0 = (squarefreeLeadingConstant z*Real.Gamma z / 2 : ℝ) ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧ η ≤ r ∧
        (fun L : ℝ => (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
          squarefreeRieszSingularFactor z (1-(t:ℂ))) -
          ∑ j ∈ range (H+1), (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) •
            (a j*(-1:ℂ)^j)) =O[atTop] (fun L => L^(z-H-2)) := by
  obtain ⟨a,ha,htaylor⟩ := squarefreeRieszSingularFactor_taylor hz hz1.le
  refine ⟨a,ha,fun H => ?_⟩
  obtain ⟨C,hC,hbound⟩ := (htaylor H).exists_pos
  obtain ⟨ε,hε,hεbound⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  obtain ⟨δ,hδ,hδbound⟩ := Metric.eventually_nhds_iff.mp
    (squarefreeRieszSingularFactor_analyticAt_one hz.le hz1.le).eventually_continuousAt
  let η := min (min ε δ) r / 2
  have hη : 0 < η := by dsimp [η] <;> positivity
  have hdist (t : ℝ) (ht : t ∈ Ioc 0 η) : t < min ε δ := by
    have hm : 0 < min ε δ := lt_min hε hδ
    dsimp [η] at ht
    linarith [ht.2, min_le_left (min ε δ) r]
  have hηr : η ≤ r := by
    dsimp [η]
    linarith [min_le_right (min ε δ) r]
  have hf : ContinuousOn (fun t : ℝ => squarefreeRieszSingularFactor z (1-(t:ℂ))) (Ioc 0 η) := by
    intro t ht
    have hd : dist (1-(t:ℂ)) 1 < δ := by
      rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
      exact (hdist t ht).trans_le (min_le_right _ _)
    have hK : ContinuousAt (squarefreeRieszSingularFactor z) (1-(t:ℂ)) := hδbound hd
    have hi : ContinuousAt (fun u : ℝ => (1:ℂ)-(u:ℂ)) t :=
      continuousAt_const.sub Complex.continuous_ofReal.continuousAt
    exact (ContinuousAt.comp (f := fun u : ℝ => (1:ℂ)-(u:ℂ)) hK hi).continuousWithinAt
  refine ⟨η,hη,hηr,laplace_taylor_isBigO hz1 hη hC.le _
    (hf.aestronglyMeasurable measurableSet_Ioc) (fun j => a j*(-1:ℂ)^j) H ?_⟩
  intro t ht
  have hd : dist (-(t:ℂ)) 0 < ε := by
    rw [dist_zero_right,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
    exact (hdist t ht).trans_le (min_le_left _ _)
  have hh := hεbound hd
  have hp : (∑ j ∈ range (H+1), a j*(-(t:ℂ))^j) =
      ∑ j ∈ range (H+1), (a j*(-1:ℂ)^j)*(t:ℂ)^j := by
    apply sum_congr rfl
    intro j _
    rw [neg_eq_neg_one_mul,mul_pow,mul_assoc]
  simpa only [hp,sub_eq_add_neg,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1,
    abs_of_nonneg (pow_nonneg ht.1.le _)] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeHankelExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal-Gamma coefficients of the local Hankel contribution -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem hankel_monomial_coefficient {z L : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (j : ℕ) (a : ℂ) :
    (Real.sin (Real.pi*z)/Real.pi) •
      ((L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • (a*(-1:ℂ)^j)) =
        (L^(z-j-1)) • (a/(Real.Gamma (z-j):ℂ)) := by
  have hs := Real.sin_sub_nat_mul_pi (Real.pi*z) j
  rw [show Real.pi*z-(j:ℝ)*Real.pi = Real.pi*(z-j) by ring] at hs
  have hc : Real.sin (Real.pi*z)/Real.pi *
      (Real.Gamma ((j:ℝ)+1-z)*(-1:ℝ)^j) = 1/Real.Gamma (z-j) := by
    rw [← gamma_reflection_coefficient hz hz1 j,hs]
    ring
  have hc' := congrArg (fun x : ℝ => (x:ℂ)) hc
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one] at hc'
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div]
  calc
    _ = (L^(z-j-1):ℝ) * a * ((Real.sin (Real.pi*z):ℂ)/(Real.pi:ℂ) *
        ((Real.Gamma ((j:ℝ)+1-z):ℂ)*(-1:ℂ)^j)) := by ring
    _ = _ := by rw [hc']; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszHankelExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Hankel coefficients for the squarefree Riesz mean -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem squarefreeRiesz_local_hankel_expansion_below {z : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℕ → ℂ, c 0 = ((squarefreeLeadingConstant z / 2:ℝ):ℂ) ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧ η ≤ r ∧
        (fun L : ℝ => (Real.sin (Real.pi*z)/Real.pi) •
          (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
            squarefreeRieszSingularFactor z (1-(t:ℂ))) -
          ∑ j ∈ range (H+1), L^(z-j-1) • c j)
          =O[atTop] (fun L => L^(z-H-2)) := by
  obtain ⟨a,ha,h⟩ := squarefreeRieszSingularFactor_laplace_expansion_below hz hz1 r hr
  refine ⟨fun j => a j/(Real.Gamma (z-j):ℂ),?_,fun H => ?_⟩
  · dsimp only
    rw [Nat.cast_zero,sub_zero,ha]
    have hG : (Real.Gamma z:ℂ) ≠ 0 := by exact_mod_cast (Real.Gamma_pos_of_pos hz).ne'
    push_cast
    field_simp
  · obtain ⟨η,hη,hηr,he⟩ := h H
    refine ⟨η,hη,hηr,?_⟩
    have hh := he.const_smul_left (Real.sin (Real.pi*z)/Real.pi)
    apply hh.congr_left
    intro L
    change (Real.sin (Real.pi*z)/Real.pi) •
      ((∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
        squarefreeRieszSingularFactor z (1-(t:ℂ))) -
        ∑ j ∈ range (H+1), (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • (a j*(-1:ℂ)^j)) = _
    rw [smul_sub,smul_sum]
    congr 1
    exact sum_congr rfl (fun j _ => hankel_monomial_coefficient hz hz1 j (a j))

theorem squarefreeRiesz_local_hankel_real_expansion_below {z : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (r : ℝ) (hr : 0 < r) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z / 2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ η : ℝ, 0 < η ∧ η ≤ r ∧
        (fun L : ℝ => squarefreeRieszLocalHankel z η L -
          ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  obtain ⟨c,hc,h⟩ := squarefreeRiesz_local_hankel_expansion_below hz hz1 r hr
  refine ⟨fun j => (c j).re,?_,?_,fun H => ?_⟩
  · dsimp only
    rw [hc,Complex.ofReal_re]
  · dsimp only
    rw [hc,Complex.ofReal_re]
    exact div_pos (squarefreeLeadingConstant_pos hz hz1.le) (by norm_num)
  · obtain ⟨η,hη,hηr,he⟩ := h H
    refine ⟨η,hη,hηr,?_⟩
    have hr : (fun L : ℝ => ((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
          squarefreeRieszSingularFactor z (1-(t:ℂ))) -
        ∑ j ∈ range (H+1), L^(z-j-1) • c j).re) =O[atTop]
          (fun L => L^(z-H-2)) := by
      apply IsBigO.trans _ he
      apply isBigO_of_le atTop
      intro L
      simpa only [Real.norm_eq_abs] using (Complex.abs_re_le_norm
        ((Real.sin (Real.pi*z)/Real.pi) •
          (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) •
            squarefreeRieszSingularFactor z (1-(t:ℂ))) -
          ∑ j ∈ range (H+1), L^(z-j-1) • c j))
    have hsum (L : ℝ) : (∑ j ∈ range (H+1), L^(z-j-1) • c j).re =
        ∑ j ∈ range (H+1), L^(z-j-1)*(c j).re := by
      change Complex.reCLM (∑ j ∈ range (H+1), L^(z-j-1) • c j) = _
      rw [map_sum]
      simp only [Complex.reCLM_apply,Complex.smul_re,smul_eq_mul]
    have hr' : (fun L : ℝ => squarefreeRieszLocalHankel z η L -
        ∑ j ∈ range (H+1), (c j).re*L^(z-1-j)) =O[atTop] (fun L => L^(z-H-2)) := by
      apply hr.congr_left
      intro L
      rw [Complex.sub_re,hsum]
      change squarefreeRieszLocalHankel z η L - _ = squarefreeRieszLocalHankel z η L - _
      congr 1
      apply sum_congr rfl
      intro j _
      rw [show z-j-1 = z-1-j by ring,mul_comm]
    simpa only [show z-H-2 = z-2-H by ring] using hr'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ZetaRectanglePrincipal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform local identification of normalized rectangle logarithms -/
namespace JointDickman
open Complex Set

theorem zeta_rectangle_principal_local : ∃ r : ℝ, 0 < r ∧
    ∀ {δ T : ℝ}, 0 < δ → 0 < T → ∀ {f : ℂ → ℂ},
      AnalyticOnNhd ℂ f (zetaOpenRectangle δ T) → f 1 = 0 →
      (∀ s ∈ zetaOpenRectangle δ T, exp (f s) = zetaPoleFactor s) →
      ∀ s ∈ Metric.ball (1:ℂ) r ∩ zetaOpenRectangle δ T,
        f s = log (zetaPoleFactor s) := by
  have hopen : IsOpen (zetaPoleFactor ⁻¹' slitPlane) :=
    isOpen_slitPlane.preimage zetaPoleFactor_differentiable.continuous
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
    (show (1:ℂ) ∈ zetaPoleFactor ⁻¹' slitPlane by
      simpa only [mem_preimage,zetaPoleFactor_one] using one_mem_slitPlane))
  refine ⟨r,hr,?_⟩
  intro δ T hδ hT f hf hf1 he s hs
  let U := Metric.ball (1:ℂ) r ∩ zetaOpenRectangle δ T
  have hU : IsOpen U := Metric.isOpen_ball.inter (zetaOpenRectangle_isOpen δ T)
  have hconv : Convex ℝ U := (convex_ball (1:ℂ) r).inter (zetaOpenRectangle_convex δ T)
  have h1 : (1:ℂ) ∈ U := ⟨Metric.mem_ball_self hr,zetaOpenRectangle_one hδ hT⟩
  have hg : AnalyticOnNhd ℂ (fun s => log (zetaPoleFactor s)) U := by
    intro s hs
    exact (zetaPoleFactor_differentiable.analyticAt s).clog (hsub hs.1)
  have hh := analytic_log_unique hU hconv.isPreconnected
    (hf.mono inter_subset_right) hg
    (fun s hs => (he s hs.2).trans (Complex.exp_log (slitPlane_ne_zero (hsub hs.1))).symm)
    h1 (by simp only [hf1,zetaPoleFactor_one,log_one])
  exact hh hs

theorem squarefreeRieszKernel_local_uniform : ∃ r : ℝ, 0 < r ∧
    ∀ {δ T : ℝ}, 0 < δ → 0 < T → ∀ {f : ℂ → ℂ},
      AnalyticOnNhd ℂ f (zetaOpenRectangle δ T) → f 1 = 0 →
      (∀ s ∈ zetaOpenRectangle δ T, exp (f s) = zetaPoleFactor s) →
      ∀ (z L : ℝ) (w : ℂ), 1+w ∈ Metric.ball (1:ℂ) r ∩ zetaOpenRectangle δ T →
        squarefreeRieszKernel z L f w =
          exp ((L:ℂ)*w)*squarefreeRieszSingularFactor z (1+w) := by
  obtain ⟨r,hr,hprincipal⟩ := zeta_rectangle_principal_local
  refine ⟨r,hr,?_⟩
  intro δ T hδ hT f hf hf1 he z L w hw
  have h := hprincipal hδ hT hf hf1 he (1+w) hw
  simp only [squarefreeRieszKernel,squarefreeRieszSingularFactor,squarefreeSingularFactor,h]
  have heq : (1:ℂ)+w+1 = 2+w := by ring
  rw [heq]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszCutIdentification
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the actual cut contribution with the local Riesz expansion -/
namespace JointDickman
open Complex MeasureTheory Set

theorem squarefreeRiesz_cut_identification : ∃ r : ℝ, 0 < r ∧
    ∀ {δ T : ℝ}, 0 < δ → 0 < T → δ/4 < r → ∀ {f : ℂ → ℂ},
      AnalyticOnNhd ℂ f (zetaOpenRectangle δ T) → f 1 = 0 →
      (∀ s ∈ zetaOpenRectangle δ T, exp (f s) = zetaPoleFactor s) →
      ∀ z L : ℝ,
        ((Real.sin (Real.pi*z)/Real.pi) •
          (∫ t : ℝ in Ioc 0 (δ/4), (t^(-z):ℝ) • squarefreeRieszKernel z L f (-(t:ℂ)))).re =
        squarefreeRieszLocalHankel z (δ/4) L := by
  obtain ⟨r,hr,hlocal⟩ := squarefreeRieszKernel_local_uniform
  refine ⟨r,hr,?_⟩
  intro δ T hδ hT hδr f hf hf1 he z L
  unfold squarefreeRieszLocalHankel
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have htδ : t < δ := by linarith [ht.2]
  have hs : 1+(-(t:ℂ)) ∈ Metric.ball (1:ℂ) r ∩ zetaOpenRectangle δ T := by
    constructor
    · rw [Metric.mem_ball,dist_eq_norm]
      have heq : (1:ℂ)+(-(t:ℂ))-1 = -(t:ℂ) := by ring
      rw [heq,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0]
      exact ht.2.trans_lt hδr
    · simp only [zetaOpenRectangle,mem_inter_iff,mem_preimage,add_re,one_re,neg_re,
        ofReal_re,add_im,one_im,neg_im,ofReal_im,neg_zero,add_zero]
      constructor <;> constructor <;> linarith
  rw [hlocal hδ hT hf hf1 he z L (-(t:ℂ)) hs]
  have hexp : exp ((L:ℂ)*(-(t:ℂ))) = (Real.exp (-(L*t)):ℂ) := by
    rw [show (L:ℂ)*(-(t:ℂ)) = (-(L*t):ℝ) by push_cast; ring,Complex.ofReal_exp]
  rw [hexp]
  simp only [Complex.real_smul,Complex.ofReal_mul,sub_eq_add_neg]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszContourError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the four contour errors with the local Riesz contribution -/
namespace JointDickman
open Complex MeasureTheory Set

theorem re_contour_error_le {P V J U D K a : ℂ} (he : V = a*(J+U-D)+K) :
    |P.re-K.re| ≤ ‖P-V‖ + ‖a‖*(‖J‖+‖U‖+‖D‖) := by
  have hid : P-K = (P-V)+a*(J+U-D) := by rw [he]; ring
  have hsum : ‖J+U-D‖ ≤ ‖J‖+‖U‖+‖D‖ := by
    linarith [norm_sub_le (J+U) D,norm_add_le J U]
  calc
    _ ≤ ‖P-K‖ := by simpa only [sub_re] using abs_re_le_norm (P-K)
    _ = ‖(P-V)+a*(J+U-D)‖ := by rw [hid]
    _ ≤ ‖P-V‖+‖a*(J+U-D)‖ := norm_add_le _ _
    _ ≤ ‖P-V‖+‖a‖*(‖J‖+‖U‖+‖D‖) := by
      rw [norm_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (norm_nonneg a))

theorem squarefreeRiesz_contour_error_le : ∃ r : ℝ, 0 < r ∧
    ∀ {z L δ c T : ℝ}, 0 ≤ z → z < 1 → 0 < δ → δ ≤ 1/4 → δ/4 < r →
      0 < c → c ≤ δ/4 → 1 < T →
      ∀ {f : ℂ → ℂ}, AnalyticOnNhd ℂ f (zetaOpenRectangle δ (2*T)) → f 1 = 0 →
      (∀ s ∈ zetaOpenRectangle δ (2*T), exp (f s) = zetaPoleFactor s) →
      |(VerticalIntegral' (squarefreeNormalizedPerron z L) c).re -
        squarefreeRieszLocalHankel z (δ/4) L| ≤
      ‖VerticalIntegral' (squarefreeNormalizedPerron z L) c -
        (1/(2*(Real.pi:ℂ)*I))*VIntegral (squarefreeNormalizedPerron z L) c (-T) T‖ +
      (1/(2*Real.pi)) *
        (‖VIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) (-T) T‖ +
         ‖HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) c T‖ +
         ‖HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ/4) c (-T)‖) := by
  obtain ⟨r,hr,hcut⟩ := squarefreeRiesz_cut_identification
  refine ⟨r,hr,?_⟩
  intro z L δ c T hz hz1 hδ hδ4 hδr hc hcδ hT f hf hf1 he
  have hs := squarefreeRiesz_finite_contour_shift (L := L) hz hz1 hδ hδ4 hc hcδ hT hf hf1 he
  have hb := re_contour_error_le (P := VerticalIntegral' (squarefreeNormalizedPerron z L) c) hs
  rw [hcut hδ (by linarith : 0 < 2*T) hδr hf hf1 he z L,perron_normalization_norm] at hb
  exact hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszHorizontalBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The horizontal errors in the squarefree Riesz contour -/
namespace JointDickman
open Complex Set

theorem squarefreeRieszKernel_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ A C : ℝ, A ∈ Ioc 0 (1/2) ∧ 0 < C ∧
      ∀ (L : ℝ) (f : ℂ → ℂ) (w : ℂ), 3 < |w.im| →
        3/4 ≤ (1+w).re → (1+w).re ≤ 2 →
        1-A/Real.log |w.im| ≤ (1+w).re →
        exp (f (1+w)) = zetaPoleFactor (1+w) →
        ‖fractionalContourIntegrand z (squarefreeRieszKernel z L f) w‖ ≤
          C*Real.exp (L*w.re)*|w.im|^(-3/2:ℝ) := by
  obtain ⟨A,C,hA,hC,hζ⟩ := zeta_fractional_power_high_bound
  obtain ⟨G,hG,hGb⟩ := squarefreeAnalyticFactor_uniform_bound hz hz1 (by norm_num : (1/2:ℝ) < 3/4)
  refine ⟨A,G*C,hA,mul_pos hG hC,?_⟩
  intro L f w ht hs hs2 hsA hf
  have ht0 : 0 < |w.im| := by linarith
  have hw : w ≠ 0 := by
    intro hw
    simp only [hw,zero_im,abs_zero] at ht
    linarith
  have heq : (((1+w).re:ℝ):ℂ)+(w.im:ℂ)*I = 1+w := by
    apply Complex.ext <;> simp
  have hb := hζ z (1+w).re w.im hz hz1 ht ⟨hsA,hs2⟩
  rw [heq] at hb
  have hd : |w.im|^2 ≤ ‖1+w‖*‖2+w‖ := by
    simpa only [add_im,one_im,zero_add,sq_abs,
      show (1:ℂ)+w+1 = 2+w by ring] using rieszDenominator_im_lower_bound (1+w)
  have hp : |w.im|^(1/2:ℝ)/|w.im|^2 = |w.im|^(-3/2:ℝ) := by
    rw [←Real.rpow_ofNat,←Real.rpow_sub ht0]
    norm_num
  rw [squarefreeRieszKernel_norm hw hf]
  calc
    _ ≤ (G*(C*|w.im|^(1/2:ℝ))*Real.exp (L*w.re))/|w.im|^2 := by
      apply div_le_div₀ (by positivity) _ (pow_pos ht0 2) hd
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hGb (1+w) hs) hb (Real.rpow_nonneg (norm_nonneg _) _) hG.le)
        (Real.exp_pos _).le
    _ = (G*C)*Real.exp (L*w.re)*(|w.im|^(1/2:ℝ)/|w.im|^2) := by ring
    _ = _ := by rw [hp]

theorem squarefreeRiesz_horizontal_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ A C : ℝ, A ∈ Ioc 0 (1/2) ∧ 0 < C ∧
      ∀ (δ c T L ε : ℝ) (f : ℂ → ℂ), 0 ≤ δ → δ ≤ 1/4 → 0 ≤ c → c ≤ 1 →
        3 < T → 0 ≤ L → δ ≤ A/Real.log T → |ε| = 1 →
        (∀ u ∈ Icc (-δ) c, exp (f (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I))) =
          zetaPoleFactor (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I))) →
        ‖HIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f))
          (-δ) c (ε*T)‖ ≤ C*Real.exp (L*c)*T^(-3/2:ℝ)*(δ+c) := by
  obtain ⟨A,C,hA,hC,hb⟩ := squarefreeRieszKernel_high_bound hz hz1
  refine ⟨A,C,hA,hC,?_⟩
  intro δ c T L ε f hδ hδ4 hc hc1 hT hL hδA hε hf
  have hT0 : 0 < T := by linarith
  have hac : -δ ≤ c := by linarith
  unfold HIntegral
  have hbound : ‖∫ u in -δ..c,
      fractionalContourIntegrand z (squarefreeRieszKernel z L f)
        ((u:ℂ)+((ε*T:ℝ):ℂ)*I)‖ ≤
      (C*Real.exp (L*c)*T^(-3/2:ℝ))*|c-(-δ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    have hu' : -δ ≤ u ∧ u ≤ c := by
      have hh : u ∈ Ioc (-δ) c := by simpa only [uIoc_of_le hac] using hu
      exact ⟨hh.1.le,hh.2⟩
    have hi : |(((u:ℂ)+((ε*T:ℝ):ℂ)*I)).im| = T := by
      simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,
        zero_add,add_zero,abs_mul,hε,one_mul,abs_of_pos hT0]
    have hr : (((u:ℂ)+((ε*T:ℝ):ℂ)*I)).re = u := by simp
    have hs : (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I)).re = 1+u := by simp
    have ht := hb L f ((u:ℂ)+((ε*T:ℝ):ℂ)*I)
      (by rwa [hi]) (by rw [hs]; linarith) (by rw [hs]; linarith)
      (by rw [hi,hs]; linarith) (hf u hu')
    rw [hi,hr] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu'.2 hL)) hC.le)
      (Real.rpow_nonneg hT0.le _))
  rw [abs_of_nonneg (by linarith : 0 ≤ c-(-δ))] at hbound
  simpa only [sub_neg_eq_add,add_comm c δ] using hbound

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszLeftBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The left vertical error in the squarefree Riesz contour -/
namespace JointDickman
open Complex Set MeasureTheory

theorem squarefreeRiesz_left_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ A C G : ℝ, A ∈ Ioc 0 (1/2) ∧ 0 < C ∧ 0 < G ∧
      ∀ (δ T L : ℝ) (f : ℂ → ℂ), 0 < δ → δ ≤ 1/4 → 4 ≤ T → δ ≤ A/Real.log T →
      (∀ t ∈ Icc (-T) T, exp (f (1+(((-δ:ℝ):ℂ)+(t:ℂ)*I))) =
        zetaPoleFactor (1+(((-δ:ℝ):ℂ)+(t:ℂ)*I))) →
      ‖VIntegral (fractionalContourIntegrand z (squarefreeRieszKernel z L f)) (-δ) (-T) T‖ ≤
        (5*G*(C/δ)^z*Real.exp (-(L*δ)))*Real.pi := by
  obtain ⟨A,C,hA,hC,hζ⟩ := zeta_left_contour_bound
  obtain ⟨G,hG,hGb⟩ := squarefreeAnalyticFactor_uniform_bound hz hz1 (by norm_num : (1/2:ℝ) < 3/4)
  refine ⟨A,C,G,hA,hC,hG,?_⟩
  intro δ T L f hδ hδ4 hT hδA hf
  apply verticalIntegral_bound_by_cauchy (by linarith : 0 ≤ T) (by positivity)
  intro t ht
  let w : ℂ := ((-δ:ℝ):ℂ)+(t:ℂ)*I
  have hw : w ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [w,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero,zero_re] at hr
    linarith
  have hsr : (3/4:ℝ) ≤ (1+w).re := by
    simp only [w,add_re,one_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,
      zero_mul,sub_zero,add_zero]
    linarith
  have hζw : ‖riemannZeta (1+w)‖ ≤ C/δ := by
    have htT : |t| ≤ T := abs_le.mpr ⟨ht.1.le,ht.2⟩
    have h := hζ δ T hδ hδ4 hT hδA t htT
    have heq : (1:ℂ)+w = ((1-δ:ℝ):ℂ)+(t:ℂ)*I := by
      simp only [w,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_neg]
      ring
    rw [heq]
    exact h
  have he := squarefreeRieszKernel_bound (L := L) hz hw (by linarith : (1/2:ℝ) ≤ (1+w).re)
    (hf t ⟨ht.1.le,ht.2⟩) (hGb (1+w) hsr) hζw
  simpa only [w,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
    sub_zero,add_zero,add_im,mul_im,mul_one,zero_add,mul_neg] using he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszLocalBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed bounded neighborhood for the local Riesz kernel -/
namespace JointDickman
open Set Filter
open scoped Topology

theorem squarefreeRieszSingularFactor_local_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ContinuousOn (fun t : ℝ => squarefreeRieszSingularFactor z (1-(t:ℂ))) (Icc 0 r) ∧
      ∀ t ∈ Icc 0 r, ‖squarefreeRieszSingularFactor z (1-(t:ℂ))‖ ≤ C := by
  obtain ⟨δ,hδ,hcont⟩ := Metric.eventually_nhds_iff.mp
    (squarefreeRieszSingularFactor_analyticAt_one hz hz1).eventually_continuousAt
  let r := δ/2
  have hr : 0 < r := by dsimp [r] <;> positivity
  have hf : ContinuousOn (fun t : ℝ => squarefreeRieszSingularFactor z (1-(t:ℂ))) (Icc 0 r) := by
    intro t ht
    have hd : dist (1-(t:ℂ)) 1 < δ := by
      rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
      dsimp [r] at ht
      linarith [ht.2]
    exact (ContinuousAt.comp (f := fun t : ℝ => (1:ℂ)-(t:ℂ)) (hcont hd)
      (continuousAt_const.sub Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact ⟨r,max C 0,hr,le_max_right _ _,hf,fun t ht => (hC t ht).trans (le_max_left _ _)⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszMovingHankel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The all-order local expansion with a shrinking contour cutoff -/
namespace JointDickman
open Set Filter MeasureTheory Asymptotics Finset
open scoped Topology

theorem squarefreeRiesz_moving_hankel_expansion {z a α : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (ha : 0 < a) (hα : 0 < α)
    {η : ℝ → ℝ} (hη : ∀ᶠ L in atTop, 0 ≤ η L)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hgrowth : ∀ᶠ L in atTop, a*L^α ≤ L*η L/2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z / 2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun L : ℝ => squarefreeRieszLocalHankel z (η L) L -
        ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  obtain ⟨r,C,hr,hC,hcont,hbound⟩ := squarefreeRieszSingularFactor_local_bound hz.le hz1.le
  obtain ⟨c,hc,hcpos,hexp⟩ := squarefreeRiesz_local_hankel_real_expansion_below hz hz1 r hr
  refine ⟨c,hc,hcpos,fun H => ?_⟩
  obtain ⟨r₀,hr₀,hr₀r,hfixed⟩ := hexp H
  have hsub : Ioc (0:ℝ) r₀ ⊆ Icc 0 r := fun _ ht => ⟨ht.1.le,ht.2.trans hr₀r⟩
  have hsmall : ∀ᶠ L in atTop, η L < r₀ := hηlim.eventually (gt_mem_nhds hr₀)
  have hmove := laplace_moving_local_isLittleO hz1 hC ha hα
    (fun t : ℝ => squarefreeRieszSingularFactor z (1-(t:ℂ)))
    ((hcont.mono hsub).aestronglyMeasurable measurableSet_Ioc)
    (fun t ht => hbound t (hsub ht))
    (hη.and (hsmall.mono fun _ h => h.le)) hgrowth (z-2-H)
  have hcplx := hmove.const_smul_left (Real.sin (Real.pi*z)/Real.pi)
  have hreal : (fun L : ℝ => squarefreeRieszLocalHankel z r₀ L -
      squarefreeRieszLocalHankel z (η L) L) =o[atTop] (fun L => L^(z-2-H)) := by
    apply IsBigO.trans_isLittleO _ hcplx
    apply isBigO_of_le atTop
    intro L
    change ‖((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 r₀, (t^(-z)*Real.exp (-(L*t))) •
          squarefreeRieszSingularFactor z (1-(t:ℂ)))).re -
      ((Real.sin (Real.pi*z)/Real.pi) •
        (∫ t : ℝ in Ioc 0 (η L), (t^(-z)*Real.exp (-(L*t))) •
          squarefreeRieszSingularFactor z (1-(t:ℂ)))).re‖ ≤ _
    rw [←Complex.sub_re,←smul_sub]
    exact Complex.abs_re_le_norm _
  apply (hfixed.sub hreal.isBigO).congr_left
  intro L
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszPerronLocal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local expansion at the concrete Perron cutoff -/
namespace JointDickman
open Filter Asymptotics Finset
open scoped Topology

theorem perronScaleWidth_tendsto_zero {A : ℝ} (hA : 0 < A) :
    Tendsto (perronScaleWidth A) atTop (𝓝 0) := by
  have hlim : Tendsto (fun q : ℝ => A/(4*q)) atTop (𝓝 0) := by
    simpa only [div_div,id_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => A/4) atTop (𝓝 (A/4))).div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall (fun q => (perronScaleWidth_pos hA (q := q)).le)) _ hlim
  filter_upwards [eventually_ge_atTop (2:ℝ)] with q hq
  exact perronScaleWidth_upper hA.le hq

theorem perronLogScaleWidth_tendsto_zero {A : ℝ} (hA : 0 < A) :
    Tendsto (perronLogScaleWidth A) atTop (𝓝 0) :=
  (perronScaleWidth_tendsto_zero hA).comp (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10))

theorem perronLogScaleWidth_growth {A : ℝ} (hA : 0 < A) :
    ∀ᶠ L in atTop, (A/4096)*L^(1/10:ℝ) ≤ L*perronLogScaleWidth A L/2 := by
  filter_upwards [eventually_ge_atTop (0:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10)).eventually (eventually_ge_atTop (2:ℝ))] with L hL hq
  have he : (L^(1/10:ℝ))^10 = L := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hL]
    norm_num
  have h := perronScaleWidth_mul_lower hA hq
  rw [he] at h
  change (A/4096)*L^(1/10:ℝ) ≤ L*perronScaleWidth A (L^(1/10:ℝ))/2
  linarith

theorem squarefreeRiesz_perron_local_expansion {z A : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (hA : 0 < A) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z / 2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun L : ℝ => squarefreeRieszLocalHankel z (perronLogScaleWidth A L) L -
        ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  exact squarefreeRiesz_moving_hankel_expansion hz hz1
    (div_pos hA (by norm_num)) (by norm_num : (0:ℝ) < 1/10)
    (Eventually.of_forall (fun L => (perronScaleWidth_pos hA (q := L^(1/10:ℝ))).le))
    (perronLogScaleWidth_tendsto_zero hA) (perronLogScaleWidth_growth hA)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszScaleError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A quantitative global error at the chosen Perron scale -/
namespace JointDickman
open Complex Filter Set
open scoped Topology

theorem squarefreeRiesz_scale_error {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∃ A C D : ℝ, 0 < A ∧ 0 < C ∧ 0 < D ∧
      ∀ᶠ q : ℝ in atTop,
        |(VerticalIntegral' (squarefreeNormalizedPerron z (q^10)) (1/q^10)).re -
          squarefreeRieszLocalHankel z (perronScaleWidth A q) (q^10)| ≤
        C*((D/perronScaleWidth A q)^z*Real.exp (-(q^10*perronScaleWidth A q)) +
          (Real.exp q/2)^(-1/2:ℝ)) := by
  obtain ⟨A₀,hA₀,hA₀4,hlog⟩ := zeta_rectangle_log_below
  obtain ⟨A₁,D,G,hA₁,hD,hG,hleft⟩ := squarefreeRiesz_left_bound hz hz1.le
  obtain ⟨A₂,E,hA₂,hE,hhor⟩ := squarefreeRiesz_horizontal_bound hz hz1.le
  obtain ⟨F,hF,htail⟩ := squarefreeNormalizedPerron_truncation_bound hz hz1.le
  obtain ⟨r,hr,herror⟩ := squarefreeRiesz_contour_error_le
  let A := min A₀ (min A₁ A₂)
  have hA : 0 < A := lt_min hA₀ (lt_min hA₁.1 hA₂.1)
  have hAA₀ : A ≤ A₀ := min_le_left _ _
  have hAA₁ : A ≤ A₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hAA₂ : A ≤ A₂ := (min_le_right _ _).trans (min_le_right _ _)
  let C := F*Real.exp 1 + (1/(2*Real.pi))*(5*G*Real.pi+2*E*Real.exp 1)
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨A,C,D,hA,hC,hD,?_⟩
  filter_upwards [eventually_ge_atTop (max 8 (2048/A)),
    (perronScaleWidth_tendsto_zero hA).eventually (gt_mem_nhds hr)] with q hq hqr
  have hq8 : 8 ≤ q := (le_max_left _ _).trans hq
  have hqA : 2048/A ≤ q := (le_max_right _ _).trans hq
  have hq0 : 0 < q := by linarith
  let η := perronScaleWidth A q
  let c : ℝ := 1/q^10
  let T := Real.exp q/2
  have hη : 0 < η := perronScaleWidth_pos hA
  have hη4 : 4*η ≤ 1/4 := (perronScaleWidth_four_le hA (by linarith)).trans (hAA₀.trans hA₀4)
  have hη1 : η ≤ 1/4 := by linarith
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hcη : c ≤ η := perronScale_right_le_width hA (by linarith) hqA
  have hc1 : c ≤ 1 := by linarith
  have hT : 3 < T := perronScale_height_gt_three hq8
  have hT4 : 4 ≤ T := by dsimp [T] <;> linarith [Real.add_one_le_exp q]
  have hL : 0 ≤ q^10 := pow_nonneg hq0.le _
  have hLc : q^10*c = 1 := by dsimp [c]; field_simp
  have hηlog := perronScaleWidth_le_log_height hA hq8
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hηA₁ : η ≤ A₁/Real.log T := hηlog.trans (div_le_div_of_nonneg_right hAA₁ hlogT.le)
  have hηA₂ : η ≤ A₂/Real.log T := hηlog.trans (div_le_div_of_nonneg_right hAA₂ hlogT.le)
  obtain ⟨f,hf,hf1,he⟩ := hlog A hA hAA₀ (Real.exp q) (Real.exp_pos q)
  have hrect : zetaOpenRectangle (4*η) (2*T) =
      zetaOpenRectangle (zetaContourWidth A (Real.exp q)) (Real.exp q) := by
    dsimp [η,T,perronScaleWidth]
    congr 1 <;> ring
  rw [←hrect] at hf he
  have hbranch (u t : ℝ) (hu : u ∈ Icc (-η) c) (ht : |t| ≤ T) :
      exp (f (1+((u:ℂ)+(t:ℂ)*I))) = zetaPoleFactor (1+((u:ℂ)+(t:ℂ)*I)) := by
    apply he
    apply perron_inner_contour_mem hη hη1 hcη (by linarith : 0 < T)
    · simpa using hu
    · simpa using ht
  have hl := hleft η T (q^10) f hη hη1 hT4 hηA₁
    (fun t ht => hbranch (-η) t ⟨le_rfl,by linarith⟩ (abs_le.mpr ht))
  have hhor' (ε : ℝ) (hε : |ε| = 1) :=
    hhor η c T (q^10) ε f hη.le hη1 hc.le hc1 hT hL hηA₂ hε
      (fun u hu => hbranch u (ε*T) hu (by rw [abs_mul,hε,abs_of_pos (by linarith : 0 < T),one_mul]))
  have hhPos := hhor' 1 (by norm_num)
  have hhNeg := hhor' (-1) (by norm_num)
  simp only [one_mul,neg_one_mul] at hhPos hhNeg
  have ht := htail (q^10) c T hc hc1 hT
  have he' := herror (L := q^10) hz hz1 (by linarith : 0 < 4*η) hη4
    (by simpa using hqr) hc (by simpa using hcη) (by linarith : 1 < T) hf hf1 he
  simp only [show 4*η/4 = η by ring,show -(4*η)/4 = -η by ring] at he'
  change |(VerticalIntegral' (squarefreeNormalizedPerron z (q^10)) c).re -
    squarefreeRieszLocalHankel z η (q^10)| ≤ _
  have hhalf : T^(-3/2:ℝ) ≤ T^(-1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlen : η+c ≤ 1 := by linarith
  have hhorbound : E*Real.exp (q^10*c)*T^(-3/2:ℝ)*(η+c) ≤
      E*Real.exp 1*T^(-1/2:ℝ) := by
    rw [hLc]
    calc
      _ ≤ E*Real.exp 1*T^(-3/2:ℝ)*1 :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ E*Real.exp 1)
  rw [hLc] at ht
  calc
    _ ≤ F*Real.exp 1*T^(-1/2:ℝ) + (1/(2*Real.pi)) *
        ((5*G*(D/η)^z*Real.exp (-(q^10*η)))*Real.pi +
          E*Real.exp 1*T^(-1/2:ℝ)+E*Real.exp 1*T^(-1/2:ℝ)) := by
      exact he'.trans (add_le_add ht (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hl (hhPos.trans hhorbound)) (hhNeg.trans hhorbound)) (by positivity)))
    _ ≤ C*((D/η)^z*Real.exp (-(q^10*η)) + T^(-1/2:ℝ)) := by
      dsimp [C]
      have hp : 0 ≤ (D/η)^z*Real.exp (-(q^10*η)) := by positivity
      have htpos : 0 ≤ T^(-1/2:ℝ) := by positivity
      have hcross₁ : 0 ≤ F*Real.exp 1*((D/η)^z*Real.exp (-(q^10*η))) := by positivity
      have hcross₂ : 0 ≤ (1/(2*Real.pi))*(5*G*Real.pi)*T^(-1/2:ℝ) := by positivity
      have hcross₃ : 0 ≤ (1/(2*Real.pi))*(2*E*Real.exp 1)*((D/η)^z*Real.exp (-(q^10*η))) := by positivity
      nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszGlobalDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global errors smaller than every fixed logarithmic power -/
namespace JointDickman
open Complex Filter Asymptotics
open scoped Topology

theorem squarefreeRiesz_scale_decay {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ b : ℝ,
      (fun q : ℝ => (VerticalIntegral' (squarefreeNormalizedPerron z (q^10)) (1/q^10)).re -
        squarefreeRieszLocalHankel z (perronScaleWidth A q) (q^10)) =o[atTop]
      (fun q => q^b) := by
  obtain ⟨A,C,D,hA,_,hD,hbound⟩ := squarefreeRiesz_scale_error hz hz1
  refine ⟨A,hA,fun b => ?_⟩
  have hg : (fun q : ℝ => (VerticalIntegral' (squarefreeNormalizedPerron z (q^10)) (1/q^10)).re -
      squarefreeRieszLocalHankel z (perronScaleWidth A q) (q^10)) =O[atTop]
      (fun q => (D/perronScaleWidth A q)^z*Real.exp (-(q^10*perronScaleWidth A q)) +
        (Real.exp q/2)^(-1/2:ℝ)) := by
    apply IsBigO.of_bound C
    filter_upwards [hbound] with q hq
    have hη := perronScaleWidth_pos hA (q := q)
    have hp : 0 ≤ (D/perronScaleWidth A q)^z*Real.exp (-(q^10*perronScaleWidth A q)) +
        (Real.exp q/2)^(-1/2:ℝ) := by positivity
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hp]
    exact hq
  exact hg.trans_isLittleO
    ((perronScale_left_scalar_decay hz hz1.le hD.le hA b).add (perronScale_tail_scalar_decay b))

theorem squarefreeRiesz_global_decay {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ b : ℝ,
      (fun L : ℝ => (VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re -
        squarefreeRieszLocalHankel z (perronLogScaleWidth A L) L) =o[atTop]
      (fun L => L^b) := by
  obtain ⟨A,hA,hdecay⟩ := squarefreeRiesz_scale_decay hz hz1
  refine ⟨A,hA,fun b => ?_⟩
  have h := (hdecay (10*b)).comp_tendsto
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10))
  apply h.congr'
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    have he : (L^(1/10:ℝ))^10 = L := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hL]
      norm_num
    simp only [Function.comp_apply]
    rw [he]
    rfl
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    simp only [Function.comp_apply]
    rw [←Real.rpow_mul hL]
    congr 1
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_SquarefreeRieszPerronExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full normalized Perron integral has the local all-order expansion -/
namespace JointDickman
open Complex Filter Asymptotics Finset
open scoped Topology

theorem squarefreeRiesz_perron_expansion_jd_oai {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z/2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun L : ℝ =>
        (VerticalIntegral' (squarefreeNormalizedPerron z L) (1/L)).re -
        ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  obtain ⟨A,hA,hglobal⟩ := squarefreeRiesz_global_decay hz.le hz1
  obtain ⟨c,hc,hc0,hlocal⟩ := squarefreeRiesz_perron_local_expansion hz hz1 hA
  refine ⟨c,hc,hc0,fun H => ?_⟩
  have h := ((hglobal (z-2-H)).isBigO).add (hlocal H)
  apply h.congr_left
  intro L
  ring

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.squarefreeRiesz_perron_expansion_jd_oai := @OAI.JointDickman.squarefreeRiesz_perron_expansion_jd_oai
