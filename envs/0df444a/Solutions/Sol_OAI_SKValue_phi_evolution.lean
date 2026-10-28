-- Prove2me | solution 1 for OAI.SKValue.phi_evolution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:03:55.203813+00:00
-- url     : https://prove2.me/submissions/3d333f51-7bf0-4973-addc-ef9062f2f2d0

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_smoothApprox_tendsto

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_Cutoff
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma OrderParameter.cutoff_measurable (γ : OrderParameter) : Measurable γ.cutoff := by
  apply measurable_of_restrict_of_restrict_compl (s := Ico (0 : ℝ) 1) measurableSet_Ico
  · have hm : Monotone (fun t : Ico (0 : ℝ) 1 ↦ γ.coeff t) :=
      fun x y hxy ↦ γ.monotone x.property y.property hxy
    change Measurable (fun t : Ico (0 : ℝ) 1 ↦ γ.cutoff t)
    convert hm.measurable using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    exact Set.indicator_of_mem t.property γ.coeff
  · have he : ((Ico (0 : ℝ) 1)ᶜ).domRestrict γ.cutoff = fun _ ↦ (0 : ℝ) := by
      funext t
      exact Set.indicator_of_notMem t.property γ.coeff
    rw [he]
    exact measurable_const

lemma OrderParameter.cutoff_nonneg (γ : OrderParameter) (t : ℝ) : 0≤γ.cutoff t := by
  by_cases ht : t∈Ico (0 : ℝ) 1
  · simpa only [OrderParameter.cutoff, Set.indicator_of_mem ht] using γ.nonneg t ht
  · simp only [OrderParameter.cutoff, Set.indicator_of_notMem ht, le_refl]

lemma OrderParameter.cutoff_integrable (γ : OrderParameter) : Integrable γ.cutoff := by
  apply (integrable_indicator_iff measurableSet_Ico).mpr
  have hi : IntegrableOn γ.coeff (Icc (0 : ℝ) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr γ.integrable
  exact hi.mono_set Ico_subset_Icc_self

lemma Admissible.limited_measurable {W : BrownianSpace} {t : ℝ}
    {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    Measurable (fun p : ℝ×W.Ω ↦ limitedControl α p.1 p.2) := by
  have hj : Measurable (fun p : Iic (1 : ℝ≥0) × W.Ω ↦ α p.1 p.2) := by
    apply (hα.1 1).comp
    exact measurable_fst.prodMk (measurable_snd.mono le_rfl ((shiftedFiltration W t).le 1))
  exact hj.comp (((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk (h := fun p ↦ Set.mem_Iic.mpr (min_le_right _ _) ) |>.prodMk measurable_snd)

lemma limitedControl_eq {W : BrownianSpace} (α : ℝ≥0 → W.Ω → ℝ) {s : ℝ}
    (hs : s≤1) (ω : W.Ω) : limitedControl α s ω=α (Real.toNNReal s) ω := by
  have hs' : Real.toNNReal s≤(1 : ℝ≥0) := Real.toNNReal_le_iff_le_coe.mpr hs
  simp only [limitedControl, min_eq_left hs']

lemma Admissible.limited_bound {W : BrownianSpace} {t : ℝ} {α : ℝ≥0 → W.Ω → ℝ}
    (hα : Admissible W t α) (s : ℝ) (ω : W.Ω) : |limitedControl α s ω|≤1 := hα.2 _ _

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlIntegral
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma controlIntegral_eq (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (α : ℝ≥0 → W.Ω → ℝ) (n : ℕ) (ω : W.Ω) :
    controlIntegral γ t α n ω =
      ∫ s in (0 : ℝ)..(1-t), γ.coeff (t+s)*(α (Real.toNNReal s) ω)^n := by
  unfold controlIntegral
  apply intervalIntegral.integral_congr_Ioo_of_le (sub_nonneg.mpr ht.2)
  intro s hs
  have hts : t+s∈Ico (0 : ℝ) 1 := ⟨by linarith [hs.1,ht.1],by linarith [hs.2]⟩
  change γ.cutoff (t+s) * (limitedControl α s ω)^n = γ.coeff (t+s) * (α (Real.toNNReal s) ω)^n
  unfold OrderParameter.cutoff
  rw [Set.indicator_of_mem hts, limitedControl_eq α (by linarith [hs.2,ht.1]) ω]

lemma controlIntegral_measurable {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) (n : ℕ) :
    Measurable (controlIntegral γ t α n) := by
  have hm : Measurable (fun p : ℝ×W.Ω ↦ γ.cutoff (t+p.1)*(limitedControl α p.1 p.2)^n) :=
    (γ.cutoff_measurable.comp (measurable_const.add measurable_fst)).mul (hα.limited_measurable.pow_const n)
  unfold controlIntegral intervalIntegral
  exact (hm.stronglyMeasurable.integral_prod_left.measurable).sub
    (hm.stronglyMeasurable.integral_prod_left.measurable)

lemma controlIntegral_integrand_bound {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) (n : ℕ) (s : ℝ) (ω : W.Ω) :
    |γ.cutoff (t+s)*(limitedControl α s ω)^n|≤γ.cutoff (t+s) := by
  rw [abs_mul, abs_of_nonneg (γ.cutoff_nonneg _), abs_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hα.limited_bound s ω)) (γ.cutoff_nonneg _)).trans_eq (mul_one _)

lemma controlIntegral_bound {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α)
    (n : ℕ) (ω : W.Ω) :
    |controlIntegral γ t α n ω|≤∫ s in t..1, γ.cutoff s := by
  have hi : IntervalIntegrable (fun s ↦ γ.cutoff (t+s)) volume 0 (1-t) := by
    simpa only [sub_self] using (γ.cutoff_integrable.intervalIntegrable (a := t) (b := 1)).comp_add_left t
  have hh := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun s ↦ γ.cutoff (t+s)*(limitedControl α s ω)^n) (sub_nonneg.mpr ht.2)
    (Eventually.of_forall (fun s _ ↦ by simpa only [Real.norm_eq_abs] using controlIntegral_integrand_bound γ hα n s ω)) hi
  simpa [Real.norm_eq_abs, controlIntegral, intervalIntegral.integral_comp_add_left] using hh

lemma controlIntegral_integrable {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) (n : ℕ) :
    Integrable (controlIntegral γ t α n) W.μ := by
  apply Integrable.of_bound (controlIntegral_measurable γ hα n).aestronglyMeasurable (∫ s in t..1, γ.cutoff s)
  exact Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using controlIntegral_bound γ ht hα n ω)

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma controlIntegrand_intervalIntegrable {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) (n : ℕ) (ω : W.Ω) :
    IntervalIntegrable (fun s ↦ γ.cutoff (t+s)*(limitedControl α s ω)^n) volume 0 (1-t) := by
  have hi : IntervalIntegrable (fun s ↦ γ.cutoff (t+s)) volume 0 (1-t) := by
    have hg := (γ.cutoff_integrable.intervalIntegrable (a := t) (b := 1)).comp_add_left t
    simpa only [sub_self] using hg
  apply hi.mono_fun'
  · exact ((γ.cutoff_measurable.comp (measurable_const.add measurable_id)).mul
      ((hα.limited_measurable.comp (measurable_id.prodMk measurable_const)).pow_const n)).aestronglyMeasurable
  · exact Eventually.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using controlIntegral_integrand_bound γ hα n s ω)

lemma control_cost_bound {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) (ω : W.Ω) :
    |controlIntegral γ t α 1 ω|-(1/2 : ℝ)*controlIntegral γ t α 2 ω≤
      (1/2 : ℝ)*∫ s in t..1, γ.cutoff s := by
  have h1 := controlIntegrand_intervalIntegrable γ hα 1 ω
  have h2 := controlIntegrand_intervalIntegrable γ hα 2 ω
  have hγ : IntervalIntegrable (fun s ↦ γ.cutoff (t+s)) volume 0 (1-t) := by
    simpa only [sub_self] using (γ.cutoff_integrable.intervalIntegrable (a := t) (b := 1)).comp_add_left t
  have hpoint (s : ℝ) : |γ.cutoff (t+s)*(limitedControl α s ω)^1|-
      (1/2 : ℝ)*(γ.cutoff (t+s)*(limitedControl α s ω)^2)≤(1/2 : ℝ)*γ.cutoff (t+s) := by
    rw [pow_one, abs_mul, abs_of_nonneg (γ.cutoff_nonneg _)]
    have hscalar : |limitedControl α s ω|-(1/2 : ℝ)*(limitedControl α s ω)^2≤1/2 := by
      nlinarith [sq_nonneg (|limitedControl α s ω|-1),sq_abs (limitedControl α s ω)]
    nlinarith [mul_le_mul_of_nonneg_left hscalar (γ.cutoff_nonneg (t+s))]
  calc
    _ ≤ (∫ s in (0 : ℝ)..(1-t), |γ.cutoff (t+s)*(limitedControl α s ω)^1|)-
        (1/2 : ℝ)*(∫ s in (0 : ℝ)..(1-t), γ.cutoff (t+s)*(limitedControl α s ω)^2) :=
      sub_le_sub_right (intervalIntegral.abs_integral_le_integral_abs (sub_nonneg.mpr ht.2)) _
    _ = ∫ s in (0 : ℝ)..(1-t), |γ.cutoff (t+s)*(limitedControl α s ω)^1|-
        (1/2 : ℝ)*(γ.cutoff (t+s)*(limitedControl α s ω)^2) := by
      rw [intervalIntegral.integral_sub h1.abs (h2.const_mul _), intervalIntegral.integral_const_mul]
    _ ≤ ∫ s in (0 : ℝ)..(1-t), (1/2 : ℝ)*γ.cutoff (t+s) :=
      intervalIntegral.integral_mono (sub_nonneg.mpr ht.2)
        (h1.abs.sub (h2.const_mul _)) (hγ.const_mul _) hpoint
    _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_left]; simp

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_StripIntegralLimit
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology
namespace SKValue

lemma strip_integral_limit {T a b Γ A B : ℝ}
    {c : ℕ → ℝ → ℝ} {γ : ℝ → ℝ} {f g : ℕ → ℝ → ℝ} {F G : ℝ → ℝ}
    (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T)
    (hc : ∀ n, Measurable (c n))
    (hf : ∀ n, ContinuousOn (f n) (Icc (0 : ℝ) T))
    (hg : ∀ n, ContinuousOn (g n) (Icc (0 : ℝ) T))
    (hcb : ∀ n t, t∈Icc (0 : ℝ) T → |c n t| ≤ Γ)
    (hfb : ∀ n t, t∈Icc (0 : ℝ) T → |f n t| ≤ A)
    (hgb : ∀ n t, t∈Icc (0 : ℝ) T → |g n t| ≤ B)
    (hΓ : 0 ≤ Γ)
    (hlc : ∀ᵐ t ∂volume, t∈Icc (0 : ℝ) T → Tendsto (fun n ↦ c n t) atTop (𝓝 (γ t)))
    (hlf : ∀ t∈Icc (0 : ℝ) T, Tendsto (fun n ↦ f n t) atTop (𝓝 (F t)))
    (hlg : ∀ t∈Icc (0 : ℝ) T, Tendsto (fun n ↦ g n t) atTop (𝓝 (G t))) :
    Tendsto (fun n ↦ ∫ t in a..b, f n t+c n t*g n t) atTop
      (𝓝 (∫ t in a..b, F t+γ t*G t)) := by
  have hsub : uIoc a b⊆Icc (0 : ℝ) T := uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ A+Γ*B)
  · apply Eventually.of_forall
    intro n
    exact ((hf n).aestronglyMeasurable measurableSet_Icc |>.mono_set hsub).add
      ((hc n).aestronglyMeasurable.mul ((hg n).aestronglyMeasurable measurableSet_Icc |>.mono_set hsub))
  · apply Eventually.of_forall
    intro n
    apply Eventually.of_forall
    intro t ht
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add (hfb n t (hsub ht)) (by
      rw [abs_mul]
      exact mul_le_mul (hcb n t (hsub ht)) (hgb n t (hsub ht)) (abs_nonneg _) hΓ))
  · exact intervalIntegrable_const
  · filter_upwards [hlc] with t hlt ht
    exact (hlf t (hsub ht)).add ((hlt (hsub ht)).mul (hlg t (hsub ht)))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_DerivativeLimit
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue

lemma second_order_remainder {f : ℝ → ℝ} {C : ℝ} (hf : ContDiff ℝ 2 f) (hC : 0 ≤ C)
    (hb : ∀ x, |deriv (deriv f) x| ≤ C) (x d : ℝ) :
    |f (x+d)-f x-deriv f x*d| ≤ (C/2)*d^2 := by
  by_cases hd : d=0
  · rw [hd, add_zero, mul_zero, sub_self, sub_zero, abs_zero]
    exact mul_nonneg (div_nonneg hC (by norm_num)) (sq_nonneg 0)
  have hne : x≠x+d := by intro hx; apply hd; linarith
  have h1 : iteratedDerivWithin 1 f (uIcc x (x+d)) x=deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hf.of_le (by norm_num)).contDiffAt left_mem_uIcc,iteratedDeriv_one]
  have ht : taylorWithinEval f 1 (uIcc x (x+d)) x (x+d)=f x+deriv f x*d := by
    rw [taylorWithinEval_succ,taylor_within_zero_eval,h1]
    norm_num
    ring
  obtain ⟨y,_,hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hf.contDiffOn
  rw [ht] at hy
  have he : f (x+d)-f x-deriv f x*d=deriv (deriv f) y*d^2/2 := by
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,
      mul_one,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] at hy
    convert hy using 1 <;> ring
  rw [he,abs_div,abs_mul,abs_of_nonneg (sq_nonneg d)]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_right (hb y) (sq_nonneg d)]

lemma derivative_difference_of_values {f g : ℝ → ℝ} {C ε d : ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hC : 0 ≤ C) (hd : 0<d)
    (hfb : ∀ x, |deriv (deriv f) x| ≤ C) (hgb : ∀ x, |deriv (deriv g) x| ≤ C)
    (he : ∀ x, |f x-g x|<ε) (x : ℝ) :
    |deriv f x-deriv g x| * d < 2*ε+C*d^2 := by
  have hf' := second_order_remainder hf hC hfb x d
  have hg' := second_order_remainder hg hC hgb x d
  have hid : (deriv f x-deriv g x)*d=
      (f (x+d)-g (x+d))-(f x-g x)-
        (f (x+d)-f x-deriv f x*d)+(g (x+d)-g x-deriv g x*d) := by ring
  have hmul : |deriv f x-deriv g x| * d = |(deriv f x-deriv g x)*d| := by rw [abs_mul,abs_of_pos hd]
  rw [hmul,hid]
  have hp := abs_sub (f (x+d)-g (x+d)) (f x-g x)
  have hq := abs_sub ((f (x+d)-g (x+d))-(f x-g x)) (f (x+d)-f x-deriv f x*d)
  have hb := abs_add_le ((f (x+d)-g (x+d))-(f x-g x)-(f (x+d)-f x-deriv f x*d))
    (g (x+d)-g x-deriv g x*d)
  have h1 := he (x+d)
  have h2 := he x
  nlinarith

lemma uniform_derivative_limit {A : Type*} {F : ℕ → A → ℝ → ℝ} {f : A → ℝ → ℝ} {C : ℝ}
    (hF : TendstoUniformly (fun n (p : A×ℝ) ↦ F n p.1 p.2) (fun p ↦ f p.1 p.2) atTop)
    (hs : ∀ n a, ContDiff ℝ 2 (F n a)) (hC : 0 ≤ C)
    (hb : ∀ n a x, |deriv (deriv (F n a)) x| ≤ C) :
    TendstoUniformly (fun n (p : A×ℝ) ↦ deriv (F n p.1) p.2)
      (fun p ↦ deriv (f p.1) p.2) atTop ∧ ∀ a, Differentiable ℝ (f a) := by
  have hc : UniformCauchySeqOn (fun n (p : A×ℝ) ↦ deriv (F n p.1) p.2) atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let d := ε/(2*(C+1))
    have hd : 0<d := by dsimp [d]; positivity
    have hdC : C*d<ε/2 := by
      dsimp [d]
      have hn : 0<2*(C+1) := by positivity
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hn).mpr
      nlinarith
    have hcF := (hF.tendstoUniformlyOn (s := univ)).uniformCauchySeqOn
    obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp hcF (ε*d/4) (by positivity)
    refine ⟨N,?_⟩
    intro m hm n hn p hp
    have he : ∀ x, |F m p.1 x-F n p.1 x|<ε*d/4 := by
      intro x
      simpa only [Real.dist_eq] using hN m hm n hn (p.1,x) (mem_univ _)
    have hv := derivative_difference_of_values (hs m p.1) (hs n p.1) hC hd
      (hb m p.1) (hb n p.1) he p.2
    rw [Real.dist_eq]
    have hh : |deriv (F m p.1) p.2-deriv (F n p.1) p.2| * d<ε*d := by
      nlinarith [mul_lt_mul_of_pos_right hdC hd]
    nlinarith
  have hex (p : A×ℝ) : ∃ g : ℝ, Tendsto (fun n ↦ deriv (F n p.1) p.2) atTop (𝓝 g) :=
    cauchySeq_tendsto_of_complete (hc.cauchySeq (mem_univ p))
  choose g hg using hex
  have hG : TendstoUniformly (fun n (p : A×ℝ) ↦ deriv (F n p.1) p.2) g atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hc.tendstoUniformlyOn_of_tendsto (fun p _ ↦ hg p)
  have hgder (a : A) (x : ℝ) : HasDerivAt (f a) (g (a,x)) x := by
    apply hasDerivAt_of_tendstoUniformly (hG.comp (fun z ↦ (a,z)))
    · exact Eventually.of_forall (fun n y ↦ ((hs n a).differentiable (by norm_num) y).hasDerivAt)
    · intro y
      exact hF.tendsto_at (a,y)
  have heq : g=(fun p ↦ deriv (f p.1) p.2) := by
    funext p
    exact (hgder p.1 p.2).deriv.symm
  exact ⟨heq ▸ hG,fun a x ↦ (hgder a x).differentiableAt⟩

lemma contDiff_infty_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ k hk =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp hk).2

lemma uniform_all_derivative_limits {A : Type*} {F : ℕ → A → ℝ → ℝ} {f : A → ℝ → ℝ}
    (hF : TendstoUniformly (fun n (p : A×ℝ) ↦ F n p.1 p.2) (fun p ↦ f p.1 p.2) atTop)
    (hs : ∀ n a, ContDiff ℝ ∞ (F n a))
    (hb : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ n a x, |iteratedDeriv (k+1) (F n a) x| ≤ C) :
    (∀ k, TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv k (F n p.1) p.2)
      (fun p ↦ iteratedDeriv k (f p.1) p.2) atTop) ∧ ∀ a, ContDiff ℝ ∞ (f a) := by
  have step (k : ℕ)
      (hk : TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv k (F n p.1) p.2)
        (fun p ↦ iteratedDeriv k (f p.1) p.2) atTop) :
      TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv (k+1) (F n p.1) p.2)
        (fun p ↦ iteratedDeriv (k+1) (f p.1) p.2) atTop ∧
        ∀ a, Differentiable ℝ (iteratedDeriv k (f a)) := by
    obtain ⟨C,hC,hbc⟩ := hb (k+1)
    have hh := uniform_derivative_limit (F := fun n a ↦ iteratedDeriv k (F n a))
      (f := fun a ↦ iteratedDeriv k (f a)) hk
      (fun n a ↦ (contDiff_infty_iteratedDeriv (hs n a) k).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hC (fun n a x ↦ by
          simpa only [iteratedDeriv_succ] using hbc n a x)
    simpa only [iteratedDeriv_succ] using hh
  have hc : ∀ k, TendstoUniformly (fun n (p : A×ℝ) ↦ iteratedDeriv k (F n p.1) p.2)
      (fun p ↦ iteratedDeriv k (f p.1) p.2) atTop := by
    intro k
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hF
    | succ k hk => exact (step k hk).1
  refine ⟨hc,?_⟩
  intro a
  apply contDiff_iff_iteratedDeriv.mpr
  constructor
  · intro m hm
    exact ((step m (hc m)).2 a).continuous
  · intro m hm
    exact (step m (hc m)).2 a

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_AdmissibleZero
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma admissible_zero (W : BrownianSpace) (t : ℝ) :
    Admissible W t (fun _ _ ↦ (0 : ℝ)) := by
  constructor
  · intro s
    exact measurable_const
  · intro s ω
    norm_num

lemma brownian_increment_integrable (W : BrownianSpace) (t : ℝ) :
    Integrable (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω) W.μ :=
  (W.brownian.integrable_eval 1).sub (W.brownian.integrable_eval _)

lemma controlPayoff_eq (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) (α : ℝ≥0 → W.Ω → ℝ) :
    controlPayoff W γ t x α = ∫ ω,
      |x+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω|-
        (1/2 : ℝ)*controlIntegral γ t α 2 ω ∂W.μ := by
  simp only [controlPayoff, controlIntegral_eq W γ ht, pow_one]
  congr 1
  funext ω
  congr 2
  ring

lemma controlPayoff_integrable {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    Integrable (fun ω ↦ |x+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω|-
      (1/2 : ℝ)*controlIntegral γ t α 2 ω) W.μ :=
  (((integrable_const x).add (brownian_increment_integrable W t)).add
    (controlIntegral_integrable γ ht hα 1)).abs.sub
      ((controlIntegral_integrable γ ht hα 2).const_mul _)

lemma controlPayoff_upper {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    controlPayoff W γ t x α ≤ |x|+(∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)+
      (1/2 : ℝ)*∫ s in t..1, γ.cutoff s := by
  rw [controlPayoff_eq W γ ht]
  calc
    _ ≤ ∫ ω, |x|+|W.B 1 ω-W.B t.toNNReal ω|+
        (1/2 : ℝ)*(∫ s in t..1, γ.cutoff s) ∂W.μ := by
      apply integral_mono (controlPayoff_integrable γ ht x hα)
        (((integrable_const _).add (brownian_increment_integrable W t).abs).add (integrable_const _))
      intro ω
      dsimp only [Pi.add_apply]
      have hc := control_cost_bound γ ht hα ω
      have h1 := abs_add_le (x+(W.B 1 ω-W.B t.toNNReal ω)) (controlIntegral γ t α 1 ω)
      have h2 := abs_add_le x (W.B 1 ω-W.B t.toNNReal ω)
      linarith
    _ = _ := by
      have hi : Integrable (fun ω ↦ |x|+|W.B 1 ω-W.B t.toNNReal ω|) W.μ :=
        (integrable_const |x|).add (brownian_increment_integrable W t).abs
      rw [integral_add hi (integrable_const ((1/2 : ℝ)*(∫ s in t..1, γ.cutoff s))),
        integral_add (integrable_const |x|) (brownian_increment_integrable W t).abs]
      simp

lemma control_values_nonempty (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) :
    {r | ∃ α, Admissible W t α ∧ r=controlPayoff W γ t x α}.Nonempty :=
  ⟨_, ⟨_, admissible_zero W t, rfl⟩⟩

lemma control_values_bddAbove (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    BddAbove {r | ∃ α, Admissible W t α ∧ r=controlPayoff W γ t x α} := by
  refine ⟨|x|+(∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)+
      (1/2 : ℝ)*∫ s in t..1, γ.cutoff s, ?_⟩
  rintro r ⟨α,hα,rfl⟩
  exact controlPayoff_upper γ ht x hα

lemma controlPayoff_le_add_dist {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x y : ℝ) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    controlPayoff W γ t x α ≤ controlPayoff W γ t y α+|x-y| := by
  rw [controlPayoff_eq W γ ht, controlPayoff_eq W γ ht]
  have hi := controlPayoff_integrable γ ht y hα
  have hh : ∫ ω, |x+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω|-
      (1/2 : ℝ)*controlIntegral γ t α 2 ω ∂W.μ ≤
      ∫ ω, (|y+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω|-
      (1/2 : ℝ)*controlIntegral γ t α 2 ω)+|x-y| ∂W.μ := by
    apply integral_mono (controlPayoff_integrable γ ht x hα) (hi.add (integrable_const _))
    intro ω
    dsimp only [Pi.add_apply]
    have he : x+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω =
        (y+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω)+(x-y) := by ring
    rw [he]
    linarith [abs_add_le (y+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω) (x-y)]
  simpa only [integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul] using hh

lemma phi_le_add_dist (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x y : ℝ) : phi W γ t x ≤ phi W γ t y+|x-y| := by
  apply csSup_le (control_values_nonempty W γ t x)
  rintro r ⟨α,hα,rfl⟩
  exact (controlPayoff_le_add_dist γ ht x y hα).trans
    (add_le_add (le_csSup (control_values_bddAbove W γ ht y) ⟨α,hα,rfl⟩) le_rfl)

lemma phi_lipschitz (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) : LipschitzWith 1 (phi W γ t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have h := phi_le_add_dist W γ ht y x
    rw [abs_sub_comm y x] at h
    linarith
  · linarith [phi_le_add_dist W γ ht x y]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_JetAlgebra
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

namespace JetExpr

lemma uniform_bound {α : Type*} {R : ℕ → α → ℝ}
    (hR : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a, |R j a|≤C) (e : JetExpr) :
    ∃ C : ℝ, 0≤C ∧ ∀ a, |eval (fun j ↦ R j a) e|≤C := by
  induction e with
  | const c => exact ⟨|c|,abs_nonneg c,fun _ ↦ le_rfl⟩
  | coord j => exact hR j
  | add e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A+B,add_nonneg hA hB,fun a ↦ (abs_add_le _ _).trans (add_le_add (he a) (hf a))⟩
  | mul e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A*B,mul_nonneg hA hB,fun a ↦ by
      simpa only [eval,abs_mul] using mul_le_mul (he a) (hf a) (abs_nonneg _) hA⟩

end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_PredictableNormalizer
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SKValue

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma gaussian_mean {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, Z ω ∂μ = 0 := by
  rw [hZ.integral_eq, integral_id_gaussianReal]

lemma gaussian_memLp {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp Z p μ := by
  have H : MemLp (id : ℝ → ℝ) p (μ.map Z) := by
    rw [hZ.map_eq]
    exact memLp_id_gaussianReal' p hp
  simpa using (memLp_map_measure_iff H.aestronglyMeasurable hZ.aemeasurable).1 H

lemma gaussian_second_moment {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, (Z ω)^2 ∂μ = 1 := by
  have hvar := hZ.variance_eq
  rw [variance_eq_integral hZ.aemeasurable, gaussian_mean hZ] at hvar
  simpa using hvar

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_ColeHopfPDE
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma heat_log_pde {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf'' : Continuous f'') (hfg : ExpGrowth f) (hf'g : ExpGrowth f')
    (hf''g : ExpGrowth f'') {c h : ℝ} (hc : c≠0) (hh : 0<h)
    (hp : ∀ x, heat h f x ≠ 0) (x : ℝ) :
    HasDerivAt (fun r ↦ Real.log (heat r f x)/c)
      ((1/2 : ℝ)*(deriv (deriv (fun y ↦ Real.log (heat h f y)/c)) x +
        c*(deriv (fun y ↦ Real.log (heat h f y)/c) x)^2)) h := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun y ↦ (hf' y).continuousAt)
  have hd := ((heat_time_hasDerivAt hf hf' hf'' hfg hf'g hf''g x hh).log (hp x)).div_const c
  rw [heat_log_spatial_second hf hf' hf'' hfg hf'g hf''g c h hp,
    heat_log_spatial_deriv hf hf'c hfg hf'g c h hp]
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hp x,hc]
  ring

lemma coleHopf_pde_of_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0 < c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  let f := fun x ↦ Real.exp (c*ψ x)
  let f' := fun x ↦ Real.exp (c*ψ x)*(c*deriv ψ x)
  let f'' := fun x ↦ Real.exp (c*ψ x)*((c*deriv ψ x)^2+c*deriv (deriv ψ) x)
  have hψd := hψs.differentiable (by norm_num)
  have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
  have hψ'd : Differentiable ℝ (deriv ψ) := hψ's.differentiable (by norm_num)
  have hψc := hψs.continuous
  have hψ'c := hψs.continuous_deriv (by norm_num)
  have hψ''c : Continuous (deriv (deriv ψ)) :=
    hψ's.continuous_deriv (by norm_num)
  have hfd (y : ℝ) : HasDerivAt f (f' y) y := ((hψd y).hasDerivAt.const_mul c).exp
  have hf'd (y : ℝ) : HasDerivAt f' (f'' y) y := by
    have hd := (hfd y).mul ((hψ'd y).hasDerivAt.const_mul c)
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [f,f',f'']
    ring
  have hfg : ExpGrowth f := ExpGrowth.exp_lipschitz hψ hc.le
  have hψ'b (y : ℝ) : |deriv ψ y|≤1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y)
  have hf'g : ExpGrowth f' := hfg.mul_bounded hc.le (fun y ↦ by
    simpa only [abs_mul,abs_of_pos hc,mul_one] using
      mul_le_mul_of_nonneg_left (hψ'b y) hc.le)
  have hf''g : ExpGrowth f'' := hfg.mul_bounded (R := c^2+c*K) (by positivity) (fun y ↦ by
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_pos hc]
    have hsq : (c*deriv ψ y)^2 ≤ c^2 := by
      have h := sq_le_sq₀ (abs_nonneg (deriv ψ y)) zero_le_one |>.mpr (hψ'b y)
      rw [sq_abs] at h
      nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr h)]
    linarith [mul_le_mul_of_nonneg_left (hψ'' y) hc.le])
  have hp (y : ℝ) : heat h f y≠0 := (lipschitz_exp_integral_pos hψ hc.le y (Real.sqrt h)).ne'
  have hd := heat_log_pde hfd hf'd (by dsimp [f'']; fun_prop) hfg hf'g hf''g hc.ne' hh hp x
  have heq (r : ℝ) : coleHopf c r ψ = fun y ↦ Real.log (heat r f y)/c := by
    funext y
    simp only [coleHopf,ite_eq_right hc.ne',f]
  simp_rw [heq]
  exact hd

lemma coleHopf_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0 ≤ c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  rcases hc.eq_or_lt with rfl | hc
  · have hd (y : ℝ) := ((hψs.differentiable (by norm_num)) y).hasDerivAt
    have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
    have hd' (y : ℝ) := ((hψ's.differentiable (by norm_num)) y).hasDerivAt
    have hψ'g : ExpGrowth (deriv ψ) := ExpGrowth.of_bound zero_le_one (fun y ↦ by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y))
    have hψ''g := ExpGrowth.of_bound hK hψ''
    have heq (r : ℝ) : coleHopf 0 r ψ = heat r ψ := by funext y; simp [coleHopf]
    have h1 : deriv (heat h ψ)=heat h (deriv ψ) := by
      funext y
      exact (heat_spatial_hasDerivAt hd hψ's.continuous (ExpGrowth.lipschitz hψ) hψ'g y h).deriv
    have h2 : deriv (heat h (deriv ψ))=heat h (deriv (deriv ψ)) := by
      funext y
      exact (heat_spatial_hasDerivAt hd' (hψ's.continuous_deriv (by norm_num)) hψ'g hψ''g y h).deriv
    simpa only [heq,h1,h2,zero_mul,add_zero] using
      heat_time_hasDerivAt hd hd' (hψ's.continuous_deriv (by norm_num))
        (ExpGrowth.lipschitz hψ) hψ'g hψ''g x hh
  · exact coleHopf_pde_of_pos hψ hψs hK hψ'' hc hh x

lemma coleHopf_backward_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c b t : ℝ} (hc : 0 ≤ c) (ht : t<b) (x : ℝ) :
    HasDerivAt (fun s ↦ coleHopf c (b-s) ψ x)
      (-(1/2 : ℝ)*(deriv (deriv (coleHopf c (b-t) ψ)) x+
        c*(deriv (coleHopf c (b-t) ψ) x)^2)) t := by
  have hd := (coleHopf_pde hψ hψs hK hψ'' hc (sub_pos.mpr ht) x).comp t
    ((hasDerivAt_const t b).sub (hasDerivAt_id t))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_sub]
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_BoundedSmooth
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.expGrowth {f : ℝ → ℝ} (hf : BoundedSmooth f) :
    ExpGrowth f := by
  obtain ⟨C,hC,hfC⟩ := hf.bound_zero
  exact ExpGrowth.of_bound hC hfC

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatContinuity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma coleHopf_continuous {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ×ℝ ↦ coleHopf c p.1 ψ p.2) := by
  by_cases hc0 : c=0
  · simpa [SKValue.coleHopf,hc0] using heat_continuous hψ.continuous (ExpGrowth.lipschitz hψ)
  · have hH := heat_continuous (Real.continuous_exp.comp (continuous_const.mul hψ.continuous)) (ExpGrowth.exp_lipschitz hψ hc)
    simpa only [coleHopf,ite_eq_right hc0,Function.comp_def,Pi.mul_apply] using
      (hH.log (fun p ↦ (lipschitz_exp_integral_pos hψ hc p.2 (Real.sqrt p.1)).ne')).div_const c

lemma SmoothTerminal.coleHopf_uniform_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ h x, |iteratedDeriv n (deriv (coleHopf c h ψ)) x|≤C := by
  rcases hc.eq_or_lt with rfl | hc
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    refine ⟨C,hC,?_⟩
    intro h x
    rw [coleHopf_zero_coeff]
    rw [hψ.heat_deriv_jets]
    exact heat_bound hC hb h x
  · exact coleHopf_deriv_uniform_bounds_of_pos hψ.lipschitz hψ.smooth hψ.jets hc

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_LogHeatJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma nonneg_time_lipschitz {f g : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ h, 0<h → HasDerivAt f (g h) h)
    (hb : ∀ h, 0≤h → |g h|≤C) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |f s-f t|≤C* |s-t| := by
  wlog hst : s≤t generalizing s t
  · simpa only [abs_sub_comm] using this ht hs (le_of_not_ge hst)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hf.continuousOn
    (fun r hr ↦ hd r (hs.trans_lt hr.1)) (hg.intervalIntegrable _ _)
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (f := g) (C := |C|) (fun r hr ↦ by
      rw [uIoc_of_le hst] at hr
      simpa only [Real.norm_eq_abs] using
        (hb r (hs.trans hr.1.le)).trans (le_abs_self C))
  rw [he,Real.norm_eq_abs] at hb'
  simpa only [abs_of_nonneg hC,abs_sub_comm,mul_comm] using hb'

lemma SmoothTerminal.coleHopf_time_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ d : ℝ → ℝ → ℝ, Continuous (fun p : ℝ×ℝ ↦ d p.1 p.2) ∧
      (∃ C : ℝ, 0≤C ∧ ∀ h x, |d h x|≤C) ∧
      ∀ h x, 0<h → HasDerivAt (fun r ↦ iteratedDeriv n (deriv (coleHopf c r ψ)) x) (d h x) h := by
  rcases hc.eq_or_lt with rfl | hc
  · let d := fun h x ↦ (1/2 : ℝ)*iteratedDeriv (n+3) (heat h ψ) x
    refine ⟨d,continuous_const.mul (heat_jet_continuous hψ.smooth hψ.growth _),?_,?_⟩
    · obtain ⟨C,hC,hb⟩ := hψ.jets.bound (n+2)
      refine ⟨C/2,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2),
        heat_iteratedDeriv hψ.smooth hψ.growth,show n+3=(n+2)+1 from rfl,iteratedDeriv_succ']
      linarith [heat_bound hC hb h x]
    · intro h x hh
      simpa only [coleHopf_zero_coeff,←iteratedDeriv_succ'] using heat_jet_time hψ.smooth hψ.growth (n+1) x hh
  · let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
    let R := fun j (p : ℝ×ℝ) ↦ normalizedJet F j p.1 p.2
    let E := JetExpr.D JetExpr.σh (JetExpr.logGradientJet n)
    let d := fun h x ↦ c⁻¹*JetExpr.eval (fun j ↦ R j (h,x)) E
    have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    have hR : ∀ j, Continuous (R j) := fun j ↦ heat_normalizedJet_continuous hes hg hp j
    refine ⟨d,continuous_const.mul (JetExpr.continuous_eval hR E),?_,?_⟩
    · have hRb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ p, |R j p|≤C := by
        intro j
        obtain ⟨C,hC,hb⟩ := exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc.le j
        exact ⟨C,hC,fun p ↦ hb p.1 p.2⟩
      obtain ⟨C,hC,hb⟩ := JetExpr.uniform_bound hRb E
      refine ⟨|c⁻¹| * C,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb (h,x)) (abs_nonneg _)
    · intro h x hh
      simp_rw [coleHopf_gradient_jet_expr hψ hc]
      apply HasDerivAt.const_mul
      apply JetExpr.hasDerivAt_eval
      intro j
      simpa only [JetExpr.eval_σh] using heat_normalizedJet_time hes hg hp j x hh

lemma SmoothTerminal.coleHopf_jets_time_lipschitz {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s t x, 0 ≤ s → 0 ≤ t →
      |iteratedDeriv n (deriv (coleHopf c s ψ)) x-iteratedDeriv n (deriv (coleHopf c t ψ)) x|≤C* |s-t| := by
  obtain ⟨d,hdc,⟨C,hC,hb⟩,hd⟩ := hψ.coleHopf_time_jets hc n
  refine ⟨C,hC,?_⟩
  intro s t x hs ht
  exact nonneg_time_lipschitz hC
    ((hψ.coleHopf_joint_jets hc n).comp (continuous_id.prodMk continuous_const))
    (hdc.comp (continuous_id.prodMk continuous_const))
    (fun h hh ↦ hd h x hh) (fun h _ ↦ hb h x) hs ht

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_SmoothEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma coleHopf_gradient_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c h : ℝ} (hc : 0 ≤ c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ deriv (coleHopf c r ψ) x)
      ((1/2 : ℝ)*deriv (deriv (deriv (coleHopf c h ψ))) x+
        c*(deriv (coleHopf c h ψ) x*deriv (deriv (coleHopf c h ψ)) x)) h := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa only [coleHopf_zero_coeff,zero_mul,add_zero,show (3 : ℕ)=1+1+1 from rfl,
      iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using heat_jet_time hψ.smooth hψ.growth 1 x hh
  · let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
    have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    have hd := (heat_normalizedJet_time hes hg hp 1 x hh).const_mul c⁻¹
    have hj0 := congrFun (coleHopf_gradient_jet_expr hψ hc 0 h) x
    have hj1 := congrFun (coleHopf_gradient_jet_expr hψ hc 1 h) x
    have hj2 := congrFun (coleHopf_gradient_jet_expr hψ hc 2 h) x
    simp only [iteratedDeriv_zero,show (2 : ℕ)=1+1 from rfl,
      iteratedDeriv_succ,JetExpr.logGradientJet,JetExpr.D,JetExpr.σx,JetExpr.eval] at hj0 hj1 hj2
    convert! hd using 1
    · funext r
      rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc r]
    · rw [hj0,hj1,hj2]
      field_simp [hc.ne']
      ring

lemma integral_from_deriv_on_strip {T : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hg : ContinuousOn g (Icc (0 : ℝ) T))
    (hd : ∀ r∈Ioo (0 : ℝ) T, HasDerivAt f (g r) r)
    {s t : ℝ} (hs : s∈Icc (0 : ℝ) T) (ht : t∈Icc (0 : ℝ) T) :
    f s-f t=∫ r in t..s, g r := by
  have hi {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) :
      IntervalIntegrable g volume a b :=
    (hg.mono (by
      intro r hr
      rcases mem_uIcc.mp hr with hr | hr
      · exact ⟨ha.1.trans hr.1,hr.2.trans hb.2⟩
      · exact ⟨hb.1.trans hr.1,hr.2.trans ha.2⟩)).intervalIntegrable
  have he {a : ℝ} (ha : a∈Icc (0 : ℝ) T) : ∫ r in (0 : ℝ)..a, g r=f a-f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.1
      (hf.mono (Icc_subset_Icc le_rfl ha.2))
      (fun r hr ↦ hd r ⟨hr.1,hr.2.trans_le ha.2⟩) (hi ⟨le_rfl,ha.1.trans ha.2⟩ ha)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi ⟨le_rfl,ht.1.trans ht.2⟩ ht) (hi ht hs)
  rw [he hs,he ht] at hadd
  linarith

lemma SmoothTerminal.backward_jet_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) (n : ℕ) (x : ℝ) :
    Continuous (fun t ↦ iteratedDeriv n (deriv (coleHopf c (T-t) ψ)) x) := by
  have hmap : Continuous (fun t : ℝ ↦ (T-t,x)) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hj : Continuous (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (coleHopf c p.1 ψ)) p.2) :=
    hψ.coleHopf_joint_jets hc n
  convert hj.comp hmap using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma SmoothTerminal.backward_gradient_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (coleHopf c (T-t) ψ) x) := by
  simpa only [iteratedDeriv_zero] using hψ.backward_jet_continuous hc T 0 x

lemma SmoothTerminal.backward_curvature_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (deriv (coleHopf c (T-t) ψ)) x) := by
  simpa only [iteratedDeriv_one] using hψ.backward_jet_continuous hc T 1 x

lemma SmoothTerminal.backward_third_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (deriv (deriv (coleHopf c (T-t) ψ))) x) := by
  simpa only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
    using hψ.backward_jet_continuous hc T 2 x

lemma SmoothTerminal.backward_value_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ coleHopf c (T-t) ψ x) :=
  (coleHopf_continuous hψ.lipschitz hc).comp ((continuous_const.sub continuous_id).prodMk continuous_const)

lemma SmoothTerminal.backward_value_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) {s t : ℝ}
    (ht : t∈Icc (0 : ℝ) T) (hs : s∈Icc (0 : ℝ) T) (x : ℝ) :
    coleHopf c (T-s) ψ x-coleHopf c (T-t) ψ x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (coleHopf c (T-r) ψ)) x+
      c*((1/2 : ℝ)*(deriv (coleHopf c (T-r) ψ) x)^2)) := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (coleHopf c (T-r) ψ)) x+
    c*((1/2 : ℝ)*(deriv (coleHopf c (T-r) ψ) x)^2)
  have hgc : Continuous g := by
    exact (continuous_const.mul (hψ.backward_curvature_continuous hc T x)).add
      (continuous_const.mul (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).pow 2)))
  have hd (r : ℝ) (hr : r∈Ioo (0 : ℝ) T) :
      HasDerivAt (fun r ↦ coleHopf c (T-r) ψ x) (-g r) r := by
    obtain ⟨K,hK,hb⟩ := hψ.jets.deriv.bound_zero
    have hd := coleHopf_backward_pde hψ.lipschitz
      (hψ.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hK hb hc hr.2 x
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [g]
    ring
  have he := integral_from_deriv_on_strip
    (hψ.backward_value_continuous hc T x).continuousOn hgc.neg.continuousOn hd hs ht
  change _ = ∫ r in t..s, -(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.backward_gradient_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) {s t : ℝ}
    (ht : t∈Icc (0 : ℝ) T) (hs : s∈Icc (0 : ℝ) T) (x : ℝ) :
    deriv (coleHopf c (T-s) ψ) x-deriv (coleHopf c (T-t) ψ) x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (deriv (coleHopf c (T-r) ψ))) x+
      c*(deriv (coleHopf c (T-r) ψ) x*deriv (deriv (coleHopf c (T-r) ψ)) x)) := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (deriv (coleHopf c (T-r) ψ))) x+
    c*(deriv (coleHopf c (T-r) ψ) x*deriv (deriv (coleHopf c (T-r) ψ)) x)
  have hgc : Continuous g := by
    exact (continuous_const.mul (hψ.backward_third_continuous hc T x)).add
      (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).mul (hψ.backward_curvature_continuous hc T x)))
  have hd (r : ℝ) (hr : r∈Ioo (0 : ℝ) T) :
      HasDerivAt (fun r ↦ deriv (coleHopf c (T-r) ψ) x) (-g r) r := by
    have hd := (coleHopf_gradient_pde hψ hc (sub_pos.mpr hr.2) x).comp r
      ((hasDerivAt_const r T).sub (hasDerivAt_id r))
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [g]
    ring
  have he := integral_from_deriv_on_strip (hψ.backward_gradient_continuous hc T x).continuousOn hgc.neg.continuousOn hd hs ht
  change _ = ∫ r in t..s, -(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.constant_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    SmoothEvolution T (fun _ ↦ c) (fun t ↦ coleHopf c (T-t) ψ) := by
  refine ⟨fun _ _ ↦ hψ.evolve hc _,fun x ↦ (hψ.backward_value_continuous hc T x).continuousOn,
    fun n x ↦ (hψ.backward_jet_continuous hc T n x).continuousOn,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.coleHopf_uniform_jets hc n
    exact ⟨C,hC,fun t _ x ↦ hb (T-t) x⟩
  · intro n
    obtain ⟨L,hL,hb⟩ := hψ.coleHopf_jets_time_lipschitz hc n
    refine ⟨L,hL,?_⟩
    intro s hs t ht x
    have he : |(T-s)-(T-t)|=|s-t| := by rw [sub_sub_sub_cancel_left,abs_sub_comm]
    simpa only [he] using hb (T-s) (T-t) x (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2)
  · intro t ht s hs x
    exact hψ.backward_value_pde hc T ht hs x
  · intro t ht s hs x
    exact hψ.backward_gradient_pde hc T ht hs x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ShiftedPairing
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace SKValue

lemma integral_sq_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, f ω ∂μ)^2 ≤ ∫ ω, (f ω)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  exact sub_nonneg.mp h

lemma integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ) ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have hab : MemLp (fun ω ↦ |f ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have h := integral_sq_le_integral_sq hab
  simp only [sq_abs] at h
  exact (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _))
    (integral_nonneg (fun _ ↦ sq_nonneg _))).mpr h

end SKValue

open MeasureTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TimePatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma patchTime_left {E : Type*} {a t : ℝ} (f g : ℝ → E) (ht : t≤a) :
    patchTime a f g t=f t := ite_eq_left ht
lemma patchTime_right {E : Type*} {a t : ℝ} (f g : ℝ → E) (ht : a<t) :
    patchTime a f g t=g (t-a) := ite_eq_right (not_le.mpr ht)

lemma patchTime_continuous {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) a)) (hg : ContinuousOn g (Icc (0 : ℝ) b))
    (hfg : f a=g 0) : ContinuousOn (patchTime a f g) (Icc (0 : ℝ) (a+b)) := by
  have hf' : ContinuousOn f (Icc (0 : ℝ) (a+b)∩closure (Iic a)) := by
    apply hf.mono
    simp only [closure_Iic]
    exact fun _ hx ↦ ⟨hx.1.1,hx.2⟩
  have hg' : ContinuousOn (fun t ↦ g (t-a)) (Icc (0 : ℝ) (a+b)∩closure (Iic a)ᶜ) := by
    apply hg.comp (continuous_id.sub continuous_const).continuousOn
    simp only [compl_Iic,closure_Ioi]
    intro t ht
    change 0≤t-a ∧ t-a≤b
    exact ⟨sub_nonneg.mpr ht.2,by linarith [ht.1.2]⟩
  have he : ∀ t∈Icc (0 : ℝ) (a+b)∩frontier (Iic a), f t=g (t-a) := by
    intro t ht
    have ht' : t=a := by simpa only [frontier_Iic,mem_singleton_iff] using ht.2
    subst t
    simpa only [sub_self] using hfg
  have hh := ContinuousOn.piecewise he hf' hg'
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  simp only [patchTime,Set.piecewise,mem_Iic]

lemma patchTime_bound {a b C D : ℝ} (hC : 0≤C) (hD : 0≤D) {f g : ℝ → ℝ}
    (hf : ∀ t∈Icc (0 : ℝ) a, |f t|≤C) (hg : ∀ t∈Icc (0 : ℝ) b, |g t|≤D) :
    ∀ t∈Icc (0 : ℝ) (a+b), |patchTime a f g t|≤C+D := by
  intro t ht
  by_cases hta : t≤a
  · rw [patchTime_left f g hta]
    exact (hf t ⟨ht.1,hta⟩).trans (le_add_of_nonneg_right hD)
  · rw [patchTime_right f g (lt_of_not_ge hta)]
    exact (hg (t-a) ⟨by linarith,by linarith [ht.2]⟩).trans (le_add_of_nonneg_left hC)

lemma patchTime_lipschitz {a b C D : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hC : 0≤C) (hD : 0≤D) {f g : ℝ → ℝ}
    (hf : ∀ s∈Icc (0 : ℝ) a, ∀ t∈Icc (0 : ℝ) a, |f s-f t|≤C*|s-t|)
    (hg : ∀ s∈Icc (0 : ℝ) b, ∀ t∈Icc (0 : ℝ) b, |g s-g t|≤D*|s-t|)
    (hfg : f a=g 0) :
    ∀ s∈Icc (0 : ℝ) (a+b), ∀ t∈Icc (0 : ℝ) (a+b),
      |patchTime a f g s-patchTime a f g t|≤(C+D)*|s-t| := by
  have hcross {s t : ℝ} (hs : s∈Icc (0 : ℝ) a) (ht : t∈Icc a (a+b)) :
      |f s-g (t-a)|≤(C+D)*|s-t| := by
    have h1 := hf s hs a ⟨ha,le_rfl⟩
    have h2 := hg 0 ⟨le_rfl,hb⟩ (t-a) ⟨sub_nonneg.mpr ht.1,by linarith [ht.2]⟩
    have hh := abs_sub_le (f s) (f a) (g (t-a))
    rw [hfg] at hh h1
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)] at h1
    rw [zero_sub,abs_neg,abs_of_nonneg (sub_nonneg.mpr ht.1)] at h2
    rw [abs_of_nonpos (sub_nonpos.mpr (hs.2.trans ht.1))]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr ht.1),mul_nonneg hD (sub_nonneg.mpr hs.2)]
  intro s hs t ht
  by_cases hsa : s≤a <;> by_cases hta : t≤a
  · rw [patchTime_left f g hsa,patchTime_left f g hta]
    have hh := hf s ⟨hs.1,hsa⟩ t ⟨ht.1,hta⟩
    nlinarith [mul_nonneg hD (abs_nonneg (s-t))]
  · rw [patchTime_left f g hsa,patchTime_right f g (lt_of_not_ge hta)]
    exact hcross ⟨hs.1,hsa⟩ ⟨le_of_lt (lt_of_not_ge hta),ht.2⟩
  · rw [patchTime_right f g (lt_of_not_ge hsa),patchTime_left f g hta,abs_sub_comm,abs_sub_comm s t]
    exact hcross ⟨ht.1,hta⟩ ⟨le_of_lt (lt_of_not_ge hsa),hs.2⟩
  · rw [patchTime_right f g (lt_of_not_ge hsa),patchTime_right f g (lt_of_not_ge hta)]
    have hh := hg (s-a) ⟨by linarith,by linarith [hs.2]⟩ (t-a) ⟨by linarith,by linarith [ht.2]⟩
    rw [sub_sub_sub_cancel_right] at hh
    nlinarith [mul_nonneg hC (abs_nonneg (s-t))]

lemma patchTime_intervalIntegrable {a b : ℝ} (ha : 0≤a) (hb : 0≤b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 a) (hg : IntervalIntegrable g volume 0 b) :
    IntervalIntegrable (patchTime a f g) volume 0 (a+b) := by
  have hl : IntervalIntegrable (patchTime a f g) volume 0 a := by
    apply hf.congr_uIoo
    rw [uIoo_of_le ha]
    intro t ht
    exact (patchTime_left f g ht.2.le).symm
  have hr : IntervalIntegrable (fun t ↦ g (t-a)) volume a (a+b) := by
    simpa only [zero_add,add_comm b a] using hg.comp_sub_right a
  apply hl.trans
  apply hr.congr_uIoo
  rw [uIoo_of_le (le_add_of_nonneg_right hb)]
  intro t ht
  exact (patchTime_right f g ht.1).symm

lemma patchTime_integral_left {a s : ℝ} (hs : s∈Icc (0 : ℝ) a) (f g : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..s, patchTime a f g r)=∫ r in (0 : ℝ)..s, f r := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hs.1]
  exact fun r hr ↦ patchTime_left f g (hr.2.trans hs.2)

lemma patchTime_integral_right {a s : ℝ} (hs : a ≤ s) (f g : ℝ → ℝ) :
    (∫ r in a..s, patchTime a f g r)=∫ r in (0 : ℝ)..(s-a), g r := by
  calc
    _ = ∫ r in a..s, g (r-a) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hs
      exact fun r hr ↦ patchTime_right f g hr.1
    _ = _ := by rw [intervalIntegral.integral_comp_sub_right,sub_self]

lemma patchTime_primitive {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {f g p q : ℝ → ℝ} (hp : IntervalIntegrable p volume 0 a)
    (hq : IntervalIntegrable q volume 0 b)
    (hf : ∀ t∈Icc (0 : ℝ) a, f t-f 0=∫ r in (0 : ℝ)..t, p r)
    (hg : ∀ t∈Icc (0 : ℝ) b, g t-g 0=∫ r in (0 : ℝ)..t, q r)
    (hfg : f a=g 0) : ∀ t∈Icc (0 : ℝ) (a+b),
    patchTime a f g t-patchTime a f g 0=∫ r in (0 : ℝ)..t, patchTime a p q r := by
  intro t ht
  rw [patchTime_left f g ha]
  by_cases hta : t≤a
  · rw [patchTime_left f g hta,patchTime_integral_left ⟨ht.1,hta⟩]
    exact hf t ⟨ht.1,hta⟩
  · rw [patchTime_right f g (lt_of_not_ge hta)]
    have hi := patchTime_intervalIntegrable ha hb hp hq
    have hsub {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) :
        uIcc s t⊆uIcc (0 : ℝ) (a+b) := by
      rw [uIcc_of_le (add_nonneg ha hb)]
      exact uIcc_subset_Icc hs ht
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (hi.mono_set (hsub ⟨le_rfl,add_nonneg ha hb⟩ ⟨ha,le_add_of_nonneg_right hb⟩))
      (hi.mono_set (hsub ⟨ha,le_add_of_nonneg_right hb⟩ ht))
    rw [patchTime_integral_left ⟨ha,le_rfl⟩,patchTime_integral_right (le_of_lt (lt_of_not_ge hta))] at hh
    have h1 := hf a ⟨ha,le_rfl⟩
    have h2 := hg (t-a) ⟨by linarith,by linarith [ht.2]⟩
    linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolutionPatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma patchTime_apply {a t x : ℝ} (V W : ℝ → ℝ → ℝ) :
    patchTime a V W t x=patchTime a (fun t ↦ V t x) (fun t ↦ W t x) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma patchTime_gradient {a t : ℝ} (V W : ℝ → ℝ → ℝ) :
    deriv (patchTime a V W t)=patchTime a (fun t ↦ deriv (V t)) (fun t ↦ deriv (W t)) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma patchTime_jet {a t x : ℝ} (V W : ℝ → ℝ → ℝ) (n : ℕ) :
    iteratedDeriv n (deriv (patchTime a V W t)) x=
      patchTime a (fun t ↦ iteratedDeriv n (deriv (V t)) x) (fun t ↦ iteratedDeriv n (deriv (W t)) x) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma SmoothEvolution.value_rhs_integrable {T : ℝ} (hT : 0≤T)
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V)
    (hg : IntervalIntegrable γ volume 0 T) (x : ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2 : ℝ)*deriv (deriv (V r)) x+
      γ r*((1/2 : ℝ)*(deriv (V r) x)^2))) volume 0 T := by
  have hc1 : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have hc0 : ContinuousOn (fun t ↦ deriv (V t) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using h.continuous_jet 0 x
  apply IntervalIntegrable.neg
  apply IntervalIntegrable.add (hc1.intervalIntegrable.const_mul _)
  apply hg.mul_continuousOn
  convert! continuousOn_const.mul (hc0.pow 2) using 1
  all_goals try with_reducible_and_instances rfl

lemma SmoothEvolution.gradient_rhs_integrable {T : ℝ} (hT : 0≤T)
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V)
    (hg : IntervalIntegrable γ volume 0 T) (x : ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V r))) x+
      γ r*(deriv (V r) x*deriv (deriv (V r)) x))) volume 0 T := by
  have hc2 : ContinuousOn (fun t ↦ deriv (deriv (deriv (V t))) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
      using h.continuous_jet 2 x
  have hc1 : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have hc0 : ContinuousOn (fun t ↦ deriv (V t) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using h.continuous_jet 0 x
  apply IntervalIntegrable.neg
  apply IntervalIntegrable.add (hc2.intervalIntegrable.const_mul _)
  apply hg.mul_continuousOn
  convert! hc0.mul hc1 using 1
  all_goals try with_reducible_and_instances rfl

lemma primitive_to_integral {T : ℝ} (hT : 0≤T) {f p : ℝ → ℝ}
    (hp : IntervalIntegrable p volume 0 T)
    (hf : ∀ t∈Icc (0 : ℝ) T, f t-f 0=∫ r in (0 : ℝ)..t, p r)
    {s t : ℝ} (hs : s∈Icc (0 : ℝ) T) (ht : t∈Icc (0 : ℝ) T) :
    f s-f t=∫ r in t..s, p r := by
  have hi {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) :
      IntervalIntegrable p volume a b := hp.mono_set (by
    rw [uIcc_of_le hT]
    exact uIcc_subset_Icc ha hb)
  have hh := intervalIntegral.integral_add_adjacent_intervals (hi ⟨le_rfl,hT⟩ ht) (hi ht hs)
  rw [←hf s hs,←hf t ht] at hh
  linarith

lemma SmoothEvolution.patch_value_pde {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) (x : ℝ) :
    patchTime a V W s x-patchTime a V W t x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (patchTime a V W r)) x+
      patchTime a γ η r*((1/2 : ℝ)*(deriv (patchTime a V W r) x)^2)) := by
  let p := fun r ↦ -((1/2 : ℝ)*deriv (deriv (V r)) x+γ r*((1/2 : ℝ)*(deriv (V r) x)^2))
  let q := fun r ↦ -((1/2 : ℝ)*deriv (deriv (W r)) x+η r*((1/2 : ℝ)*(deriv (W r) x)^2))
  have hp := hV.value_rhs_integrable ha hγ x
  have hq := hW.value_rhs_integrable hb hη x
  have hv : ∀ t∈Icc (0 : ℝ) a, V t x-V 0 x=∫ r in (0 : ℝ)..t, p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.value_pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw : ∀ t∈Icc (0 : ℝ) b, W t x-W 0 x=∫ r in (0 : ℝ)..t, q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.value_pde 0 ⟨le_rfl,hb⟩ t ht x
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw (congrFun hjoin x)) hs ht
  rw [←patchTime_apply V W,←patchTime_apply V W] at he
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr : r≤a <;> simp [patchTime,hr]

lemma SmoothEvolution.patch_gradient_pde {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) (x : ℝ) :
    deriv (patchTime a V W s) x-deriv (patchTime a V W t) x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (deriv (patchTime a V W r))) x+
      patchTime a γ η r*(deriv (patchTime a V W r) x*deriv (deriv (patchTime a V W r)) x)) := by
  let p := fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V r))) x+γ r*(deriv (V r) x*deriv (deriv (V r)) x))
  let q := fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (W r))) x+η r*(deriv (W r) x*deriv (deriv (W r)) x))
  have hp := hV.gradient_rhs_integrable ha hγ x
  have hq := hW.gradient_rhs_integrable hb hη x
  have hv : ∀ t∈Icc (0 : ℝ) a, deriv (V t) x-deriv (V 0) x=∫ r in (0 : ℝ)..t, p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.gradient_pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw : ∀ t∈Icc (0 : ℝ) b, deriv (W t) x-deriv (W 0) x=∫ r in (0 : ℝ)..t, q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.gradient_pde 0 ⟨le_rfl,hb⟩ t ht x
  have hj : deriv (V a) x=deriv (W 0) x := by rw [hjoin]
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw hj) hs ht
  simp_rw [patchTime_gradient,patchTime_apply]
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr : r≤a <;> simp [patchTime,hr]

lemma SmoothEvolution.patch {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) :
    SmoothEvolution (a+b) (patchTime a γ η) (patchTime a V W) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro t ht
    by_cases hta : t≤a
    · rw [patchTime_left V W hta]
      exact hV.slices t ⟨ht.1,hta⟩
    · rw [patchTime_right V W (lt_of_not_ge hta)]
      exact hW.slices (t-a) ⟨by linarith,by linarith [ht.2]⟩
  · intro x
    simp_rw [patchTime_apply]
    exact patchTime_continuous (hV.continuous_value x) (hW.continuous_value x) (congrFun hjoin x)
  · intro n x
    simp_rw [patchTime_jet]
    apply patchTime_continuous (hV.continuous_jet n x) (hW.continuous_jet n x)
    rw [hjoin]
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.bound n
    obtain ⟨D,hD,hw⟩ := hW.bound n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro t ht x
    rw [patchTime_jet]
    exact patchTime_bound hC hD (fun t ht ↦ hv t ht x) (fun t ht ↦ hw t ht x) t ht
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.temporal n
    obtain ⟨D,hD,hw⟩ := hW.temporal n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro s hs t ht x
    rw [patchTime_jet,patchTime_jet]
    apply patchTime_lipschitz ha hb hC hD (fun s hs t ht ↦ hv s hs t ht x)
      (fun s hs t ht ↦ hw s hs t ht x) _ s hs t ht
    rw [hjoin]
  · intro t ht s hs x
    exact hV.patch_value_pde ha hb hW hγ hη hjoin hs ht x
  · intro t ht s hs x
    exact hV.patch_gradient_pde ha hb hW hγ hη hjoin hs ht x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolveStrips
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.jet_joint {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) :
    ∃ L : ℝ, 0≤L ∧ ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |iteratedDeriv n (deriv (V s)) y-iteratedDeriv n (deriv (V t)) x|≤L*(|s-t|+|y-x|) := by
  obtain ⟨A,hA,ha⟩ := h.temporal n
  obtain ⟨B,hB,hb⟩ := h.bound (n+1)
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro s hs t ht x y
  have hd := (h.slices t ht).jets.smooth.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
  have hl : LipschitzWith ⟨B,hB⟩ (iteratedDeriv n (deriv (V t))) := by
    apply lipschitzWith_of_nnnorm_deriv_le hd
    intro z
    have hz := hb t ht z
    rw [iteratedDeriv_succ] at hz
    exact_mod_cast hz
  have hx := hl.dist_le_mul y x
  simp only [Real.dist_eq] at hx
  change |iteratedDeriv n (deriv (V t)) y-iteratedDeriv n (deriv (V t)) x|≤B*|y-x| at hx
  have hh := abs_sub_le (iteratedDeriv n (deriv (V s)) y)
    (iteratedDeriv n (deriv (V t)) y) (iteratedDeriv n (deriv (V t)) x)
  have ht := ha s hs t ht y
  nlinarith [mul_nonneg hA (abs_nonneg (y-x)),mul_nonneg hB (abs_nonneg (s-t))]

lemma SmoothEvolution.deriv_bound {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
    |deriv (V t) x|≤1 := by
  simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (h.slices t ht).lipschitz (x₀ := x)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_FiniteStepEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma profileTime_nonneg (l : HeatProfile) : 0≤profileTime l := by
  induction l with
  | nil => exact le_rfl
  | cons p l ih => exact add_nonneg p.1.coe_nonneg ih

lemma profileCoeff_nonneg (l : HeatProfile) (t : ℝ) : 0≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact le_rfl
  | cons p l ih =>
    change 0≤patchTime _ _ _ t
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht]
      exact p.2.coe_nonneg
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _

lemma profileCoeff_integrable (l : HeatProfile) :
    IntervalIntegrable (profileCoeff l) volume 0 (profileTime l) := by
  induction l with
  | nil => exact intervalIntegrable_const
  | cons p l ih =>
    exact patchTime_intervalIntegrable p.1.coe_nonneg (profileTime_nonneg l) intervalIntegrable_const ih

lemma profileCoeff_measurable (l : HeatProfile) : Measurable (profileCoeff l) := by
  induction l with
  | nil => exact measurable_const
  | cons p l ih =>
    unfold profileCoeff patchTime
    exact Measurable.ite measurableSet_Iic measurable_const (ih.comp (measurable_id.sub measurable_const))

lemma SmoothTerminal.zero_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) :
    SmoothEvolution 0 (fun _ ↦ 0) (fun _ ↦ ψ) := by
  refine ⟨fun _ _ ↦ hψ,fun _ ↦ continuousOn_const,fun _ _ ↦ continuousOn_const,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    exact ⟨C,hC,fun _ _ ↦ hb⟩
  · intro n
    exact ⟨0,le_rfl,by intros; simp⟩
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp

lemma SmoothTerminal.profile_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (l : HeatProfile) :
    SmoothEvolution (profileTime l) (profileCoeff l) (profileValue ψ l) := by
  induction l with
  | nil => exact hψ.zero_evolution
  | cons p l ih =>
    have hv : SmoothTerminal (profileValue ψ l 0) := ih.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hc := hv.constant_evolution p.2.coe_nonneg (p.1 : ℝ)
    apply hc.patch p.1.coe_nonneg (profileTime_nonneg l) ih intervalIntegrable_const (profileCoeff_integrable l)
    funext x
    simp only [sub_self,coleHopf_zero]

lemma profileCoeff_lower {l : HeatProfile} {c : ℝ}
    (hc : ∀ p∈l, c≤(p.2 : ℝ)) {t : ℝ} (ht : t∈Ioc (0 : ℝ) (profileTime l)) :
    c≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact (not_lt_of_ge ht.2 ht.1).elim
  | cons p l ih =>
    change c≤patchTime (p.1 : ℝ) _ _ t
    by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hta]
      exact hc p (by simp)
    · rw [patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih (fun q hq ↦ hc q (by simp [hq]))
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩

lemma profileCoeff_mono {l : HeatProfile} (hl : l.Pairwise (fun p q ↦ p.2≤q.2)) :
    MonotoneOn (profileCoeff l) (Icc (0 : ℝ) (profileTime l)) := by
  induction l with
  | nil => intro s hs t ht hst; exact le_rfl
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp hl
    intro s hs t ht hst
    change patchTime (p.1 : ℝ) _ _ s≤patchTime (p.1 : ℝ) _ _ t
    by_cases hsa : s≤(p.1 : ℝ) <;> by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hsa,patchTime_left _ _ hta]
    · rw [patchTime_left _ _ hsa,patchTime_right _ _ (lt_of_not_ge hta)]
      apply profileCoeff_lower (fun q hq ↦ by exact_mod_cast hp q hq)
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
    · exact (hsa (hst.trans hta)).elim
    · rw [patchTime_right _ _ (lt_of_not_ge hsa),patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih hl
      · exact ⟨by linarith,by have hsu : s≤(p.1 : ℝ)+profileTime l := hs.2; linarith⟩
      · exact ⟨by linarith,by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
      · linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_GridProfile
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma gridProfile_time (d : ℝ≥0) (f : ℕ → ℝ≥0) (j n : ℕ) :
    profileTime (gridProfile d f j n)=(n : ℝ)*d := by
  induction n generalizing j with
  | zero => simp only [gridProfile,profileTime,Nat.cast_zero,zero_mul]
  | succ n ih => simp only [gridProfile,profileTime,ih,Nat.cast_add,Nat.cast_one]; ring

lemma gridProfile_mem {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ} {p : ℝ≥0 × ℝ≥0}
    (hp : p∈gridProfile d f j n) : ∃ i, j ≤ i ∧ i<j+n ∧ p=(d,f i) := by
  induction n generalizing j with
  | zero => simp only [gridProfile,List.not_mem_nil] at hp
  | succ n ih =>
    simp only [gridProfile,List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨j,le_rfl,by omega,rfl⟩
    · obtain ⟨i,hi,hij,rfl⟩ := ih hp
      exact ⟨i,by omega,by omega,rfl⟩

lemma gridProfile_pairwise {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ}
    (hm : ∀ i k, j ≤ i → i<k → k<j+n → f i ≤ f k) :
    (gridProfile d f j n).Pairwise (fun p q ↦ p.2 ≤ q.2) := by
  induction n generalizing j with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [gridProfile,List.pairwise_cons]
    constructor
    · intro q hq
      obtain ⟨i,hi,hij,rfl⟩ := gridProfile_mem hq
      exact hm j i le_rfl (by omega) (by omega)
    · exact ih (fun i k hi hik hk ↦ hm i k (by omega) hik (by omega))

lemma gridProfile_sample {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ}
    (hn : 0<n) {t : ℝ} (ht : t∈Icc (0 : ℝ) ((n : ℝ)*d)) :
    ∃ i, j ≤ i ∧ i<j+n ∧
      profileCoeff (gridProfile d f j n) t=(f i : ℝ) ∧
      0 ≤ (j : ℝ)*d+t-(i : ℝ)*d ∧ (j : ℝ)*d+t-(i : ℝ)*d ≤ d := by
  induction n generalizing j t with
  | zero => omega
  | succ n ih =>
    by_cases htd : t ≤ (d : ℝ)
    · refine ⟨j,le_rfl,by omega,?_,?_,?_⟩
      · exact patchTime_left _ _ htd
      · linarith [ht.1]
      · linarith
    · have hd : (d : ℝ)<t := lt_of_not_ge htd
      have hn' : 0<n := by
        by_contra hh
        have hn0 : n=0 := by omega
        subst n
        simp only [Nat.cast_one,zero_add,one_mul] at ht
        exact htd ht.2
      have ht' : t-(d : ℝ)∈Icc (0 : ℝ) ((n : ℝ)*d) := by
        constructor
        · linarith
        · have hu := ht.2
          rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul] at hu
          linarith
      obtain ⟨i,hij,hin,hc,hlo,hhi⟩ := ih hn' ht' (j := j+1)
      refine ⟨i,by omega,by omega,?_,?_,?_⟩
      · change patchTime (d : ℝ) _ _ t=_
        rw [patchTime_right _ _ hd]
        exact hc
      · simp only [Nat.cast_add,Nat.cast_one] at hlo
        nlinarith
      · simp only [Nat.cast_add,Nat.cast_one] at hhi
        nlinarith

lemma gridDelta_coe (n : ℕ) : (gridDelta n : ℝ)=1/(n+1 : ℝ) := rfl

lemma OrderParameter.grid_time (γ : OrderParameter) (n : ℕ) : profileTime (γ.grid n)=1 := by
  rw [OrderParameter.grid,gridProfile_time]
  simp only [gridDelta_coe,Nat.cast_add,Nat.cast_one]
  field_simp

lemma OrderParameter.grid_mono (γ : OrderParameter) (n : ℕ) :
    (γ.grid n).Pairwise (fun p q ↦ p.2 ≤ q.2) := by
  apply gridProfile_pairwise
  intro i k hi hik hk
  apply Real.toNNReal_mono
  apply γ.monotone
  · exact ⟨by positivity,(div_lt_one (by positivity)).mpr (by exact_mod_cast (lt_trans hik (by simpa using hk)))⟩
  · exact ⟨by positivity,(div_lt_one (by positivity)).mpr (by exact_mod_cast (show k<n+1 by simpa using hk))⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hik.le) (by positivity)

lemma OrderParameter.grid_sample (γ : OrderParameter) (n : ℕ) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) : ∃ r∈Ico (0 : ℝ) 1,
      profileCoeff (γ.grid n) t=γ.coeff r ∧ r ≤ t ∧ t-r ≤ 1/(n+1 : ℝ) := by
  have hnd : ((n+1 : ℕ) : ℝ)*(gridDelta n : ℝ≥0)=1 := by
    simp only [gridDelta_coe,Nat.cast_add,Nat.cast_one]; field_simp
  obtain ⟨i,hi,hin,hc,hlo,hhi⟩ := gridProfile_sample (d := gridDelta n)
    (f := fun i ↦ (γ.coeff ((i : ℝ)/(n+1 : ℝ))).toNNReal) (j := 0)
    (Nat.succ_pos n) (t := t) (by simpa only [hnd] using ht)
  have hr : (i : ℝ)/(n+1 : ℝ)∈Ico (0 : ℝ) 1 :=
    ⟨by positivity,(div_lt_one (by positivity)).mpr (by exact_mod_cast (show i<n+1 by simpa using hin))⟩
  refine ⟨(i : ℝ)/(n+1 : ℝ),hr,?_,?_,?_⟩
  · simpa only [OrderParameter.grid,Real.coe_toNNReal _ (γ.nonneg _ hr)] using hc
  · simp only [Nat.cast_zero,zero_mul,zero_add,gridDelta_coe] at hlo
    rw [mul_one_div] at hlo
    linarith
  · simpa only [Nat.cast_zero,zero_mul,zero_add,gridDelta_coe,mul_one_div,zero_div,zero_add] using hhi

lemma OrderParameter.grid_le (γ : OrderParameter) (n : ℕ) {t : ℝ}
    (ht : t∈Ico (0 : ℝ) 1) : profileCoeff (γ.grid n) t ≤ γ.coeff t := by
  obtain ⟨r,hr,hc,hrt,_⟩ := γ.grid_sample n ⟨ht.1,ht.2.le⟩
  rw [hc]
  exact γ.monotone hr ht hrt

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_LogCoshTerminal
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma logCoshTerminal_smooth (M : ℝ) : ContDiff ℝ ∞ (logCoshTerminal M) := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact contDiff_const.mul (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id))
  · intro x
    exact (mul_pos (by norm_num) (Real.cosh_pos (M*x))).ne'

lemma logCoshTerminal_hasDerivAt {M : ℝ} (hM : M≠0) (x : ℝ) :
    HasDerivAt (logCoshTerminal M) (Real.tanh (M*x)) x := by
  have hc := (Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd := ((hc.const_mul 2).log (mul_pos (by norm_num : (0:ℝ)<2) (Real.cosh_pos (M*x))).ne').div_const M
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  rw [Real.tanh_eq_sinh_div_cosh]
  simp only [Function.comp_apply, mul_one]
  field_simp

lemma tanh_scaled_hasDerivAt (M x : ℝ) :
    HasDerivAt (fun x ↦ Real.tanh (M*x)) (M*(1-(Real.tanh (M*x))^2)) x := by
  have hs := (Real.hasDerivAt_sinh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hc := (Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd := hs.div hc (Real.cosh_pos (M*x)).ne'
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Function.comp_apply, mul_one]
  field_simp [(Real.cosh_pos (M*x)).ne']

namespace JetExpr

lemma iteratedDeriv_fieldJet {R : ℕ → ℝ → ℝ} {σ : ℕ → JetExpr}
    (hd : ∀ j x, HasDerivAt (R j) (eval (fun i ↦ R i x) (σ j)) x) (e : JetExpr) (n : ℕ) :
    iteratedDeriv n (fun x ↦ eval (fun j ↦ R j x) e)=
      fun x ↦ eval (fun j ↦ R j x) (fieldJet σ e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (hasDerivAt_eval (fun j ↦ hd j x) _).deriv
end JetExpr

lemma logCoshTerminal_jets {M : ℝ} (hM : M≠0) :
    BoundedSmooth (deriv (logCoshTerminal M)) := by
  refine ⟨(contDiff_infty_iff_deriv.mp (logCoshTerminal_smooth M)).2,?_⟩
  intro n
  let σ : ℕ → JetExpr := fun _ ↦ JetExpr.mul (JetExpr.const M)
    (JetExpr.add (JetExpr.const 1) (JetExpr.mul (JetExpr.const (-1)) (JetExpr.mul (JetExpr.coord 0) (JetExpr.coord 0))))
  let R : ℕ → ℝ → ℝ := fun _ x ↦ Real.tanh (M*x)
  have hd : ∀ j x, HasDerivAt (R j) (JetExpr.eval (fun i ↦ R i x) (σ j)) x := by
    intro j x
    convert! tanh_scaled_hasDerivAt M x using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [σ,JetExpr.eval,R]
    ring
  have he : deriv (logCoshTerminal M)=fun x ↦ JetExpr.eval (fun j ↦ R j x) (JetExpr.coord 0) := by
    funext x
    exact (logCoshTerminal_hasDerivAt hM x).deriv
  rw [he,JetExpr.iteratedDeriv_fieldJet hd]
  exact JetExpr.uniform_bound (fun _ ↦ ⟨1,by norm_num,fun x ↦ (Real.abs_tanh_lt_one (M*x)).le⟩) _

lemma logCoshTerminal_smoothTerminal {M : ℝ} (hM : 0<M) : SmoothTerminal (logCoshTerminal M) := by
  have hs := logCoshTerminal_smooth M
  refine ⟨?_,hs,logCoshTerminal_jets hM.ne'⟩
  apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)))
  intro x
  have he := (logCoshTerminal_hasDerivAt hM.ne' x).deriv
  rw [he]
  exact_mod_cast (Real.abs_tanh_lt_one (M*x)).le

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_GridConvergence
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma OrderParameter.grid_tendsto (γ : OrderParameter) {t : ℝ} (ht : t∈Ico (0 : ℝ) 1)
    (hc : ContinuousWithinAt γ.coeff (Ico (0 : ℝ) 1) t) :
    Tendsto (fun n ↦ profileCoeff (γ.grid n) t) atTop (𝓝 (γ.coeff t)) := by
  have hp (n : ℕ) := γ.grid_sample n ⟨ht.1,ht.2.le⟩
  choose r hr he hrt hdist using hp
  have hrd : Tendsto (fun n ↦ dist (r n) t) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (hrt n))]
    exact hdist n
  have hrl : Tendsto r atTop (𝓝 t) := (tendsto_iff_dist_tendsto_zero).mpr hrd
  have hl := hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hrl,Eventually.of_forall hr⟩)
  exact hl.congr (fun n ↦ (he n).symm)

lemma OrderParameter.grid_ae_tendsto (γ : OrderParameter) :
    ∀ᵐ t ∂volume, t∈Ioc (0 : ℝ) 1 →
      Tendsto (fun n ↦ profileCoeff (γ.grid n) t) atTop (𝓝 (γ.cutoff t)) := by
  filter_upwards [γ.monotone.countable_not_continuousWithinAt.ae_notMem volume,Measure.ae_ne volume (1 : ℝ)] with t hc hne ht
  have ht' : t∈Ico (0 : ℝ) 1 := ⟨ht.1.le,lt_of_le_of_ne ht.2 hne⟩
  have hc' : ContinuousWithinAt γ.coeff (Ico (0 : ℝ) 1) t := by
    by_contra hh
    exact hc ⟨ht',hh⟩
  simpa only [OrderParameter.cutoff,indicator_of_mem ht'] using γ.grid_tendsto ht' hc'

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma smoothApprox_evolution (γ : OrderParameter) (n : ℕ) :
    SmoothEvolution 1 (profileCoeff (γ.grid n)) (smoothApprox γ n) := by
  unfold smoothApprox
  convert (logCoshTerminal_smoothTerminal (by positivity : (0 : ℝ)<n+1)).profile_evolution (γ.grid n) using 1
  all_goals try with_reducible_and_instances rfl
  exact (γ.grid_time n).symm

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BetaBound
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set
open scoped Topology
namespace SKValue

lemma inv_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) : (Real.sqrt x)⁻¹=x^(-(1/2 : ℝ)) := by
  rw [Real.rpow_neg hx,Real.sqrt_eq_rpow]

lemma intervalIntegrable_inv_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt s)⁻¹) volume a b := by
  apply (intervalIntegral.intervalIntegrable_rpow' (a := a) (b := b) (r := -(1/2 : ℝ)) (by norm_num)).congr
  intro s hs
  exact (inv_sqrt_eq_rpow ((le_min ha hb).trans hs.1.le)).symm

lemma integral_inv_sqrt {d : ℝ} (hd : 0 ≤ d) :
    (∫ s in (0 : ℝ)..d, (Real.sqrt s)⁻¹) = 2*Real.sqrt d := by
  calc
    _ = ∫ s in (0 : ℝ)..d, s^(-(1/2 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hd] at hs
      exact inv_sqrt_eq_rpow hs.1
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num))]
      norm_num [Real.sqrt_eq_rpow]
      ring

lemma intervalIntegrable_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt (s-a))⁻¹) volume a b := by
  have h := (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_right a
  simpa only [zero_add,sub_add_cancel] using h

lemma intervalIntegrable_inv_sqrt_sub_left {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun s : ℝ ↦ (Real.sqrt (b-s))⁻¹) volume a b := by
  have h := (intervalIntegrable_inv_sqrt (a := 0) (b := b-a) le_rfl (sub_nonneg.mpr hab)).comp_sub_left b
  simpa only [sub_sub_cancel,sub_zero] using h.symm

lemma integral_inv_sqrt_sub {a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, (Real.sqrt (s-a))⁻¹)=2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_right (fun s : ℝ ↦ (Real.sqrt s)⁻¹),sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

lemma integral_inv_sqrt_sub_left {a b : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, (Real.sqrt (b-s))⁻¹)=2*Real.sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ ↦ (Real.sqrt s)⁻¹),sub_self,integral_inv_sqrt (sub_nonneg.mpr hab)]

lemma sqrtKernel_nonneg (a b s : ℝ) : 0 ≤ sqrtKernel a b s := by unfold sqrtKernel; positivity

lemma sqrtKernel_le_majorant {a b s : ℝ} (hab : a<b) (hs : s∈Icc a b) :
    sqrtKernel a b s ≤ sqrtMajorant a b s := by
  have hd := Real.sqrt_pos.mpr (sub_pos.mpr hab)
  have hD := Real.sq_sqrt (sub_nonneg.mpr hab.le)
  have hx := Real.sq_sqrt (sub_nonneg.mpr hs.1)
  have hy := Real.sq_sqrt (sub_nonneg.mpr hs.2)
  have hsx := Real.sqrt_nonneg (s-a)
  have hsy := Real.sqrt_nonneg (b-s)
  unfold sqrtKernel sqrtMajorant
  by_cases hsa : s=a
  · subst s
    simp only [sub_self,Real.sqrt_zero,inv_zero,zero_mul,zero_add]
    positivity
  by_cases hsb : s=b
  · subst s
    simp only [sub_self,Real.sqrt_zero,inv_zero,mul_zero,add_zero]
    positivity
  have hxpos := Real.sqrt_pos.mpr (sub_pos.mpr (lt_of_le_of_ne hs.1 (Ne.symm hsa)))
  have hypos := Real.sqrt_pos.mpr (sub_pos.mpr (lt_of_le_of_ne hs.2 hsb))
  have hc : 0 ≤ 2/Real.sqrt (b-a) := by positivity
  by_cases hm : (b-a)/2 ≤ s-a
  · have hsqrt : Real.sqrt (b-a) ≤ 2*Real.sqrt (s-a) := by nlinarith
    have hi : (Real.sqrt (s-a))⁻¹ ≤ 2/Real.sqrt (b-a) := by
      rw [inv_eq_one_div,div_le_div_iff₀ hxpos hd]
      nlinarith
    calc
      _  ≤  (2/Real.sqrt (b-a))*(Real.sqrt (b-s))⁻¹ := mul_le_mul_of_nonneg_right hi (by positivity)
      _  ≤  _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hc
  · have hsqrt : Real.sqrt (b-a) ≤ 2*Real.sqrt (b-s) := by nlinarith
    have hi : (Real.sqrt (b-s))⁻¹ ≤ 2/Real.sqrt (b-a) := by
      rw [inv_eq_one_div,div_le_div_iff₀ hypos hd]
      nlinarith
    calc
      _  ≤  (Real.sqrt (s-a))⁻¹*(2/Real.sqrt (b-a)) := mul_le_mul_of_nonneg_left hi (by positivity)
      _  ≤  _ := by nlinarith [mul_nonneg hc (inv_nonneg.mpr hsy)]

lemma sqrtMajorant_integrable {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (sqrtMajorant a b) volume a b :=
  ((intervalIntegrable_inv_sqrt_sub hab).add (intervalIntegrable_inv_sqrt_sub_left hab)).const_mul _

lemma sqrtKernel_integrable {a b : ℝ} (hab : a<b) :
    IntervalIntegrable (sqrtKernel a b) volume a b := by
  apply (sqrtMajorant_integrable hab.le).mono_fun'
  · exact (((measurable_id.sub_const a).sqrt.inv).mul
      ((measurable_const.sub measurable_id).sqrt.inv)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le hab.le] at hs
    rw [Real.norm_eq_abs,abs_of_nonneg (sqrtKernel_nonneg a b s)]
    exact sqrtKernel_le_majorant hab ⟨hs.1.le,hs.2⟩

lemma sqrtKernel_integral_le_eight {a b : ℝ} (hab : a<b) :
    (∫ s in a..b, sqrtKernel a b s) ≤ 8 := by
  have hd := Real.sqrt_ne_zero'.mpr (sub_pos.mpr hab)
  calc
    _  ≤  ∫ s in a..b, sqrtMajorant a b s :=
      intervalIntegral.integral_mono_on hab.le (sqrtKernel_integrable hab)
        (sqrtMajorant_integrable hab.le) (fun s hs ↦ sqrtKernel_le_majorant hab hs)
    _ = (2/Real.sqrt (b-a))*(2*Real.sqrt (b-a)+2*Real.sqrt (b-a)) := by
      unfold sqrtMajorant
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
        (intervalIntegrable_inv_sqrt_sub hab.le) (intervalIntegrable_inv_sqrt_sub_left hab.le),
        integral_inv_sqrt_sub hab.le,integral_inv_sqrt_sub_left hab.le]
    _ = 8 := by field_simp; ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_WeightedCap
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set
namespace SKValue

lemma weightedCap_bddAbove {a b C : ℝ} {F : ℝ → ℝ → ℝ} (_ : a≤b)
    (_ : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) :
    BddAbove ((fun p : ℝ×ℝ ↦ Real.sqrt (b-p.1)*|F p.1 p.2|) '' (Icc a b ×ˢ univ)) := by
  refine ⟨Real.sqrt (b-a)*C,?_⟩
  rintro _ ⟨⟨t,x⟩,ht,rfl⟩
  exact mul_le_mul (Real.sqrt_le_sqrt (sub_le_sub_left ht.1.1 b)) (hF t ht.1 x)
    (abs_nonneg _) (Real.sqrt_nonneg _)

lemma le_weightedCap {a b C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) {t : ℝ} (ht : t∈Icc a b) (x : ℝ) :
    Real.sqrt (b-t)*|F t x|≤weightedCap a b F :=
  le_csSup (weightedCap_bddAbove hab hC hF) ⟨(t,x),⟨ht,mem_univ _⟩,rfl⟩

lemma weightedCap_nonneg {a b C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) : 0≤weightedCap a b F := by
  simpa only [sub_self,Real.sqrt_zero,zero_mul] using le_weightedCap hab hC hF ⟨hab,le_rfl⟩ 0

lemma abs_le_weightedCap_div {a b C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) {t : ℝ} (ht : t∈Ico a b) (x : ℝ) :
    |F t x|≤weightedCap a b F/Real.sqrt (b-t) := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (sub_pos.mpr ht.2))).mpr
  simpa only [mul_comm] using le_weightedCap hab hC hF ⟨ht.1,ht.2.le⟩ x

lemma weightedCap_le {a b A : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hF : ∀ t∈Icc a b, ∀ x, Real.sqrt (b-t)*|F t x|≤A) : weightedCap a b F≤A := by
  unfold weightedCap
  refine csSup_le ?_ ?_
  · exact ⟨Real.sqrt (b-a)*|F a 0|, ⟨(a,0),⟨⟨le_rfl,hab⟩,mem_univ _⟩,rfl⟩⟩
  · rintro _ ⟨⟨t,x⟩,ht,rfl⟩
    exact hF t ht.1 x

lemma weightedCap_absorb {a b A q C : ℝ} {F : ℝ → ℝ → ℝ} (hab : a≤b)
    (hC : 0≤C) (hF : ∀ t∈Icc a b, ∀ x, |F t x|≤C) (hq : q≤1/2)
    (h : ∀ t∈Icc a b, ∀ x, Real.sqrt (b-t)*|F t x|≤A+q*weightedCap a b F) :
    weightedCap a b F≤2*A := by
  have hb := weightedCap_nonneg hab hC hF
  have hc := weightedCap_le hab h
  nlinarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ParametricChain
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology NNReal ENNReal BigOperators Convex
namespace SKValue

theorem parametric_spatial_error
    {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u : E} {v w : α → E} {l : Filter α} (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    (s : Set E := Set.univ) (seg : ∀ᶠ χ in l, [w χ -[ℝ] v χ] ⊆ s := by simp)
    {f : α → E → F} {f' : α → E → E →L[𝕜] F}
    (df' : ∀ᶠ p in l ×ˢ 𝓝[s] u, HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2)
    {φ : E →L[𝕜] F} (cf' : Tendsto ↿f' (l ×ˢ 𝓝[s] u) (𝓝 φ)) :
    (fun χ => f χ (v χ) - f χ (w χ) - φ (v χ - w χ)) =o[l] (fun χ => v χ - w χ) := by
  rw [isLittleO_iff]
  intro ε hε
  replace df' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], HasFDerivWithinAt (f χ) (f' χ z) s z :=
    df'.segment_of_prod_nhdsWithin hw hv seg
  replace cf' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], ‖f' χ z - φ‖ < ε := by
    simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at cf'
    exact (cf' ε hε).segment_of_prod_nhdsWithin hw hv seg
  filter_upwards [seg, df', cf'] with χ seg df' cf'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (df' z hz).mono seg) (fun z hz => (cf' z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

lemma hasDerivAt_parametric_comp {f fx : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {t a b : ℝ}
    (hd : HasDerivAt (fun s ↦ f s (φ t)) a t) (hφ : HasDerivAt φ b t)
    (hx : ∀ᶠ p : ℝ×ℝ in 𝓝 (t,φ t), HasDerivAt (f p.1) (fx p.1 p.2) p.2)
    (hc : ContinuousAt (fun p : ℝ×ℝ ↦ fx p.1 p.2) (t,φ t)) :
    HasDerivAt (fun s ↦ f s (φ s)) (a+fx t (φ t)*b) t := by
  have hsp := parametric_spatial_error hφ.continuousAt tendsto_const_nhds
    (s := Set.univ) (seg := by simp) (f := f) (f' := fun s x ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (fx s x))
    (φ := (1 : ℝ →L[ℝ] ℝ).smulRight (fx t (φ t)))
    (df' := by
      rw [nhdsWithin_univ,←nhds_prod_eq]
      exact hx.mono (fun p hp ↦ hp.hasFDerivAt.hasFDerivWithinAt))
    (cf' := by
      rw [nhdsWithin_univ,←nhds_prod_eq]
      exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.continuousAt.comp hc)
  have hsmall := (hsp.trans_isBigO hφ.isBigO_sub).add
    (hd.isLittleO.add (hφ.isLittleO.const_mul_left (fx t (φ t))))
  apply HasDerivAt.of_isLittleO
  have heq : (fun s ↦ f s (φ s)-f s (φ t)-
      (1 : ℝ →L[ℝ] ℝ).smulRight (fx t (φ t)) (φ s-φ t) +
      ((f s (φ t)-f t (φ t)-(s-t) • a)+fx t (φ t)*(φ s-φ t-(s-t) • b))) =
      (fun s ↦ f s (φ s)-f t (φ t)-(s-t) • (a+fx t (φ t)*b)) := by
    funext s
    simp only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,smul_eq_mul]
    ring
  rw [heq] at hsmall
  exact hsmall

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolutionDifferentiation
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma SmoothEvolution.jet_joint_continuousOn {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) :
    ContinuousOn (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (V p.1)) p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  obtain ⟨L,hL,hl⟩ := h.jet_joint n
  have hh : LipschitzOnWith ⟨2*L,by positivity⟩
      (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (V p.1)) p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    simp only [Real.dist_eq,Prod.dist_eq]
    have hb := hl p.1 hp.1 q.1 hq.1 q.2 p.2
    change |iteratedDeriv n (deriv (V p.1)) p.2-iteratedDeriv n (deriv (V q.1)) q.2|≤
      (2*L)*max |p.1-q.1| |p.2-q.2|
    have hm1 := le_max_left |p.1-q.1| |p.2-q.2|
    have hm2 := le_max_right |p.1-q.1| |p.2-q.2|
    nlinarith
  exact hh.continuousOn

lemma SmoothEvolution.jet_joint_continuousAt {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) {t : ℝ} (ht : t∈Ioo (0 : ℝ) T) (x : ℝ) :
    ContinuousAt (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (V p.1)) p.2) (t,x) := by
  exact (h.jet_joint_continuousOn n (t,x) ⟨⟨ht.1.le,ht.2.le⟩,mem_univ x⟩).continuousAt
    (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem)

lemma SmoothEvolution.gradient_time_hasDerivAt {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) {t : ℝ} (ht : t∈Ioo (0 : ℝ) T)
    (hγ : ContinuousAt γ t) (x : ℝ) :
    HasDerivAt (fun s ↦ deriv (V s) x)
      (-((1/2 : ℝ)*deriv (deriv (deriv (V t))) x+γ t*(deriv (V t) x*deriv (deriv (V t)) x))) t := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (deriv (V r))) x+γ r*(deriv (V r) x*deriv (deriv (V r)) x)
  have hc0 : ContinuousOn (fun r ↦ deriv (V r) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_zero] using h.continuous_jet 0 x
  have hc1 : ContinuousOn (fun r ↦ deriv (deriv (V r)) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_one] using h.continuous_jet 1 x
  have hc2 : ContinuousOn (fun r ↦ deriv (deriv (deriv (V r))) x) (Icc (0 : ℝ) T) := by
    simpa only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
      using h.continuous_jet 2 x
  have hti : t∈Icc (0 : ℝ) T := ⟨ht.1.le,ht.2.le⟩
  have hn := Icc_mem_nhds ht.1 ht.2
  have hgc : ContinuousAt g t :=
    (continuousAt_const.mul ((hc2 t hti).continuousAt hn)).add
      (hγ.mul (((hc0 t hti).continuousAt hn).mul ((hc1 t hti).continuousAt hn)))
  have hgm : StronglyMeasurableAtFilter g (𝓝 t) volume := by
    refine ⟨Icc (0 : ℝ) T,hn,?_⟩
    exact (aestronglyMeasurable_const.mul (hc2.aestronglyMeasurable measurableSet_Icc)).add
      (hm.aestronglyMeasurable.mul ((hc0.aestronglyMeasurable measurableSet_Icc).mul
        (hc1.aestronglyMeasurable measurableSet_Icc)))
  have hd := (hasDerivAt_const t (deriv (V t) x)).sub
    (intervalIntegral.integral_hasDerivAt_right (a := t) (b := t) (by simp) hgm hgc)
  simp only [zero_sub] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with s hs
  have hh := h.gradient_pde t hti s hs x
  dsimp only [g,Pi.sub_apply] at *
  linarith

lemma SmoothEvolution.gradient_curve_hasDerivAt {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) {t : ℝ} (ht : t∈Ioo (0 : ℝ) T)
    (hγ : ContinuousAt γ t) {φ : ℝ → ℝ} {b : ℝ} (hφ : HasDerivAt φ b t) :
    HasDerivAt (fun s ↦ deriv (V s) (φ s))
      (-((1/2 : ℝ)*deriv (deriv (deriv (V t))) (φ t)+
        γ t*(deriv (V t) (φ t)*deriv (deriv (V t)) (φ t)))+deriv (deriv (V t)) (φ t)*b) t := by
  apply hasDerivAt_parametric_comp (h.gradient_time_hasDerivAt hm ht hγ (φ t)) hφ
  · have he : ∀ᶠ p : ℝ×ℝ in 𝓝 (t,φ t), p.1∈Icc (0 : ℝ) T :=
      continuousAt_fst.preimage_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    filter_upwards [he] with p hp
    exact ((h.slices p.1 hp).jets.smooth.differentiable
      (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) p.2).hasDerivAt
  · simpa only [iteratedDeriv_one] using h.jet_joint_continuousAt 1 ht (φ t)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma sqrt_difference_bound {δ u v : ℝ} (hδ : 0<δ) (hu : δ≤u) (hv : δ≤v) :
    |Real.sqrt u-Real.sqrt v|≤(Real.sqrt δ)⁻¹*|u-v| := by
  have hd := Real.sqrt_pos.mpr hδ
  have hu0 := hδ.le.trans hu
  have hv0 := hδ.le.trans hv
  have he : |u-v|=|Real.sqrt u-Real.sqrt v| * (Real.sqrt u+Real.sqrt v) := by
    rw [←abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),←abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hu0,Real.sq_sqrt hv0]
  have hh : Real.sqrt δ≤Real.sqrt u+Real.sqrt v := by
    linarith [Real.sqrt_le_sqrt hu,Real.sqrt_nonneg v]
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hd).mpr
  rw [he]
  exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)

lemma SmoothEvolution.heat_gradient_derivative_integral {T a t : ℝ} {γ : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V) (hm : Measurable γ)
    (ha : 0≤a) (hat : a<t) (ht : t<T) (hγ : ContinuousAt γ t) (x : ℝ) :
    HasDerivAt (fun s ↦ heat (s-a) (deriv (V s)) x)
      (∫ z, -((1/2 : ℝ)*deriv (deriv (deriv (V t))) (x+Real.sqrt (t-a)*z)+
        γ t*(deriv (V t) (x+Real.sqrt (t-a)*z)*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)))+
        deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a))) ∂standardGaussian) t := by
  let q := (a+t)/2
  have haq : a<q := by dsimp [q]; linarith
  have hqt : q<t := by dsimp [q]; linarith
  have hq0 : 0≤q := ha.trans haq.le
  have hti : t∈Icc (0 : ℝ) T := ⟨ha.trans hat.le,ht.le⟩
  have hψ := (h.slices t hti).jets
  let F := fun s z ↦ deriv (V s) (x+Real.sqrt (s-a)*z)
  let F' := fun z ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V t))) (x+Real.sqrt (t-a)*z)+
        γ t*(deriv (V t) (x+Real.sqrt (t-a)*z)*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)))+
        deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a)))
  obtain ⟨L,hL,hl⟩ := h.jet_joint 0
  simp only [iteratedDeriv_zero] at hl
  let bd := fun z : ℝ ↦ L*(1+(Real.sqrt (q-a))⁻¹*|z|)
  have hbd : Integrable bd standardGaussian := by
    exact ((integrable_const 1).add (((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs.const_mul _)).const_mul L
  have hfc0 : Continuous (deriv (V t)) := hψ.smooth.continuous
  have hfc1 : Continuous (deriv (deriv (V t))) := hψ.deriv.smooth.continuous
  have hfc2 : Continuous (deriv (deriv (deriv (V t)))) := hψ.deriv.deriv.smooth.continuous
  apply (hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (F' := F') (s := Icc q T) (bound := bd) (μ := standardGaussian)
    (Icc_mem_nhds hqt ht)
    (by
      filter_upwards [Icc_mem_nhds hqt ht] with s hs
      exact (((h.slices s ⟨hq0.trans hs.1,hs.2⟩).jets.smooth.continuous).comp (by fun_prop)).aestronglyMeasurable)
    (hψ.expGrowth.shift_integrable hψ.smooth.continuous.measurable x (Real.sqrt (t-a)))
    (by dsimp [F']; fun_prop) _ hbd _).2
  · filter_upwards [] with z
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs r hr
    have hb := hl s ⟨hq0.trans hs.1,hs.2⟩ r ⟨hq0.trans hr.1,hr.2⟩
      (x+Real.sqrt (r-a)*z) (x+Real.sqrt (s-a)*z)
    have hsr := sqrt_difference_bound (sub_pos.mpr haq)
      (show q - a ≤ s - a by linarith [hs.1]) (show q - a ≤ r - a by linarith [hr.1])
    rw [sub_sub_sub_cancel_right] at hsr
    have he : |(x+Real.sqrt (s-a)*z)-(x+Real.sqrt (r-a)*z)|=
        |Real.sqrt (s-a)-Real.sqrt (r-a)| * |z| := by rw [add_sub_add_left_eq_sub,←sub_mul,abs_mul]
    rw [he] at hb
    simp only [Real.dist_eq,Real.coe_nnabs]
    change |F s z-F r z|≤|bd z| * |s-r|
    have hbd0 : 0 ≤ bd z := by dsimp [bd]; positivity
    rw [abs_of_nonneg hbd0]
    dsimp only [F,bd]
    have hmul := mul_le_mul_of_nonneg_right hsr (abs_nonneg z)
    nlinarith
  · filter_upwards [] with z
    have hs := ((Real.hasDerivAt_sqrt (sub_pos.mpr hat).ne').comp t
      ((hasDerivAt_id t).sub_const a)).mul_const z
    have hφ := hs.const_add x
    convert! h.gradient_curve_hasDerivAt hm ⟨ha.trans_lt hat,ht⟩ hγ hφ using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [F,F']
    ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatKernelBound
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.iteratedDeriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (n : ℕ) :
    BoundedSmooth (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma BoundedSmooth.heat_deriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (h : ℝ) :
    _root_.deriv (heat h f)=heat h (_root_.deriv f) := by
  simpa only [iteratedDeriv_one] using heat_iteratedDeriv hf.smooth
    (fun n ↦ (hf.iteratedDeriv n).expGrowth) h 1

lemma standardGaussian_abs_integral_le_one : (∫ z : ℝ, |z| ∂standardGaussian)≤1 := by
  have hl : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) standardGaussian := HasLaw.id
  have hh := integral_abs_le_sqrt_integral_sq (gaussian_memLp hl 2 (by norm_num))
  rw [gaussian_second_moment hl,Real.sqrt_one] at hh
  exact hh

lemma BoundedSmooth.heat_kernel_deriv_bound {f : ℝ → ℝ} (hf : BoundedSmooth f)
    {A h : ℝ} (hA : 0≤A) (hb : ∀ x, |f x|≤A) (hh : 0<h) (x : ℝ) :
    |_root_.deriv (heat h f) x|≤A/Real.sqrt h := by
  have hs := Real.sqrt_pos.mpr hh
  have hid := gaussian_scale_deriv_eq
    (fun y ↦ (hf.smooth.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) y).hasDerivAt)
    hf.deriv.smooth.continuous hf.expGrowth hf.deriv.expGrowth x (Real.sqrt h)
  have hi := hf.expGrowth.shift_mul_integrable hf.smooth.continuous.measurable x (Real.sqrt h)
  have hz : Integrable (fun z : ℝ ↦ |z| * A) standardGaussian := by
    exact ((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs.mul_const A
  have hb' : |∫ z, z*f (x+Real.sqrt h*z) ∂standardGaussian|≤A := by
    calc
      _ ≤ ∫ z, |z*f (x+Real.sqrt h*z)| ∂standardGaussian := abs_integral_le_integral_abs
      _ ≤ ∫ z : ℝ, |z| * A ∂standardGaussian := by
        apply integral_mono_ae hi.abs hz
        filter_upwards [] with z
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)
      _ = (∫ z : ℝ, |z| ∂standardGaussian)*A := integral_mul_const _ _
      _ ≤ A := by nlinarith [standardGaussian_abs_integral_le_one]
  rw [hf.heat_deriv]
  apply (le_div_iff₀ hs).mpr
  rw [hid,abs_mul,abs_of_pos hs] at hb'
  exact (mul_comm _ _).trans_le hb'

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_BurgersDerivative
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma SmoothEvolution.heat_gradient_hasDerivAt {T a t : ℝ} {γ : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V) (hm : Measurable γ)
    (ha : 0≤a) (hat : a<t) (ht : t<T) (hγ : ContinuousAt γ t) (x : ℝ) :
    HasDerivAt (fun s ↦ heat (s-a) (deriv (V s)) x)
      (-γ t * heat (t-a) (fun y ↦ deriv (V t) y * deriv (deriv (V t)) y) x) t := by
  have hψ := (h.slices t ⟨ha.trans hat.le,ht.le⟩).jets
  have hid := gaussian_scale_deriv_eq
    (fun y ↦ (hψ.deriv.smooth.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) y).hasDerivAt)
    hψ.deriv.deriv.smooth.continuous hψ.deriv.expGrowth hψ.deriv.deriv.expGrowth x (Real.sqrt (t-a))
  have hI := hψ.deriv.deriv.expGrowth.shift_integrable
    hψ.deriv.deriv.smooth.continuous.measurable x (Real.sqrt (t-a))
  have hJ := (hψ.mul hψ.deriv).expGrowth.shift_integrable
    (hψ.smooth.continuous.mul hψ.deriv.smooth.continuous).measurable x (Real.sqrt (t-a))
  have hZ := hψ.deriv.expGrowth.shift_mul_integrable
    hψ.deriv.smooth.continuous.measurable x (Real.sqrt (t-a))
  have he : (∫ z, -((1/2 : ℝ)*deriv (deriv (deriv (V t))) (x+Real.sqrt (t-a)*z)+
        γ t*(deriv (V t) (x+Real.sqrt (t-a)*z)*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)))+
        deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a))) ∂standardGaussian) =
      -γ t * heat (t-a) (fun y ↦ deriv (V t) y * deriv (deriv (V t)) y) x := by
    have heq (z : ℝ) : deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a))) =
        (2*Real.sqrt (t-a))⁻¹*(z*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)) := by ring
    simp_rw [heq]
    have hadd := integral_add ((hI.const_mul (1/2 : ℝ)).add (hJ.const_mul (γ t))).neg (hZ.const_mul ((2*Real.sqrt (t-a))⁻¹))
    simp only [Pi.neg_apply,Pi.add_apply] at hadd
    rw [hadd,integral_neg,integral_add (hI.const_mul (1/2 : ℝ)) (hJ.const_mul (γ t))]
    simp only [integral_const_mul]
    rw [hid]
    dsimp only [heat]
    field_simp [(Real.sqrt_pos.mpr (sub_pos.mpr hat)).ne']
    ring
  rw [←he]
  exact h.heat_gradient_derivative_integral hm ha hat ht hγ x

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma heat_family_continuousOn {T : ℝ} {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ F p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ))
    (hC : 0≤C) (hb : ∀ t∈Icc (0 : ℝ) T, ∀ x, |F t x|≤C) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (F t) x) (Icc (0 : ℝ) T) := by
  apply continuousOn_of_dominated (bound := fun _ ↦ |C|) (μ := standardGaussian)
  · intro t ht
    have hct : Continuous (F t) := by
      have hh : ContinuousOn (F t) univ := hc.comp (continuous_const.prodMk continuous_id).continuousOn
        (MapsTo.prodMk (fun _ _ ↦ ht) (fun _ _ ↦ mem_univ _))
      simpa only [Function.comp_def,continuousOn_univ] using hh
    exact (hct.comp (by fun_prop)).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,abs_of_nonneg hC] using hb t ht (x+Real.sqrt (t-a)*z))
  · exact integrable_const |C|
  · filter_upwards [] with z
    exact hc.comp ((continuous_id.prodMk (by fun_prop)).continuousOn)
      (fun t ht ↦ ⟨ht,mem_univ _⟩)

lemma SmoothEvolution.heat_gradient_continuousOn {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (deriv (V t)) x) (Icc (0 : ℝ) T) := by
  obtain ⟨C,hC,hb⟩ := h.bound 0
  simpa only [iteratedDeriv_zero] using heat_family_continuousOn (h.jet_joint_continuousOn 0) hC hb a x

lemma SmoothEvolution.heat_gradient_lipschitzOn {T a q b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (ha : 0≤a) (haq : a<q) (hqb : q≤b) (hb : b≤T) (x : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (fun t ↦ heat (t-a) (deriv (V t)) x) (Icc q b) := by
  obtain ⟨L,hL,hl⟩ := h.jet_joint 0
  simp only [iteratedDeriv_zero] at hl
  let C := L*(1+(Real.sqrt (q-a))⁻¹)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨⟨C,hC⟩,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro s hs r hr
  have hsub : Icc q b ⊆ Icc (0 : ℝ) T :=
    (Icc_subset_Icc_iff hqb).mpr ⟨ha.trans haq.le,hb⟩
  have hsT : s∈Icc (0 : ℝ) T := hsub hs
  have hrT : r∈Icc (0 : ℝ) T := hsub hr
  have hi (u : ℝ) (hu : u∈Icc (0 : ℝ) T) :
      Integrable (fun z ↦ deriv (V u) (x+Real.sqrt (u-a)*z)) standardGaussian :=
    (h.slices u hu).jets.expGrowth.shift_integrable (h.slices u hu).jets.smooth.continuous.measurable x _
  have hz : Integrable (fun z : ℝ ↦ |z|) standardGaussian :=
    ((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs
  have hbd : Integrable (fun z : ℝ ↦ L*(|s-r|+(Real.sqrt (q-a))⁻¹*|s-r| * |z|)) standardGaussian :=
    ((integrable_const _).add (hz.const_mul _)).const_mul L
  have hd : |heat (s-a) (deriv (V s)) x-heat (r-a) (deriv (V r)) x|≤C*|s-r| := by
    unfold heat
    rw [←integral_sub (hi s hsT) (hi r hrT)]
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ z : ℝ, L*(|s-r|+(Real.sqrt (q-a))⁻¹*|s-r| * |z|) ∂standardGaussian := by
        apply integral_mono_ae ((hi s hsT).sub (hi r hrT)).abs hbd
        filter_upwards [] with z
        have hh := hl s hsT r hrT (x+Real.sqrt (r-a)*z) (x+Real.sqrt (s-a)*z)
        have he : |(x+Real.sqrt (s-a)*z)-(x+Real.sqrt (r-a)*z)|=
          |Real.sqrt (s-a)-Real.sqrt (r-a)| * |z| := by rw [add_sub_add_left_eq_sub,←sub_mul,abs_mul]
        rw [he] at hh
        have hsr := sqrt_difference_bound (sub_pos.mpr haq)
          (show q-a ≤ s-a by linarith [hs.1]) (show q-a ≤ r-a by linarith [hr.1])
        rw [sub_sub_sub_cancel_right] at hsr
        have hh' := mul_le_mul_of_nonneg_right hsr (abs_nonneg z)
        simp only [Pi.sub_apply]
        exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hh') hL)
      _ = L*(|s-r|+(Real.sqrt (q-a))⁻¹*|s-r| * (∫ z : ℝ, |z| ∂standardGaussian)) := by
        rw [integral_const_mul,integral_add (integrable_const _) (hz.const_mul _),integral_const,integral_const_mul]
        simp
      _ ≤ C*|s-r| := by
        have hh := mul_le_mul_of_nonneg_left standardGaussian_abs_integral_le_one
          (show 0≤L*((Real.sqrt (q-a))⁻¹*|s-r|) by positivity)
        dsimp [C]
        nlinarith
  change dist _ _ ≤ C*dist s r
  simpa only [Real.dist_eq] using hd

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BurgersMild
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma monotoneOn_ae_continuousAt_interior {T : ℝ} {γ : ℝ → ℝ}
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) :
    ∀ᵐ t : ℝ, t∈Ioo (0 : ℝ) T → ContinuousAt γ t := by
  filter_upwards [hγ.countable_not_continuousWithinAt.ae_notMem volume] with t ht hti
  have hc : ContinuousWithinAt γ (Icc (0 : ℝ) T) t := by
    by_contra hc
    exact ht ⟨⟨hti.1.le,hti.2.le⟩,hc⟩
  exact hc.continuousAt (Icc_mem_nhds hti.1 hti.2)

lemma SmoothEvolution.heat_nonlinearity_continuousOn {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (fun y ↦ deriv (V t) y*deriv (deriv (V t)) y) x)
      (Icc (0 : ℝ) T) := by
  obtain ⟨C,hC,hb⟩ := h.bound 0
  obtain ⟨D,hD,hd⟩ := h.bound 1
  simp only [iteratedDeriv_zero] at hb
  simp only [iteratedDeriv_one] at hd
  apply heat_family_continuousOn (C := C*D)
  · simpa only [iteratedDeriv_zero,iteratedDeriv_one,Pi.mul_def] using
      (h.jet_joint_continuousOn 0).mul (h.jet_joint_continuousOn 1)
  · positivity
  · intro t ht y
    rw [abs_mul]
    exact mul_le_mul (hb t ht y) (hd t ht y) (abs_nonneg _) hC

lemma SmoothEvolution.heat_gradient_interval {T a q b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (ha : 0≤a) (haq : a<q) (hqb : q≤b) (hb : b≤T) (x : ℝ) :
    heat (b-a) (deriv (V b)) x-heat (q-a) (deriv (V q)) x =
      -(∫ s in q..b, γ s*heat (s-a) (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x) := by
  obtain ⟨L,hL⟩ := h.heat_gradient_lipschitzOn ha haq hqb hb x
  have hL' : LipschitzOnWith L (fun t ↦ heat (t-a) (deriv (V t)) x) (uIcc q b) := by
    simpa only [uIcc_of_le hqb] using hL
  rw [←hL'.absolutelyContinuousOnInterval.integral_deriv_eq_sub,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [monotoneOn_ae_continuousAt_interior hγ,(Set.countable_singleton b).ae_notMem volume] with s hs hsb hsi
  rw [uIoc_of_le hqb] at hsi
  have hst : s<T := (lt_of_le_of_ne hsi.2 (by simpa only [mem_singleton_iff] using hsb)).trans_le hb
  have has : a < s := haq.trans hsi.1
  have hd := h.heat_gradient_hasDerivAt hm ha has hst (hs ⟨ha.trans_lt has,hst⟩) x
  simpa only [neg_mul] using hd.deriv

lemma SmoothEvolution.burgers_mild {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0≤a) (hab : a≤b) (hb : b≤T) (x : ℝ) :
    deriv (V a) x=heat (b-a) (deriv (V b)) x+
      ∫ s in a..b, γ s*heat (s-a) (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have haT : a∈Icc (0 : ℝ) T := ⟨ha,hab.le.trans hb⟩
  have hT : 0≤T := ha.trans haT.2
  let g := fun s ↦ γ s*heat (s-a) (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x
  have hg : IntervalIntegrable g volume a b := by
    apply (hi.mono_set ?_).mul_continuousOn
    · simpa only [uIcc_of_le hab.le] using
        (h.heat_nonlinearity_continuousOn a x).mono (Icc_subset_Icc ha hb)
    · simp only [uIcc_of_le hab.le,uIcc_of_le hT]
      exact Icc_subset_Icc ha hb
  have hF : Tendsto (fun q ↦ heat (q-a) (deriv (V q)) x) (𝓝[>] a) (𝓝 (deriv (V a) x)) := by
    have hh := (h.heat_gradient_continuousOn a x a haT).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hab) (fun s hs ↦ ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩))
    simpa only [sub_self,heat_zero] using hh.tendsto
  have hI : Tendsto (fun q ↦ ∫ s in q..b, g s) (𝓝[>] a) (𝓝 (∫ s in a..b, g s)) := by
    have hgI : IntegrableOn g (uIcc a b) volume := (intervalIntegrable_iff').mp hg
    have hh := (intervalIntegral.continuousOn_primitive_interval_left hgI a
      (by simp only [uIcc_of_le hab.le]; exact ⟨le_rfl,hab.le⟩)).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hab) (by intro s hs; simpa only [uIcc_of_le hab.le] using ⟨hs.1.le,hs.2.le⟩))
    exact hh.tendsto
  have he : (fun q ↦ heat (q-a) (deriv (V q)) x) =ᶠ[𝓝[>] a]
      (fun q ↦ heat (b-a) (deriv (V b)) x+∫ s in q..b, g s) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with q hq
    have hh := h.heat_gradient_interval hm hγ ha hq.1 hq.2.le hb x
    change _ = -(∫ s in q..b, g s) at hh
    linarith
  exact tendsto_nhds_unique hF ((tendsto_const_nhds.add hI).congr' he.symm)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_SmoothFamily
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.gradient_family {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) : BoundedSmoothFamily T (fun t ↦ deriv (V t)) :=
  ⟨fun t ht ↦ (h.slices t ht).jets,h.bound,h.jet_joint_continuousOn⟩

lemma BoundedSmoothFamily.deriv {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) : BoundedSmoothFamily T (fun t ↦ _root_.deriv (F t)) := by
  refine ⟨fun t ht ↦ (h.slices t ht).deriv,?_,?_⟩
  · intro n
    simpa only [iteratedDeriv_succ'] using h.bound (n+1)
  · intro n
    simpa only [iteratedDeriv_succ'] using h.joint (n+1)

lemma BoundedSmoothFamily.mul {T : ℝ} {F G : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily T F) (hG : BoundedSmoothFamily T G) :
    BoundedSmoothFamily T (fun t x ↦ F t x*G t x) := by
  classical
  have hid (n : ℕ) (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
      iteratedDeriv n (fun x ↦ F t x*G t x) x =
      ∑ i∈Finset.range (n+1), (n.choose i : ℝ)*iteratedDeriv i (F t) x*iteratedDeriv (n-i) (G t) x := by
    rw [iteratedDeriv_fun_mul
      ((hF.slices t ht).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
      ((hG.slices t ht).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
  refine ⟨fun t ht ↦ (hF.slices t ht).mul (hG.slices t ht),?_,?_⟩
  · intro n
    choose A hA hFA using hF.bound
    choose B hB hGB using hG.bound
    refine ⟨∑ i∈Finset.range (n+1), (n.choose i : ℝ)*A i*B (n-i),?_,?_⟩
    · exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _))
    · intro t ht x
      rw [hid n t ht x]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose i))]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFA i t ht x) (Nat.cast_nonneg _)) (hGB (n-i) t ht x)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
  · intro n
    apply ContinuousOn.congr (f := fun p : ℝ×ℝ ↦ ∑ i∈Finset.range (n+1),
      (n.choose i : ℝ)*iteratedDeriv i (F p.1) p.2*iteratedDeriv (n-i) (G p.1) p.2)
    · apply continuousOn_finsetSum
      intro i _
      simpa only [Pi.mul_def] using (continuousOn_const.mul (hF.joint i)).mul (hG.joint (n-i))
    · intro p hp
      exact hid n p.1 hp.1 p.2

lemma BoundedSmoothFamily.heat_continuousOn {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (F t) x) (Icc (0 : ℝ) T) := by
  obtain ⟨C,hC,hb⟩ := h.bound 0
  simpa only [iteratedDeriv_zero] using heat_family_continuousOn (h.joint 0) hC hb a x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_DuhamelJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmoothFamily.duhamel_hasDerivAt {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) (x : ℝ) :
    HasDerivAt (duhamel a b γ F) (duhamel a b γ (fun t ↦ _root_.deriv (F t)) x) x := by
  have hfi (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*heat (s-a) (F s) u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.heat_continuousOn a u).mono (Icc_subset_Icc ha hb)
  have hf'i (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*heat (s-a) (_root_.deriv (F s)) u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.deriv.heat_continuousOn a u).mono (Icc_subset_Icc ha hb)
  obtain ⟨C,hC,hbd⟩ := h.bound 1
  simp only [iteratedDeriv_one] at hbd
  have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u s ↦ γ s*heat (s-a) (F s) u)
    (F' := fun u s ↦ γ s*heat (s-a) (_root_.deriv (F s)) u)
    (s := univ) (bound := fun s ↦ |γ s| * C) (μ := volume.restrict (Ioc a b))
    univ_mem (Eventually.of_forall (fun u ↦ ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi u)).aestronglyMeasurable))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi x))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hf'i x)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (heat_bound hC (hbd s ⟨ha.trans hs.1.le,hs.2.trans hb⟩) _ u) (abs_nonneg _))
    (hi'.abs.mul_const C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      have hfs := h.slices s ⟨ha.trans hs.1.le,hs.2.trans hb⟩
      exact (heat_spatial_hasDerivAt
        (fun y ↦ (hfs.smooth.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) y).hasDerivAt)
        hfs.deriv.smooth.continuous hfs.expGrowth hfs.deriv.expGrowth u (s-a)).const_mul (γ s))
  change HasDerivAt (fun u ↦ ∫ s in a..b, γ s*heat (s-a) (F s) u)
    (∫ s in a..b, γ s*heat (s-a) (_root_.deriv (F s)) x) x
  simpa only [intervalIntegral.integral_of_le hab] using hd.2

lemma BoundedSmoothFamily.duhamel_deriv {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) :
    _root_.deriv (duhamel a b γ F)=duhamel a b γ (fun t ↦ _root_.deriv (F t)) := by
  funext x
  exact (h.duhamel_hasDerivAt hi ha hab hb x).deriv

lemma BoundedSmoothFamily.iteratedDeriv {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (n : ℕ) :
    BoundedSmoothFamily T (fun t ↦ iteratedDeriv n (F t)) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma BoundedSmoothFamily.duhamel_iteratedDeriv {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) (n : ℕ) :
    _root_.iteratedDeriv n (duhamel a b γ F)=duhamel a b γ (fun t ↦ _root_.iteratedDeriv n (F t)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih,(h.iteratedDeriv n).duhamel_deriv hi ha hab hb]
    simp only [iteratedDeriv_succ]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_MildBurgersJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.heat_iteratedDeriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (h : ℝ) (n : ℕ) :
    _root_.iteratedDeriv n (heat h f)=heat h (_root_.iteratedDeriv n f) :=
  SKValue.heat_iteratedDeriv hf.smooth (fun n ↦ (hf.iteratedDeriv n).expGrowth) h n

lemma SmoothEvolution.burgers_jet_mild {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0≤a) (hab : a≤b) (hb : b≤T) (m : ℕ) :
    iteratedDeriv (m+1) (deriv (V a)) =
      fun x ↦ deriv (heat (b-a) (iteratedDeriv m (deriv (V b)))) x+
        ∫ s in a..b, γ s*deriv (heat (s-a) (iteratedDeriv m
          (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y))) x := by
  have haT : a∈Icc (0 : ℝ) T := ⟨ha,hab.trans hb⟩
  have hbT : b∈Icc (0 : ℝ) T := ⟨ha.trans hab,hb⟩
  have hiab : IntervalIntegrable γ volume a b := hi.mono_set (by
    simp only [uIcc_of_le hab,uIcc_of_le (ha.trans (hab.trans hb))]
    exact Icc_subset_Icc ha hb)
  have hF := h.gradient_family.mul h.gradient_family.deriv
  have hid : deriv (V a)=fun x ↦ heat (b-a) (deriv (V b)) x+
      duhamel a b γ (fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y) x :=
    funext (h.burgers_mild hm hγ hi ha hab hb)
  have hdD (n : ℕ) : Differentiable ℝ (iteratedDeriv n
      (duhamel a b γ (fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y))) := by
    rw [hF.duhamel_iteratedDeriv hiab ha hab hb]
    exact fun x ↦ ((hF.iteratedDeriv n).duhamel_hasDerivAt hiab ha hab hb x).differentiableAt
  have hcD : ContDiff ℝ ∞ (duhamel a b γ (fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y)) :=
    (contDiff_iff_iteratedDeriv).mpr ⟨fun n _ ↦ (hdD n).continuous,fun n _ ↦ hdD n⟩
  have hfb := (h.slices b hbT).jets
  have hcH := SKValue.heat_contDiff hfb.smooth (fun n ↦ (hfb.iteratedDeriv n).expGrowth) (b-a)
  have horder := ENat.natCast_le_of_coe_top_le_withTop le_rfl (m+1)
  rw [hid]
  funext x
  rw [iteratedDeriv_fun_add (hcH.of_le horder).contDiffAt (hcD.of_le horder).contDiffAt]
  rw [hfb.heat_iteratedDeriv,hF.duhamel_iteratedDeriv hiab ha hab hb]
  rw [iteratedDeriv_succ,←(hfb.iteratedDeriv m).heat_deriv]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hab] at hs
  have hsT : s∈Icc (0 : ℝ) T := ⟨ha.trans hs.1,hs.2.trans hb⟩
  dsimp only
  rw [iteratedDeriv_succ,←((hF.slices s hsT).iteratedDeriv m).heat_deriv]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_ShortStrip
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.jet_mild_bound {T a b Γ A K : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0≤a) (hab : a<b) (hb : b≤T) (m : ℕ)
    (hΓ : 0≤Γ) (hA : 0≤A) (hK : 0≤K)
    (hγbd : ∀ s∈Icc a b, |γ s|≤Γ)
    (hprev : ∀ s∈Icc a b, ∀ x, |iteratedDeriv m (deriv (V s)) x|≤A)
    (hprod : ∀ s∈Icc a b, ∀ x,
      |iteratedDeriv m (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x|≤
        |iteratedDeriv (m+1) (deriv (V s)) x|+K)
    {t : ℝ} (ht : t∈Ico a b) (x : ℝ) :
    |iteratedDeriv (m+1) (deriv (V t)) x|≤A/Real.sqrt (b-t)+
      Γ*(8*weightedCap a b (fun s ↦ iteratedDeriv (m+1) (deriv (V s)))+2*K*Real.sqrt (b-t)) := by
  let F := fun s ↦ iteratedDeriv (m+1) (deriv (V s))
  let R := weightedCap a b F
  obtain ⟨C,hC,hbd⟩ := h.bound (m+1)
  have hbd' : ∀ s∈Icc a b, ∀ y, |F s y|≤C := fun s hs y ↦ hbd s ⟨ha.trans hs.1,hs.2.trans hb⟩ y
  have hR : 0≤R := weightedCap_nonneg hab.le hC hbd'
  have habT : b∈Icc (0 : ℝ) T := ⟨ha.trans hab.le,hb⟩
  have htT : t∈Icc (0 : ℝ) T := ⟨ha.trans ht.1,ht.2.le.trans hb⟩
  let G := fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y
  let H := fun s ↦ γ s*deriv (heat (s-t) (iteratedDeriv m (G s))) x
  let J := fun s ↦ Γ*(R*sqrtKernel t b s+K*(Real.sqrt (s-t))⁻¹)
  have hg := h.gradient_family.mul h.gradient_family.deriv
  have hi' : IntervalIntegrable γ volume t b := hi.mono_set (by
    simp only [uIcc_of_le ht.2.le,uIcc_of_le (ha.trans (hab.le.trans hb))]
    exact Icc_subset_Icc htT.1 hb)
  have hHi : IntervalIntegrable H volume t b := by
    have hh := hi'.mul_continuousOn (show ContinuousOn
        (fun s ↦ heat (s-t) (iteratedDeriv (m+1) (G s)) x) (uIcc t b) from by
      simpa only [uIcc_of_le ht.2.le] using
        ((hg.iteratedDeriv (m+1)).heat_continuousOn t x).mono (Icc_subset_Icc htT.1 hb))
    apply hh.congr
    intro s hs
    rw [uIoc_of_le ht.2.le] at hs
    have hsT : s∈Icc (0 : ℝ) T := ⟨htT.1.trans hs.1.le,hs.2.trans hb⟩
    dsimp only [H,G]
    rw [iteratedDeriv_succ, ((hg.slices s hsT).iteratedDeriv m).heat_deriv]
  have hJi : IntervalIntegrable J volume t b :=
    (((sqrtKernel_integrable ht.2).const_mul R).add
      ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul K)).const_mul Γ
  have hpoint (s : ℝ) (hs : s∈Ioo t b) : |H s|≤J s := by
    have hsab : s∈Ico a b := ⟨ht.1.trans hs.1.le,hs.2⟩
    have hsT : s∈Icc (0 : ℝ) T := ⟨ha.trans hsab.1,hs.2.le.trans hb⟩
    have hspos := Real.sqrt_pos.mpr (sub_pos.mpr hs.1)
    have hsbpos := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
    have hf := ((hg.slices s hsT).iteratedDeriv m).heat_kernel_deriv_bound
      (A := R/Real.sqrt (b-s)+K) (by positivity)
      (fun y ↦ (hprod s ⟨hsab.1,hsab.2.le⟩ y).trans
        (add_le_add (abs_le_weightedCap_div hab.le hC hbd' hsab y) le_rfl))
      (sub_pos.mpr hs.1) x
    dsimp only [H]
    rw [abs_mul]
    apply (mul_le_mul (hγbd s ⟨hsab.1,hsab.2.le⟩) hf (abs_nonneg _) hΓ).trans_eq
    dsimp only [J,sqrtKernel]
    ring
  have hint : |∫ s in t..b, H s|≤Γ*(8*R+2*K*Real.sqrt (b-t)) := by
    calc
      _ ≤ ∫ s in t..b, |H s| := intervalIntegral.abs_integral_le_integral_abs ht.2.le
      _ ≤ ∫ s in t..b, J s := intervalIntegral.integral_mono_on_of_le_Ioo ht.2.le hHi.abs hJi hpoint
      _ = Γ*(R*(∫ s in t..b, sqrtKernel t b s)+K*(2*Real.sqrt (b-t))) := by
        dsimp only [J]
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
          ((sqrtKernel_integrable ht.2).const_mul R) ((intervalIntegrable_inv_sqrt_sub ht.2.le).const_mul K),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_inv_sqrt_sub ht.2.le]
      _ ≤ Γ*(R*8+K*(2*Real.sqrt (b-t))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
          (sqrtKernel_integral_le_eight ht.2) hR) le_rfl) hΓ
      _ = _ := by ring
  have hterm := ((h.slices b habT).jets.iteratedDeriv m).heat_kernel_deriv_bound hA
    (hprev b ⟨hab.le,le_rfl⟩) (sub_pos.mpr ht.2) x
  have hid := congrFun (h.burgers_jet_mild hm hγ hi htT.1 ht.2.le hb m) x
  change F t x=_+(∫ s in t..b, H s) at hid
  change |F t x|≤A/Real.sqrt (b-t)+Γ*(8*R+2*K*Real.sqrt (b-t))
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hterm hint)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ShortStripClose
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma weighted_bound_algebra {a b t A Γ K R D : ℝ} (ht : t∈Ico a b)
    (hΓ : 0 ≤ Γ) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hD : D ≤ A/Real.sqrt (b-t)+Γ*(8*R+2*K*Real.sqrt (b-t))) :
    Real.sqrt (b-t)*D ≤ (A+2*Γ*K*(b-a))+(8*Γ*Real.sqrt (b-a))*R := by
  have hs := Real.sqrt_pos.mpr (sub_pos.mpr ht.2)
  calc
    _  ≤  Real.sqrt (b-t)*(A/Real.sqrt (b-t)+Γ*(8*R+2*K*Real.sqrt (b-t))) :=
      mul_le_mul_of_nonneg_left hD hs.le
    _ = A+2*Γ*K*(b-t)+(8*Γ*Real.sqrt (b-t))*R := by
      rw [mul_add,mul_comm (Real.sqrt (b-t)) (A/Real.sqrt (b-t)),div_mul_cancel₀ _ hs.ne']
      ring_nf
      rw [Real.sq_sqrt (sub_nonneg.mpr ht.2.le)]
      ring
    _  ≤  _ := by
      have hr := Real.sqrt_le_sqrt (sub_le_sub_left ht.1 b)
      have h1 := mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 b) (by positivity : 0 ≤ 2*Γ*K)
      have h2 := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 8*Γ*R)
      nlinarith

lemma SmoothEvolution.short_strip_jet_bound {T a b Γ A K : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0 ≤ a) (hab : a<b) (hb : b ≤ T) (m : ℕ)
    (hΓ : 0 ≤ Γ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hγbd : ∀ s∈Icc a b, |γ s| ≤ Γ)
    (hprev : ∀ s∈Icc a b, ∀ x, |iteratedDeriv m (deriv (V s)) x| ≤ A)
    (hprod : ∀ s∈Icc a b, ∀ x,
      |iteratedDeriv m (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x| ≤
        |iteratedDeriv (m+1) (deriv (V s)) x|+K)
    (hshort : 8*Γ*Real.sqrt (b-a) ≤ 1/2) (x : ℝ) :
    |iteratedDeriv (m+1) (deriv (V a)) x| ≤ 2*(A+2*Γ*K*(b-a))/Real.sqrt (b-a) := by
  let F := fun s ↦ iteratedDeriv (m+1) (deriv (V s))
  obtain ⟨C,hC,hbd⟩ := h.bound (m+1)
  have hbd' : ∀ s∈Icc a b, ∀ y, |F s y| ≤ C := fun s hs y ↦ hbd s ⟨ha.trans hs.1,hs.2.trans hb⟩ y
  have hR := weightedCap_nonneg hab.le hC hbd'
  have hcap : weightedCap a b F ≤ 2*(A+2*Γ*K*(b-a)) := by
    apply weightedCap_absorb hab.le hC hbd' hshort
    intro t ht y
    rcases ht.2.eq_or_lt with rfl | htb
    · simp only [sub_self,Real.sqrt_zero,zero_mul]
      positivity
    · exact weighted_bound_algebra ⟨ht.1,htb⟩ hΓ hK hR
        (h.jet_mild_bound hm hγ hi ha hab hb m hΓ hA hK hγbd hprev hprod ⟨ht.1,htb⟩ y)
  apply (abs_le_weightedCap_div hab.le hC hbd' ⟨le_rfl,hab⟩ x).trans
  exact div_le_div_of_nonneg_right hcap (Real.sqrt_nonneg _)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma lowerJetConstant_nonneg (m : ℕ) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ lowerJetConstant m A := by
  unfold lowerJetConstant
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA) hA)

lemma SmoothTerminal.product_jet_bound {f : ℝ → ℝ} (hf : SmoothTerminal f)
    (m : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ k ≤ m, ∀ x, |iteratedDeriv k (deriv f) x| ≤ A) (x : ℝ) :
    |iteratedDeriv m (fun y ↦ deriv f y*deriv (deriv f) y) x| ≤
      |iteratedDeriv (m+1) (deriv f) x|+lowerJetConstant m A := by
  have horder := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  rw [iteratedDeriv_fun_mul (hf.jets.smooth.of_le horder).contDiffAt
    (hf.jets.deriv.smooth.of_le horder).contDiffAt,Finset.sum_range_succ']
  have hstep (n : ℕ) : iteratedDeriv n (deriv (deriv f))=iteratedDeriv (n+1) (deriv f) :=
    (iteratedDeriv_succ').symm
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,iteratedDeriv_zero,Nat.sub_zero,hstep]
  apply (abs_add_le _ _).trans
  have hfirst : |deriv f x*iteratedDeriv (m+1) (deriv f) x| ≤
      |iteratedDeriv (m+1) (deriv f) x| := by
    rw [abs_mul]
    have hgrad := norm_deriv_le_of_lipschitz hf.lipschitz (x₀ := x)
    simp only [Real.norm_eq_abs,NNReal.coe_one] at hgrad
    nlinarith [abs_nonneg (iteratedDeriv (m+1) (deriv f) x)]
  have hrest : |∑ i∈Finset.range m, (m.choose (i+1) : ℝ)*iteratedDeriv (i+1) (deriv f) x*
      iteratedDeriv (m-(i+1)+1) (deriv f) x| ≤ lowerJetConstant m A := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (m.choose (i+1)))]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hb (i+1) (by omega) x) (Nat.cast_nonneg _))
      (hb (m-(i+1)+1) (by omega) x) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
  exact (add_le_add hrest hfirst).trans_eq (add_comm _ _)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma exists_short_length {Γ d : ℝ} (hΓ : 0 ≤ Γ) (hd : 0<d) :
    ∃ δ : ℝ, 0<δ ∧ δ ≤ d ∧ 8*Γ*Real.sqrt δ ≤ 1/2 := by
  let e := min (1 : ℝ) (min d (1/(16*(Γ+1))))
  have hden : 0<16*(Γ+1) := by positivity
  have he : 0<e := lt_min zero_lt_one (lt_min hd (one_div_pos.mpr hden))
  have he1 : e ≤ 1 := min_le_left _ _
  have hed : e ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hei : e ≤ 1/(16*(Γ+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hei' := (le_div_iff₀ hden).mp hei
  refine ⟨e^2,sq_pos_of_pos he,?_,?_⟩
  · nlinarith
  · rw [Real.sqrt_sq he.le]
    nlinarith

theorem uniform_bulk_jets (Γ : ℝ) (hΓ : 0 ≤ Γ) (T : ℝ) (m : ℕ) :
    ∀ S : ℝ, 0 ≤ S → S<T → ∃ A : ℝ, 0 ≤ A ∧
      ∀ (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ), SmoothEvolution T γ V → Measurable γ →
        MonotoneOn γ (Icc (0 : ℝ) T) → (∀ t∈Icc (0 : ℝ) T, |γ t| ≤ Γ) →
        ∀ t∈Icc (0 : ℝ) S, ∀ k ≤ m, ∀ x, |iteratedDeriv k (deriv (V t)) x| ≤ A := by
  induction m with
  | zero =>
    intro S hS hST
    refine ⟨1,by norm_num,?_⟩
    intro γ V h hm hmono hbd t ht k hk x
    have hk' : k=0 := by omega
    subst k
    simpa only [iteratedDeriv_zero] using h.deriv_bound ⟨ht.1,ht.2.trans hST.le⟩ x
  | succ m ih =>
    intro S hS hST
    let S' := (S+T)/2
    have hSS' : S<S' := by dsimp only [S']; linarith
    have hS'T : S'<T := by dsimp only [S']; linarith
    obtain ⟨A,hA,hAall⟩ := ih S' (hS.trans hSS'.le) hS'T
    obtain ⟨δ,hδ,hδgap,hshort⟩ := exists_short_length hΓ (sub_pos.mpr hSS')
    let K := lowerJetConstant m A
    have hK : 0 ≤ K := lowerJetConstant_nonneg m hA
    let B := 2*(A+2*Γ*K*δ)/Real.sqrt δ
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    refine ⟨max A B,le_max_of_le_left hA,?_⟩
    intro γ V h hm hmono hbd t ht k hk x
    have hprev := hAall γ V h hm hmono hbd
    by_cases hkm : k ≤ m
    · exact (hprev t ⟨ht.1,ht.2.trans hSS'.le⟩ k hkm x).trans (le_max_left _ _)
    · have hk' : k=m+1 := by omega
      subst k
      have htδ : t<t+δ := by linarith
      have htδS' : t+δ ≤ S' := by linarith [ht.2]
      have hi : IntervalIntegrable γ volume 0 T := by
        apply MonotoneOn.intervalIntegrable
        simpa only [uIcc_of_le (hS.trans hST.le)] using hmono
      have hh := h.short_strip_jet_bound hm hmono hi ht.1 htδ (htδS'.trans hS'T.le) m
        hΓ hA hK
        (fun s hs ↦ hbd s ⟨ht.1.trans hs.1,hs.2.trans (htδS'.trans hS'T.le)⟩)
        (fun s hs y ↦ hprev s ⟨ht.1.trans hs.1,hs.2.trans htδS'⟩ m le_rfl y)
        (fun s hs y ↦ (h.slices s ⟨ht.1.trans hs.1,hs.2.trans (htδS'.trans hS'T.le)⟩).product_jet_bound
          m hA (fun j hj z ↦ hprev s ⟨ht.1.trans hs.1,hs.2.trans htδS'⟩ j hj z) y)
        (by simpa only [add_sub_cancel_left] using hshort) x
      have hh' : |iteratedDeriv (m+1) (deriv (V t)) x| ≤ B := by
        simpa only [add_sub_cancel_left] using hh
      exact hh'.trans (le_max_right _ _)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatTimeBound
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmooth.heat_time_bound {f : ℝ → ℝ} (hf : BoundedSmooth f) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, |_root_.deriv (_root_.deriv f) x| ≤ C) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    |heat h f x-f x| ≤ (C/2)*h := by
  have hd (r : ℝ) (hr : r∈Ioi (0 : ℝ)) :
      HasDerivAt (fun r ↦ heat r f x) ((1/2 : ℝ)*heat r (_root_.deriv (_root_.deriv f)) x) r :=
    heat_time_hasDerivAt
      (fun y ↦ (hf.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne' y).hasDerivAt)
      (fun y ↦ (hf.deriv.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne' y).hasDerivAt)
      hf.deriv.deriv.smooth.continuous hf.expGrowth hf.deriv.expGrowth hf.deriv.deriv.expGrowth x hr
  have hl : LipschitzOnWith ⟨C/2,by positivity⟩ (fun r ↦ heat r f x) (Ioi (0 : ℝ)) := by
    apply (convex_Ioi (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r hr ↦ (hd r hr).hasDerivWithinAt)
    intro r hr
    have hh := heat_bound hC hb r x
    have habs : |(1/2 : ℝ)*heat r (_root_.deriv (_root_.deriv f)) x| ≤ C/2 := by
      rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
      linarith
    exact_mod_cast habs
  have hc : Continuous (fun r ↦ heat r f x) :=
    (heat_continuous hf.smooth.continuous hf.expGrowth).comp (continuous_id.prodMk continuous_const)
  have hl' := LipschitzOnWith.closure hc.continuousOn hl
  rw [closure_Ioi] at hl'
  have hb' := hl'.dist_le_mul h (show h∈Ici (0 : ℝ) from hh) 0 (show (0 : ℝ)∈Ici 0 from (by simp))
  change dist (heat h f x) (heat 0 f x) ≤ (C/2)*dist h 0 at hb'
  simpa only [Real.dist_eq,heat_zero,sub_zero,abs_of_nonneg hh] using hb'

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.burgers_all_jets {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (deriv (V a)) x=heat (b-a) (iteratedDeriv n (deriv (V b))) x+
      ∫ s in a..b, γ s*heat (s-a) (iteratedDeriv n
        (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y)) x := by
  cases n with
  | zero => simpa only [iteratedDeriv_zero] using h.burgers_mild hm hγ hi ha hab hb x
  | succ m =>
    rw [congrFun (h.burgers_jet_mild hm hγ hi ha hab hb m) x]
    have hbT : b∈Icc (0 : ℝ) T := ⟨ha.trans hab,hb⟩
    rw [((h.slices b hbT).jets.iteratedDeriv m).heat_deriv,iteratedDeriv_succ]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hsT : s∈Icc (0 : ℝ) T := ⟨ha.trans hs.1,hs.2.trans hb⟩
    have hg := ((h.slices s hsT).jets.mul (h.slices s hsT).jets.deriv).iteratedDeriv m
    dsimp only
    rw [hg.heat_deriv,iteratedDeriv_succ]

lemma SmoothEvolution.temporal_jet_bound {T S Γ A : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (hST : S ≤ T) (n : ℕ) (hΓ : 0 ≤ Γ) (hA : 0 ≤ A)
    (hγbd : ∀ t∈Icc (0 : ℝ) S, |γ t| ≤ Γ)
    (hjets : ∀ t∈Icc (0 : ℝ) S, ∀ k ≤ n+2, ∀ x, |iteratedDeriv k (deriv (V t)) x| ≤ A)
    {a b : ℝ} (ha : a∈Icc (0 : ℝ) S) (hb : b∈Icc (0 : ℝ) S) (hab : a ≤ b) (x : ℝ) :
    |iteratedDeriv n (deriv (V a)) x-iteratedDeriv n (deriv (V b)) x| ≤
      (A/2+Γ*(A+lowerJetConstant n A))*(b-a) := by
  let G := fun s y ↦ deriv (V s) y*deriv (deriv (V s)) y
  let K := A+lowerJetConstant n A
  have hK : 0 ≤ K := add_nonneg hA (lowerJetConstant_nonneg n hA)
  have hG (s : ℝ) (hs : s∈Icc a b) (y : ℝ) : |iteratedDeriv n (G s) y| ≤ K := by
    have hsS : s∈Icc (0 : ℝ) S := ⟨ha.1.trans hs.1,hs.2.trans hb.2⟩
    apply ((h.slices s ⟨hsS.1,hsS.2.trans hST⟩).product_jet_bound n hA
      (fun k hk z ↦ hjets s hsS k (by omega) z) y).trans
    exact add_le_add (hjets s hsS (n+1) (by omega) y) le_rfl
  have hint : |∫ s in a..b, γ s*heat (s-a) (iteratedDeriv n (G s)) x| ≤ Γ*K*(b-a) := by
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := Γ*K) (f := fun s ↦ γ s*heat (s-a) (iteratedDeriv n (G s)) x) (by
        intro s hs
        rw [uIoc_of_le hab] at hs
        have hsS : s∈Icc (0 : ℝ) S := ⟨ha.1.trans hs.1.le,hs.2.trans hb.2⟩
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul (hγbd s hsS) (heat_bound hK (hG s ⟨hs.1.le,hs.2⟩) (s-a) x)
          (abs_nonneg _) hΓ)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),Real.dist_eq] using hbnd
  have hterm := ((h.slices b ⟨hb.1,hb.2.trans hST⟩).jets.iteratedDeriv n).heat_time_bound hA
    (fun y ↦ by simpa only [iteratedDeriv_succ,iteratedDeriv_succ'] using hjets b hb (n+2) le_rfl y)
    (sub_nonneg.mpr hab) x
  have hid := h.burgers_all_jets hm hγ hi ha.1 hab (hb.2.trans hST) n x
  rw [hid]
  rw [add_sub_right_comm]
  exact (abs_add_le _ _).trans ((add_le_add hterm hint).trans_eq (by ring))

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma SmoothEvolution.restrict {T S : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hST : S ≤ T) : SmoothEvolution S γ V := by
  have hs : Icc (0 : ℝ) S⊆Icc (0 : ℝ) T := Icc_subset_Icc le_rfl hST
  refine ⟨fun t ht ↦ h.slices t (hs ht),fun x ↦ (h.continuous_value x).mono hs,
    fun n x ↦ (h.continuous_jet n x).mono hs,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := h.bound n
    exact ⟨C,hC,fun t ht ↦ hb t (hs ht)⟩
  · intro n
    obtain ⟨L,hL,hb⟩ := h.temporal n
    exact ⟨L,hL,fun s hs' t ht ↦ hb s (hs hs') t (hs ht)⟩
  · exact fun t ht s hs' ↦ h.value_pde t (hs ht) s (hs hs')
  · exact fun t ht s hs' ↦ h.gradient_pde t (hs ht) s (hs hs')

lemma SmoothEvolution.uniform_temporal_jet {T S Γ A : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) (hγ : MonotoneOn γ (Icc (0 : ℝ) T))
    (hi : IntervalIntegrable γ volume 0 T) (hST : S ≤ T) (n : ℕ) (hΓ : 0 ≤ Γ) (hA : 0 ≤ A)
    (hγbd : ∀ t∈Icc (0 : ℝ) S, |γ t| ≤ Γ)
    (hjets : ∀ t∈Icc (0 : ℝ) S, ∀ k ≤ n+2, ∀ x, |iteratedDeriv k (deriv (V t)) x| ≤ A)
    {a b : ℝ} (ha : a∈Icc (0 : ℝ) S) (hb : b∈Icc (0 : ℝ) S) (x : ℝ) :
    |iteratedDeriv n (deriv (V a)) x-iteratedDeriv n (deriv (V b)) x| ≤
      (A/2+Γ*(A+lowerJetConstant n A))*|a-b| := by
  rcases le_total a b with hab | hba
  · rw [abs_sub_comm a b,abs_of_nonneg (sub_nonneg.mpr hab)]
    exact h.temporal_jet_bound hm hγ hi hST n hΓ hA hγbd hjets ha hb hab x
  · rw [abs_sub_comm (iteratedDeriv n _ x),abs_of_nonneg (sub_nonneg.mpr hba)]
    exact h.temporal_jet_bound hm hγ hi hST n hΓ hA hγbd hjets hb ha hba x

lemma uniform_bulk_temporal (Γ : ℝ) (hΓ : 0 ≤ Γ) (T : ℝ) (m : ℕ)
    {S : ℝ} (hS : 0 ≤ S) (hST : S<T) : ∃ L : ℝ, 0 ≤ L ∧
      ∀ (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ), SmoothEvolution T γ V → Measurable γ →
        MonotoneOn γ (Icc (0 : ℝ) T) → (∀ t∈Icc (0 : ℝ) T, |γ t| ≤ Γ) →
        ∀ s∈Icc (0 : ℝ) S, ∀ t∈Icc (0 : ℝ) S, ∀ x,
          |iteratedDeriv m (deriv (V s)) x-iteratedDeriv m (deriv (V t)) x| ≤ L*|s-t| := by
  obtain ⟨A,hA,ha⟩ := uniform_bulk_jets Γ hΓ T (m+2) S hS hST
  refine ⟨A/2+Γ*(A+lowerJetConstant m A),by positivity [lowerJetConstant_nonneg m hA],?_⟩
  intro γ V h hm hmono hbd s hs t ht x
  have hi : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le (hS.trans hST.le)] using hmono
  apply h.uniform_temporal_jet hm hmono hi hST.le m hΓ hA (fun r hr ↦ hbd r ⟨hr.1,hr.2.trans hST.le⟩)
    (ha γ V h hm hmono hbd) hs ht x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_SmoothApproxBounds
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma smoothApprox_bulk_jets (γ : OrderParameter) {S : ℝ} (hS : S∈Ico (0 : ℝ) 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t∈Icc (0 : ℝ) S → ∀ k ≤ m, ∀ x,
      |iteratedDeriv k (deriv (smoothApprox γ n t)) x| ≤ C := by
  let T := (S+1)/2
  have hST : S<T := by dsimp only [T]; linarith [hS.2]
  have hT1 : T<1 := by dsimp only [T]; linarith [hS.2]
  have hT : T∈Ico (0 : ℝ) 1 := ⟨hS.1.trans hST.le,hT1⟩
  obtain ⟨C,hC,hb⟩ := uniform_bulk_jets (γ.coeff T) (γ.nonneg _ hT) T m S hS.1 hST
  refine ⟨C,hC,?_⟩
  intro n t ht k hk x
  exact hb (profileCoeff (γ.grid n)) (smoothApprox γ n)
    ((smoothApprox_evolution γ n).restrict hT1.le) (profileCoeff_measurable _)
    ((profileCoeff_mono (γ.grid_mono n)).mono (by rw [γ.grid_time]; exact Icc_subset_Icc le_rfl hT1.le))
    (fun r hr ↦ by
      rw [abs_of_nonneg (profileCoeff_nonneg _ _)]
      exact (γ.grid_le n ⟨hr.1,hr.2.trans_lt hT1⟩).trans
        (γ.monotone ⟨hr.1,hr.2.trans_lt hT1⟩ hT hr.2)) t ht k hk x

lemma smoothApprox_bulk_temporal (γ : OrderParameter) {S : ℝ} (hS : S∈Ico (0 : ℝ) 1) (m : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n s, s∈Icc (0 : ℝ) S → ∀ t∈Icc (0 : ℝ) S, ∀ x,
      |iteratedDeriv m (deriv (smoothApprox γ n s)) x-
        iteratedDeriv m (deriv (smoothApprox γ n t)) x| ≤ L*|s-t| := by
  let T := (S+1)/2
  have hST : S<T := by dsimp only [T]; linarith [hS.2]
  have hT1 : T<1 := by dsimp only [T]; linarith [hS.2]
  have hT : T∈Ico (0 : ℝ) 1 := ⟨hS.1.trans hST.le,hT1⟩
  obtain ⟨L,hL,hb⟩ := uniform_bulk_temporal (γ.coeff T) (γ.nonneg _ hT) T m hS.1 hST
  refine ⟨L,hL,?_⟩
  intro n s hs t ht x
  exact hb (profileCoeff (γ.grid n)) (smoothApprox γ n)
    ((smoothApprox_evolution γ n).restrict hT1.le) (profileCoeff_measurable _)
    ((profileCoeff_mono (γ.grid_mono n)).mono (by rw [γ.grid_time]; exact Icc_subset_Icc le_rfl hT1.le))
    (fun r hr ↦ by
      rw [abs_of_nonneg (profileCoeff_nonneg _ _)]
      exact (γ.grid_le n ⟨hr.1,hr.2.trans_lt hT1⟩).trans
        (γ.monotone ⟨hr.1,hr.2.trans_lt hT1⟩ hT hr.2)) s hs t ht x

lemma phi_smooth_and_jet_limits (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) :
    (∀ k, TendstoUniformly (fun n (p : Icc (0 : ℝ) S×ℝ) ↦ iteratedDeriv k (smoothApprox γ n p.1) p.2)
      (fun p ↦ iteratedDeriv k (phi W γ p.1) p.2) atTop) ∧
      ∀ t∈Icc (0 : ℝ) S, ContDiff ℝ ∞ (phi W γ t) := by
  let map : Icc (0 : ℝ) S×ℝ → Ico (0 : ℝ) 1×ℝ :=
    fun p ↦ (⟨p.1,⟨p.1.property.1,p.1.property.2.trans_lt hS.2⟩⟩,p.2)
  have hlim : TendstoUniformly (fun n (p : Icc (0 : ℝ) S×ℝ) ↦ smoothApprox γ n p.1 p.2)
      (fun p ↦ phi W γ p.1 p.2) atTop := (smoothApprox_tendsto W γ).comp map
  have hs (n : ℕ) (t : Icc (0 : ℝ) S) : ContDiff ℝ ∞ (smoothApprox γ n t) :=
    ((smoothApprox_evolution γ n).slices t ⟨t.property.1,t.property.2.trans hS.2.le⟩).smooth
  have hb (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (a : Icc (0 : ℝ) S) x,
      |iteratedDeriv (k+1) (smoothApprox γ n a) x| ≤ C := by
    obtain ⟨C,hC,hb⟩ := smoothApprox_bulk_jets γ hS k
    refine ⟨C,hC,fun n a x ↦ ?_⟩
    simpa only [iteratedDeriv_succ'] using hb n a a.property k le_rfl x
  obtain ⟨hl,hsm⟩ := uniform_all_derivative_limits (f := fun t : Icc (0 : ℝ) S ↦ phi W γ t) hlim hs hb
  exact ⟨hl,fun t ht ↦ hsm ⟨t,ht⟩⟩

lemma phi_jet_limit (W : BrownianSpace) (γ : OrderParameter) {S t : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (ht : t∈Icc (0 : ℝ) S) (k : ℕ) (x : ℝ) :
    Tendsto (fun n ↦ iteratedDeriv k (deriv (smoothApprox γ n t)) x) atTop
      (𝓝 (iteratedDeriv k (deriv (phi W γ t)) x)) := by
  simpa only [iteratedDeriv_succ'] using
    ((phi_smooth_and_jet_limits W γ hS).1 (k+1)).tendsto_at (⟨t,ht⟩,x)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_PhiRegularity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma phi_bulk_jets (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t∈Icc (0 : ℝ) S, ∀ x,
      |iteratedDeriv k (deriv (phi W γ t)) x| ≤ C := by
  obtain ⟨C,hC,hb⟩ := smoothApprox_bulk_jets γ hS k
  refine ⟨C,hC,?_⟩
  intro t ht x
  exact le_of_tendsto (phi_jet_limit W γ hS ht k x).abs
    (Eventually.of_forall (fun n ↦ hb n t ht k le_rfl x))

lemma phi_bulk_temporal (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (k : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s∈Icc (0 : ℝ) S, ∀ t∈Icc (0 : ℝ) S, ∀ x,
      |iteratedDeriv k (deriv (phi W γ s)) x-iteratedDeriv k (deriv (phi W γ t)) x| ≤ L*|s-t| := by
  obtain ⟨L,hL,hb⟩ := smoothApprox_bulk_temporal γ hS k
  refine ⟨L,hL,?_⟩
  intro s hs t ht x
  exact le_of_tendsto ((phi_jet_limit W γ hS hs k x).sub (phi_jet_limit W γ hS ht k x)).abs
    (Eventually.of_forall (fun n ↦ hb n s hs t ht x))

lemma phi_smoothTerminal (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Ico (0 : ℝ) 1) : SmoothTerminal (phi W γ t) := by
  have hs := (phi_smooth_and_jet_limits W γ ht).2 t ⟨ht.1,le_rfl⟩
  refine ⟨phi_lipschitz W γ ⟨ht.1,ht.2.le⟩,hs,(contDiff_infty_iff_deriv.mp hs).2,?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := phi_bulk_jets W γ ht k
  exact ⟨C,hC,hb t ⟨ht.1,le_rfl⟩⟩

lemma phi_time_jet_continuous (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (k : ℕ) (x : ℝ) :
    ContinuousOn (fun t ↦ iteratedDeriv k (phi W γ t) x) (Icc (0 : ℝ) S) := by
  have hh := ((phi_smooth_and_jet_limits W γ hS).1 k).comp
    (fun t : Icc (0 : ℝ) S ↦ (t,x))
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hh.continuous
  apply Eventually.frequently (Eventually.of_forall _)
  intro n
  have hc : ContinuousOn (fun t ↦ iteratedDeriv k (smoothApprox γ n t) x) (Icc (0 : ℝ) S) := by
    have hsub : Icc (0 : ℝ) S⊆Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hS.2.le
    cases k with
    | zero => simpa only [iteratedDeriv_zero] using ((smoothApprox_evolution γ n).continuous_value x).mono hsub
    | succ k => simpa only [iteratedDeriv_succ'] using ((smoothApprox_evolution γ n).continuous_jet k x).mono hsub
  exact continuousOn_iff_continuous_domRestrict.mp hc

lemma smoothApprox_time_jet_continuous (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (n k : ℕ) (x : ℝ) :
    ContinuousOn (fun t ↦ iteratedDeriv k (deriv (smoothApprox γ n t)) x) (Icc (0 : ℝ) S) :=
  ((smoothApprox_evolution γ n).continuous_jet k x).mono (Icc_subset_Icc le_rfl hS.2.le)

lemma OrderParameter.grid_bulk_bound (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (n : ℕ) {t : ℝ} (ht : t∈Icc (0 : ℝ) S) :
    |profileCoeff (γ.grid n) t| ≤ γ.coeff S := by
  rw [abs_of_nonneg (profileCoeff_nonneg _ _)]
  exact (γ.grid_le n ⟨ht.1,ht.2.trans_lt hS.2⟩).trans
    (γ.monotone ⟨ht.1,ht.2.trans_lt hS.2⟩ hS ht.2)

lemma OrderParameter.grid_bulk_ae_tendsto (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) :
    ∀ᵐ t ∂volume, t∈Icc (0 : ℝ) S →
      Tendsto (fun n ↦ profileCoeff (γ.grid n) t) atTop (𝓝 (γ.coeff t)) := by
  filter_upwards [γ.grid_ae_tendsto,Measure.ae_ne volume (0 : ℝ)] with t hc hne ht
  have ht' : t∈Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 hne.symm,ht.2.trans hS.2.le⟩
  simpa only [OrderParameter.cutoff,indicator_of_mem (show t∈Ico (0 : ℝ) 1 from ⟨ht.1,ht.2.trans_lt hS.2⟩)] using hc ht'

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma phi_value_pde (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) {t s : ℝ} (ht : t∈Icc (0 : ℝ) S) (hs : s∈Icc (0 : ℝ) S) (x : ℝ) :
    phi W γ s x-phi W γ t x = -(∫ r in t..s,
      (1/2 : ℝ)*deriv (deriv (phi W γ r)) x+
        γ.coeff r*((1/2 : ℝ)*(deriv (phi W γ r) x)^2)) := by
  obtain ⟨C,hC,hb⟩ := smoothApprox_bulk_jets γ hS 1
  have hD := strip_integral_limit (c := fun n ↦ profileCoeff (γ.grid n)) (γ := γ.coeff)
    (f := fun n r ↦ (1/2 : ℝ)*iteratedDeriv 1 (deriv (smoothApprox γ n r)) x)
    (g := fun n r ↦ (1/2 : ℝ)*(iteratedDeriv 0 (deriv (smoothApprox γ n r)) x)^2)
    (F := fun r ↦ (1/2 : ℝ)*iteratedDeriv 1 (deriv (phi W γ r)) x)
    (G := fun r ↦ (1/2 : ℝ)*(iteratedDeriv 0 (deriv (phi W γ r)) x)^2)
    (Γ := γ.coeff S) (A := C/2) (B := C^2/2) ht hs
    (fun n ↦ profileCoeff_measurable _) (fun n ↦ continuousOn_const.mul (smoothApprox_time_jet_continuous γ hS n 1 x))
    (fun n ↦ continuousOn_const.mul ((smoothApprox_time_jet_continuous γ hS n 0 x).pow 2))
    (fun n r hr ↦ γ.grid_bulk_bound hS n hr)
    (fun n r hr ↦ by
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith [hb n r hr 1 le_rfl x])
    (fun n r hr ↦ by
      rw [abs_mul,abs_pow,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      have hh := hb n r hr 0 (by omega) x
      nlinarith [abs_nonneg (iteratedDeriv 0 (deriv (smoothApprox γ n r)) x)])
    (γ.nonneg _ hS) (γ.grid_bulk_ae_tendsto hS)
    (fun r hr ↦ (phi_jet_limit W γ hS hr 1 x).const_mul (1/2 : ℝ))
    (fun r hr ↦ ((phi_jet_limit W γ hS hr 0 x).pow 2).const_mul (1/2 : ℝ))
  simp only [iteratedDeriv_one,iteratedDeriv_zero] at hD
  have hvs := (smoothApprox_tendsto W γ).tendsto_at (⟨s,⟨hs.1,hs.2.trans_lt hS.2⟩⟩,x)
  have hvt := (smoothApprox_tendsto W γ).tendsto_at (⟨t,⟨ht.1,ht.2.trans_lt hS.2⟩⟩,x)
  have he (n : ℕ) := (smoothApprox_evolution γ n).value_pde t ⟨ht.1,ht.2.trans hS.2.le⟩ s ⟨hs.1,hs.2.trans hS.2.le⟩ x
  exact tendsto_nhds_unique (hvs.sub hvt) (hD.neg.congr (fun n ↦ (he n).symm))

lemma phi_gradient_pde (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) {t s : ℝ} (ht : t∈Icc (0 : ℝ) S) (hs : s∈Icc (0 : ℝ) S) (x : ℝ) :
    deriv (phi W γ s) x-deriv (phi W γ t) x = -(∫ r in t..s,
      (1/2 : ℝ)*deriv (deriv (deriv (phi W γ r))) x+
        γ.coeff r*(deriv (phi W γ r) x*deriv (deriv (phi W γ r)) x)) := by
  obtain ⟨C,hC,hb⟩ := smoothApprox_bulk_jets γ hS 2
  have hD := strip_integral_limit (c := fun n ↦ profileCoeff (γ.grid n)) (γ := γ.coeff)
    (f := fun n r ↦ (1/2 : ℝ)*iteratedDeriv 2 (deriv (smoothApprox γ n r)) x)
    (g := fun n r ↦ iteratedDeriv 0 (deriv (smoothApprox γ n r)) x*iteratedDeriv 1 (deriv (smoothApprox γ n r)) x)
    (F := fun r ↦ (1/2 : ℝ)*iteratedDeriv 2 (deriv (phi W γ r)) x)
    (G := fun r ↦ iteratedDeriv 0 (deriv (phi W γ r)) x*iteratedDeriv 1 (deriv (phi W γ r)) x)
    (Γ := γ.coeff S) (A := C/2) (B := C^2) ht hs
    (fun n ↦ profileCoeff_measurable _) (fun n ↦ continuousOn_const.mul (smoothApprox_time_jet_continuous γ hS n 2 x))
    (fun n ↦ (smoothApprox_time_jet_continuous γ hS n 0 x).mul (smoothApprox_time_jet_continuous γ hS n 1 x))
    (fun n r hr ↦ γ.grid_bulk_bound hS n hr)
    (fun n r hr ↦ by
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      linarith [hb n r hr 2 le_rfl x])
    (fun n r hr ↦ by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hb n r hr 0 (by omega) x) (hb n r hr 1 (by omega) x) (abs_nonneg _) hC)
    (γ.nonneg _ hS) (γ.grid_bulk_ae_tendsto hS)
    (fun r hr ↦ (phi_jet_limit W γ hS hr 2 x).const_mul (1/2 : ℝ))
    (fun r hr ↦ (phi_jet_limit W γ hS hr 0 x).mul (phi_jet_limit W γ hS hr 1 x))
  simp only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hD
  have hvs := phi_jet_limit W γ hS hs 0 x
  have hvt := phi_jet_limit W γ hS ht 0 x
  simp only [iteratedDeriv_zero] at hvs hvt
  have he (n : ℕ) := (smoothApprox_evolution γ n).gradient_pde t ⟨ht.1,ht.2.trans hS.2.le⟩ s ⟨hs.1,hs.2.trans hS.2.le⟩ x
  exact tendsto_nhds_unique (hvs.sub hvt) (hD.neg.congr (fun n ↦ (he n).symm))

lemma phi_evolution_oai (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) : SmoothEvolution S γ.coeff (phi W γ) := by
  refine ⟨fun t ht ↦ phi_smoothTerminal W γ ⟨ht.1,ht.2.trans_lt hS.2⟩,?_,?_,
    phi_bulk_jets W γ hS,phi_bulk_temporal W γ hS,?_,?_⟩
  · intro x
    simpa only [iteratedDeriv_zero] using phi_time_jet_continuous W γ hS 0 x
  · intro n x
    simpa only [iteratedDeriv_succ'] using phi_time_jet_continuous W γ hS (n+1) x
  · exact fun t ht s hs x ↦ phi_value_pde W γ hS ht hs x
  · exact fun t ht s hs x ↦ phi_gradient_pde W γ hS ht hs x

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.phi_evolution_oai := @OAI.SKValue.phi_evolution_oai
