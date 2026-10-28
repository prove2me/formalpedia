-- Prove2me | solution 1 for OAI.SKValue.IsDiffusion.parisi_first_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:57:04.446562+00:00
-- url     : https://prove2.me/submissions/31641a8c-5ca8-4449-875a-d672337b9c98

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000

section
-- module Solutions.OAIQ4_Sk.Compat
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

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

lemma OrderParameter.intervalIntegrable (γ : OrderParameter) :
    IntervalIntegrable γ.coeff volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr γ.integrable

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

lemma brownian_increment_mean (W : BrownianSpace) (t : ℝ) :
    (∫ ω, W.B 1 ω-W.B t.toNNReal ω ∂W.μ)=0 := by
  rw [integral_sub (W.brownian.integrable_eval 1) (W.brownian.integrable_eval _),
    W.brownian.integral_eval, W.brownian.integral_eval, sub_self]

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

lemma controlPayoff_zero (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) :
    controlPayoff W γ t x (fun _ _ ↦ (0 : ℝ)) =
      ∫ ω, |x+(W.B 1 ω-W.B t.toNNReal ω)| ∂W.μ := by
  simp only [controlPayoff, mul_zero, zero_pow (by norm_num : 2≠0),
    intervalIntegral.integral_zero, add_zero, sub_zero]
  congr 1
  funext ω
  congr 1
  ring

lemma controlPayoff_zero_lower (W : BrownianSpace) (γ : OrderParameter) (t x : ℝ) :
    |x| ≤ controlPayoff W γ t x (fun _ _ ↦ (0 : ℝ)) := by
  rw [controlPayoff_zero]
  have hm : (∫ ω, x+(W.B 1 ω-W.B t.toNNReal ω) ∂W.μ)=x := by
    rw [integral_add (integrable_const _) (brownian_increment_integrable W t), brownian_increment_mean]
    simp
  simpa only [Real.norm_eq_abs, hm] using
    norm_integral_le_integral_norm (μ := W.μ) (fun ω ↦ x+(W.B 1 ω-W.B t.toNNReal ω))

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

lemma phi_lower (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) : |x|≤phi W γ t x := by
  exact (controlPayoff_zero_lower W γ t x).trans
    (le_csSup (control_values_bddAbove W γ ht x) ⟨_, admissible_zero W t, rfl⟩)

lemma phi_upper (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    phi W γ t x≤|x|+(∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)+
      (1/2 : ℝ)*∫ s in t..1, γ.cutoff s := by
  apply csSup_le (control_values_nonempty W γ t x)
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
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlPayoffConvex
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

lemma brownian_increment_memLp (W : BrownianSpace) (t : ℝ) :
    MemLp (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω) 2 W.μ :=
  (W.brownian.hasLaw_sub 1 t.toNNReal).hasGaussianLaw.memLp (by norm_num)

lemma brownian_increment_second (W : BrownianSpace) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    (∫ ω, (W.B 1 ω-W.B t.toNNReal ω)^2 ∂W.μ)=1-t := by
  have h := (W.brownian.hasLaw_sub 1 t.toNNReal).integral_comp
    (f := fun x : ℝ ↦ x^2) (by fun_prop)
  change (∫ ω, (W.B 1 ω-W.B t.toNNReal ω)^2 ∂W.μ)=_ at h
  rw [h]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := nndist ((1 : ℝ≥0) : ℝ) (t.toNNReal : ℝ))
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hv
  simp only [sub_zero] at hv
  exact hv.trans (by simp only [NNReal.coe_one, coe_nndist, Real.dist_eq, Real.coe_toNNReal t ht.1,
    abs_of_nonneg (sub_nonneg.mpr ht.2)])

lemma brownian_increment_abs_bound (W : BrownianSpace) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    (∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)≤Real.sqrt (1-t) := by
  have hf := brownian_increment_memLp W t
  have hab : MemLp (fun ω ↦ |W.B 1 ω-W.B t.toNNReal ω|) 2 W.μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hv := variance_nonneg (fun ω ↦ |W.B 1 ω-W.B t.toNNReal ω|) W.μ
  rw [variance_eq_sub hab] at hv
  simp only [Pi.pow_apply, sq_abs, brownian_increment_second W ht] at hv
  apply (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _)) (sub_nonneg.mpr ht.2)).mpr
  linarith

lemma phi_terminal_bound (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    0≤phi W γ t x-|x| ∧
      phi W γ t x-|x|≤Real.sqrt (1-t)+(1/2 : ℝ)*∫ s in t..1, γ.cutoff s := by
  constructor
  · exact sub_nonneg.mpr (phi_lower W γ ht x)
  · linarith [phi_upper W γ ht x, brownian_increment_abs_bound W ht]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_InitialMax
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

lemma finite_discrete_gronwall {e r : ℕ → ℝ} {c : ℝ} {N : ℕ}
    (hc : 0 ≤ c) (he0 : e 0 = 0)
    (hr : ∀ j < N, 0 ≤ r j)
    (hrec : ∀ j < N, e (j+1) ≤ (1+c) * e j + r j) :
    ∀ n ≤ N, e n ≤ (∑ j ∈ range n, r j) * Real.exp ((n : ℝ)*c) := by
  intro n hn
  induction n with
  | zero => simp [he0]
  | succ n ih =>
    have hnN : n < N := by omega
    have ih' := ih (by omega)
    have hsum : 0 ≤ ∑ j ∈ range n, r j :=
      sum_nonneg (fun j hj ↦ hr j (lt_of_lt_of_le (mem_range.mp hj) (by omega)))
    have hexp : 1 ≤ Real.exp (((n+1 : ℕ) : ℝ)*c) :=
      Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hc)
    calc
      e (n+1) ≤ (1+c) * e n + r n := hrec n hnN
      _ ≤ (1+c) * ((∑ j ∈ range n, r j) * Real.exp ((n : ℝ)*c)) + r n := by
        gcongr
      _ ≤ Real.exp c * ((∑ j ∈ range n, r j) * Real.exp ((n : ℝ)*c)) +
          r n * Real.exp (((n+1 : ℕ) : ℝ)*c) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by simpa [add_comm] using Real.add_one_le_exp c)
            (mul_nonneg hsum (Real.exp_pos _).le)
        · exact le_mul_of_one_le_right (hr n hnN) hexp
      _ = (∑ j ∈ range (n+1), r j) * Real.exp (((n+1 : ℕ) : ℝ)*c) := by
        rw [sum_range_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.exp_add]
        ring

lemma finite_discrete_gronwall_uniform {e r : ℕ → ℝ} {c : ℝ} {N : ℕ}
    (hc : 0 ≤ c) (he0 : e 0 = 0)
    (hr : ∀ j < N, 0 ≤ r j)
    (hrec : ∀ j < N, e (j+1) ≤ (1+c) * e j + r j)
    {R : ℝ} (hR : (∑ j ∈ range N, r j) ≤ R) :
    ∀ n ≤ N, e n ≤ R * Real.exp ((N : ℝ)*c) := by
  intro n hn
  apply (finite_discrete_gronwall hc he0 hr hrec n hn).trans
  apply mul_le_mul
  · exact (sum_le_sum_of_subset_of_nonneg (range_mono hn)
      (fun j hj _ ↦ hr j (mem_range.mp hj))).trans hR
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hc)
  · exact (Real.exp_pos _).le
  · exact le_trans (sum_nonneg (fun j hj ↦ hr j (mem_range.mp hj))) hR

lemma driven_euler_stability {δ G L : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} {Y r : ℕ → ℝ}
    (hδ : 0 ≤ δ) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hγ : ∀ j < N, |γ ((j : ℝ)*δ)| ≤ G)
    (hu : ∀ j < N, ∀ x y,
      |u ((j : ℝ)*δ) x - u ((j : ℝ)*δ) y| ≤ L * |x-y|)
    (hY : ∀ j < N, Y (j+1) = Y j + W (((j+1 : ℕ) : ℝ)*δ) - W ((j : ℝ)*δ) +
      δ * γ ((j : ℝ)*δ) * u ((j : ℝ)*δ) (Y j))
    (hdefect : ∀ j < N,
      |X (((j+1 : ℕ) : ℝ)*δ) - X ((j : ℝ)*δ) -
        (W (((j+1 : ℕ) : ℝ)*δ) - W ((j : ℝ)*δ)) -
        δ * γ ((j : ℝ)*δ) * u ((j : ℝ)*δ) (X ((j : ℝ)*δ))| ≤ r j)
    {R : ℝ} (hR : (∑ j ∈ range N, r j) ≤ R) :
    ∀ j ≤ N, |Y j - X ((j : ℝ)*δ)| ≤ R * Real.exp ((N : ℝ)*δ*G*L) := by
  have hr : ∀ j < N, 0 ≤ r j := fun j hj ↦ (abs_nonneg _).trans (hdefect j hj)
  have hrec : ∀ j < N,
      |Y (j+1) - X (((j+1 : ℕ) : ℝ)*δ)| ≤
        (1+δ*G*L) * |Y j - X ((j : ℝ)*δ)| + r j := by
    intro j hj
    let q := X (((j+1 : ℕ) : ℝ)*δ) - X ((j : ℝ)*δ) -
         (W (((j+1 : ℕ) : ℝ)*δ) - W ((j : ℝ)*δ)) -
         δ * γ ((j : ℝ)*δ) * u ((j : ℝ)*δ) (X ((j : ℝ)*δ))
    have heq : Y (j+1) - X (((j+1 : ℕ) : ℝ)*δ) =
        (Y j - X ((j : ℝ)*δ)) + δ * γ ((j : ℝ)*δ) *
        (u ((j : ℝ)*δ) (Y j) - u ((j : ℝ)*δ) (X ((j : ℝ)*δ))) - q := by
      rw [hY j hj]
      dsimp [q]
      ring
    rw [heq]
    calc
      _ ≤ |Y j - X ((j : ℝ)*δ)| +
          |δ * γ ((j : ℝ)*δ) * (u ((j : ℝ)*δ) (Y j) -
            u ((j : ℝ)*δ) (X ((j : ℝ)*δ)))| + |q| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |Y j - X ((j : ℝ)*δ)| + δ * G * (L * |Y j - X ((j : ℝ)*δ)|) + r j := by
        rw [abs_mul, abs_mul, abs_of_nonneg hδ]
        gcongr
        · exact hγ j hj
        · exact hu j hj _ _
        · exact hdefect j hj
      _ = (1+δ*G*L) * |Y j - X ((j : ℝ)*δ)| + r j := by ring
  simpa only [mul_assoc] using
    finite_discrete_gronwall_uniform (mul_nonneg (mul_nonneg hδ hG) hL)
      (by simp [hY0, hX0]) hr hrec hR

lemma monotone_drift_local_error {a b G L ε : ℝ} {γ X : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} (hab : a ≤ b) (hG : 0 ≤ G) (hL : 0 ≤ L) (_ : 0 ≤ ε)
    (hγ : MonotoneOn γ (Icc a b)) (hγ0 : 0 ≤ γ a) (hγG : γ a ≤ G)
    (hu : ∀ s ∈ Icc a b, |u s (X s)| ≤ 1)
    (hLip : ∀ s ∈ Icc a b,
      |u s (X s) - u a (X a)| ≤ L * (|s-a| + |X s-X a|))
    (hX : ∀ s ∈ Icc a b, |X s-X a| ≤ ε)
    (hint : IntervalIntegrable (fun s ↦ γ s * u s (X s)) volume a b) :
    |(∫ s in a..b, γ s * u s (X s)) - (b-a) * γ a * u a (X a)| ≤
      (b-a) * (γ b-γ a) + (b-a) * G * L * ((b-a)+ε) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hp : ∀ s ∈ Icc a b,
      |γ s * u s (X s) - γ a * u a (X a)| ≤ (γ b-γ a) + G*L*((b-a)+ε) := by
    intro s hs
    have hsa := hγ ha hs hs.1
    have hsb := hγ hs hb hs.2
    calc
      _ = |(γ s-γ a)*u s (X s) + γ a*(u s (X s)-u a (X a))| := by
        congr 1; ring
      _ ≤ |(γ s-γ a)*u s (X s)| + |γ a*(u s (X s)-u a (X a))| := abs_add_le _ _
      _ = (γ s-γ a)*|u s (X s)| + γ a*|u s (X s)-u a (X a)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hsa), abs_of_nonneg hγ0]
      _ ≤ (γ b-γ a) + G*L*((b-a)+ε) := by
        calc
          _ ≤ (γ s-γ a)*1 + G*(L*((b-a)+ε)) := by
            gcongr
            · exact hu s hs
            · exact hLip s hs |>.trans (by
                gcongr
                · rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
                  exact sub_le_sub_right hs.2 a
                · exact hX s hs)
          _ ≤ (γ b-γ a) + G*L*((b-a)+ε) := by nlinarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun s ↦ γ s*u s (X s)-γ a*u a (X a))
    (C := (γ b-γ a)+G*L*((b-a)+ε)) (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le hab] at hs
      exact hp s ⟨hs.1.le, hs.2⟩)
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  convert hi using 1
  · congr 1; ring
  · ring

lemma mesh_mem_strip {δ T : ℝ} {N j : ℕ} (hδ : 0 ≤ δ)
    (horizon : (N : ℝ)*δ = T) (hj : j ≤ N) : (j : ℝ)*δ ∈ Icc (0 : ℝ) T := by
  constructor
  · positivity
  · rw [← horizon]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ

lemma intervalIntegrable_substrip {f : ℝ → ℝ} {T a b : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T) (ha : a ∈ Icc (0 : ℝ) T)
    (hb : b ∈ Icc (0 : ℝ) T) : IntervalIntegrable f volume a b := by
  apply hf.mono_set
  rw [uIcc_of_le hT]
  exact uIcc_subset_Icc ha hb

lemma driven_euler_error_bound {δ T L ε : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} {Y : ℕ → ℝ}
    (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (horizon : (N : ℝ)*δ = T)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0 ≤ γ 0)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x| ≤ 1)
    (hLip : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y| ≤ L*(|s-t|+|x-y|))
    (hXosc : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      |s-t| ≤ δ → |X s-X t| ≤ ε)
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, X t = W t + ∫ s in (0 : ℝ)..t, γ s*u s (X s))
    (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hY : ∀ j < N, Y (j+1) = Y j + W (((j+1 : ℕ) : ℝ)*δ)-W ((j : ℝ)*δ) +
      δ*γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j)) :
    ∀ j ≤ N, |Y j-X ((j : ℝ)*δ)| ≤
      (δ*(γ T-γ 0)+T*γ T*L*(δ+ε))*Real.exp (T*γ T*L) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl,hT⟩
  have h1 : T ∈ Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hG : 0 ≤ γ T := hγ0.trans (hγ h0 h1 hT)
  have hmesh := fun j hj ↦ mesh_mem_strip hδ horizon (j := j) hj
  have hγnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ γ t :=
    fun t ht ↦ hγ0.trans (hγ h0 ht ht.1)
  let r : ℕ → ℝ := fun j ↦ δ*(γ (((j+1 : ℕ) : ℝ)*δ)-γ ((j : ℝ)*δ)) +
    δ*γ T*L*(δ+ε)
  have hdefect : ∀ j < N,
      |X (((j+1 : ℕ) : ℝ)*δ)-X ((j : ℝ)*δ) -
        (W (((j+1 : ℕ) : ℝ)*δ)-W ((j : ℝ)*δ)) -
        δ*γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (X ((j : ℝ)*δ))| ≤ r j := by
    intro j hj
    have ha := hmesh j (by omega)
    have hb := hmesh (j+1) (by omega)
    have hab : (j : ℝ)*δ ≤ ((j+1 : ℕ) : ℝ)*δ := by push_cast; nlinarith
    have hlength : ((j+1 : ℕ) : ℝ)*δ-(j : ℝ)*δ = δ := by push_cast; ring
    have hsub : Icc ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) ⊆ Icc (0 : ℝ) T :=
      Icc_subset_Icc ha.1 hb.2
    have hquadrature := monotone_drift_local_error hab hG hL hε
      (hγ.mono hsub) (hγnonneg _ ha) (hγ ha h1 ha.2)
      (fun s hs ↦ hu s (hsub hs) _)
      (fun s hs ↦ hLip s (hsub hs) _ ha _ _)
      (fun s hs ↦ hXosc s (hsub hs) _ ha (by
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        calc s-(j : ℝ)*δ ≤ ((j+1 : ℕ) : ℝ)*δ-(j : ℝ)*δ := sub_le_sub_right hs.2 _
             _ = δ := hlength))
      (intervalIntegrable_substrip hT hint ha hb)
    rw [hlength] at hquadrature
    have hdiff : X (((j+1 : ℕ) : ℝ)*δ)-X ((j : ℝ)*δ) -
        (W (((j+1 : ℕ) : ℝ)*δ)-W ((j : ℝ)*δ)) =
        ∫ s in (j : ℝ)*δ..((j+1 : ℕ) : ℝ)*δ, γ s*u s (X s) := by
      rw [hX _ hb, hX _ ha]
      have hi := intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_substrip hT hint h0 hb)
        (intervalIntegrable_substrip hT hint h0 ha)
      linear_combination hi
    simpa only [hdiff, r] using hquadrature
  have hsum : (∑ j ∈ range N, r j) = δ*(γ T-γ 0)+T*γ T*L*(δ+ε) := by
    dsimp [r]
    rw [sum_add_distrib, ← mul_sum, sum_range_sub (fun j : ℕ ↦ γ ((j : ℝ)*δ))]
    simp only [Nat.cast_zero, zero_mul, sum_const, card_range, nsmul_eq_mul]
    rw [horizon]
    rw [← horizon]
    ring
  have hbound := driven_euler_stability hδ hG hL hX0 hY0
    (fun j hj ↦ by
      rw [abs_of_nonneg (hγnonneg _ (hmesh j (by omega)))]
      exact hγ (hmesh j (by omega)) h1 (hmesh j (by omega)).2)
    (fun j hj x y ↦ by simpa using hLip _ (hmesh j (by omega)) _ (hmesh j (by omega)) x y)
    hY hdefect hsum.le
  simpa only [horizon] using hbound

lemma driven_euler_uniform_convergence {T L : ℝ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} {Y : ℕ → ℕ → ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0 ≤ γ 0)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x| ≤ 1)
    (hLip : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y| ≤ L*(|s-t|+|x-y|))
    (hXcont : ContinuousOn X (Icc (0 : ℝ) T))
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, X t = W t + ∫ s in (0 : ℝ)..t, γ s*u s (X s))
    (hX0 : X 0 = 0) (hY0 : ∀ N, Y N 0 = 0)
    (hY : ∀ N > 0, ∀ j < N,
      Y N (j+1) = Y N j + W (((j+1 : ℕ) : ℝ)*(T/N))-W ((j : ℝ)*(T/N)) +
        (T/N)*γ ((j : ℝ)*(T/N))*u ((j : ℝ)*(T/N)) (Y N j)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ j ≤ N, |Y N j-X ((j : ℝ)*(T/N))| < ε := by
  intro ε hε
  have hG : 0 ≤ γ T := hγ0.trans (hγ ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT)
  let E := Real.exp (T*γ T*L)
  let C := T*γ T*L*E
  have hE : 0 < E := Real.exp_pos _
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg hT hG) hL) hE.le
  let η := ε/(2*(C+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηeq : η*(2*(C+1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hCη : C*η < ε/2 := by nlinarith
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hXcont) η hη
  have hδ : Tendsto (fun N : ℕ ↦ T/N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have htail : Tendsto (fun N : ℕ ↦ (T/N)*((γ T-γ 0)+T*γ T*L)*E)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (hδ.mul_const ((γ T-γ 0)+T*γ T*L)).mul_const E
  filter_upwards [hδ.eventually_le_const hθ,
    htail.eventually_lt_const (half_pos hε), eventually_gt_atTop 0] with N hNθ hNerr hN
  have hδnonneg : 0 ≤ T/(N : ℝ) := div_nonneg hT (Nat.cast_nonneg _)
  have horizon : (N : ℝ)*(T/N) = T := by
    field_simp
  have hbound := driven_euler_error_bound hδnonneg hT hL hη.le horizon hγ hγ0 hu hLip
    (fun s hs t ht hst ↦ by
      have hh := hmod s hs t ht (by simpa [Real.dist_eq] using hst.trans hNθ)
      simpa [Real.dist_eq] using hh)
    hint hX hX0 (hY0 N) (hY N hN)
  intro j hj
  apply (hbound j hj).trans_lt
  change (T/(N : ℝ)*(γ T-γ 0)+T*γ T*L*(T/N+η))*E < ε
  dsimp [C] at hCη
  nlinarith [hNerr,hCη]

lemma driven_euler_uniform_bound {δ T : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} {Y : ℕ → ℝ}
    (hδ : 0 ≤ δ) (hT : 0 ≤ T) (horizon : (N : ℝ)*δ = T)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0 ≤ γ 0)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x| ≤ 1)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, X t = W t + ∫ s in (0 : ℝ)..t, γ s*u s (X s))
    (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hY : ∀ j < N, Y (j+1) = Y j + W (((j+1 : ℕ) : ℝ)*δ)-W ((j : ℝ)*δ) +
      δ*γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j)) :
    ∀ j ≤ N, |Y j-X ((j : ℝ)*δ)| ≤ 2*T*γ T := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl,hT⟩
  have h1 : T ∈ Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hG : 0 ≤ γ T := hγ0.trans (hγ h0 h1 hT)
  have hW0 : W 0 = 0 := by simpa [hX0] using (hX 0 h0).symm
  have hmesh := fun j hj ↦ mesh_mem_strip hδ horizon (j := j) hj
  have hγnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ γ t :=
    fun t ht ↦ hγ0.trans (hγ h0 ht ht.1)
  have hγu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |γ t*u t x| ≤ γ T := by
    intro t ht x
    rw [abs_mul, abs_of_nonneg (hγnonneg t ht)]
    calc γ t*|u t x| ≤ γ t*1 := mul_le_mul_of_nonneg_left (hu t ht x) (hγnonneg t ht)
         _ ≤ γ T := by simpa using hγ ht h1 ht.2
  have hYbound : ∀ j ≤ N, |Y j-W ((j : ℝ)*δ)| ≤ ((j : ℝ)*δ)*γ T := by
    intro j hj
    induction j with
    | zero => simp [hY0,hW0]
    | succ j ih =>
      have hjN : j < N := by omega
      have ih' := ih (by omega)
      have heq : Y (j+1)-W (((j+1 : ℕ) : ℝ)*δ) =
          (Y j-W ((j : ℝ)*δ)) + δ*(γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j)) := by
        rw [hY j hjN]; ring
      calc
        _ = |(Y j-W ((j : ℝ)*δ)) + δ*(γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j))| := congrArg abs heq
        _ ≤ |Y j-W ((j : ℝ)*δ)| + |δ*(γ ((j : ℝ)*δ)*u ((j : ℝ)*δ) (Y j))| := abs_add_le _ _
        _ ≤ ((j : ℝ)*δ)*γ T+δ*γ T := by
          rw [abs_mul,abs_of_nonneg hδ]
          exact add_le_add ih' (mul_le_mul_of_nonneg_left (hγu _ (hmesh j (by omega)) _) hδ)
        _ = (((j+1 : ℕ) : ℝ)*δ)*γ T := by push_cast; ring
  intro j hj
  have hm := hmesh j hj
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (j : ℝ)*δ) (f := fun s ↦ γ s*u s (X s)) (C := γ T)
    (fun s hs ↦ by
      rw [uIoc_of_le hm.1] at hs
      rw [Real.norm_eq_abs]
      exact hγu s ⟨hs.1.le,hs.2.trans hm.2⟩ _)
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hm.1] at hi
  calc
    _ = |(Y j-W ((j : ℝ)*δ)) - ∫ s in (0 : ℝ)..(j : ℝ)*δ, γ s*u s (X s)| := by
      rw [hX _ hm]; congr 1; ring
    _ ≤ |Y j-W ((j : ℝ)*δ)| + |∫ s in (0 : ℝ)..(j : ℝ)*δ, γ s*u s (X s)| := abs_sub _ _
    _ ≤ ((j : ℝ)*δ)*γ T+γ T*((j : ℝ)*δ) := add_le_add (hYbound j hj) hi
    _ ≤ 2*T*γ T := by nlinarith [mul_le_mul_of_nonneg_right hm.2 hG]

lemma initialMax_le_iff {f : ℕ → ℝ} {n : ℕ} {b : ℝ} :
    initialMax f n ≤ b ↔ ∀ j ≤ n, f j ≤ b := by
  induction n with
  | zero => simp [initialMax]
  | succ n ih =>
    simp only [initialMax, max_le_iff, ih]
    constructor
    · rintro ⟨ha,hb⟩ j hj
      obtain hj | rfl := lt_or_eq_of_le hj
      · exact ha j (by omega)
      · exact hb
    · intro h
      exact ⟨fun j hj ↦ h j (by omega), h _ le_rfl⟩

lemma initialMax_lt_iff {f : ℕ → ℝ} {n : ℕ} {b : ℝ} :
    initialMax f n < b ↔ ∀ j ≤ n, f j < b := by
  induction n with
  | zero => simp [initialMax]
  | succ n ih =>
    simp only [initialMax, max_lt_iff, ih]
    constructor
    · rintro ⟨ha,hb⟩ j hj
      obtain hj | rfl := lt_or_eq_of_le hj
      · exact ha j (by omega)
      · exact hb
    · intro h
      exact ⟨fun j hj ↦ h j (by omega), h _ le_rfl⟩

lemma le_initialMax {f : ℕ → ℝ} {n j : ℕ} (hj : j ≤ n) : f j ≤ initialMax f n :=
  initialMax_le_iff.mp le_rfl j hj

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshMaxError
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

lemma meshMaxError_nonneg {Ω : Type*} (T : ℝ) (X : ℝ → Ω → ℝ)
    (Y : ℕ → ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : 0 ≤ meshMaxError T X Y N ω :=
  (abs_nonneg _).trans (le_initialMax
    (f := fun j ↦ |Y N j ω-X ((j : ℝ)*(T/N)) ω|) (Nat.zero_le N))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_MemLpLinearCombination
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
namespace SKValue
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} {g : ι → Ω → ℝ}

lemma memLp_linearCombination (hg : ∀ i, MemLp (g i) 2 μ) (b : ι → ℝ) :
    MemLp (fun ω ↦ ∑ i, b i*g i ω) 2 μ := by
  exact memLp_finsetSum Finset.univ (fun i _ ↦ (hg i).const_mul (b i))

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

lemma independent_of_coordinate_not_in {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace β]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ι) {j : ι} (hj : j ∉ S) {F : (ι → ℝ) → β}
    (hF : Measurable F)
    (hdep : ∀ x y, (∀ i ∈ S, x i=y i) → F x=F y) :
    IndepFun F (fun x ↦ x j) (Measure.pi μ) := by
  let fill : (S → ℝ) → ι → ℝ := fun x i ↦ if hi : i ∈ S then x ⟨i,hi⟩ else 0
  have hfill : Measurable fill := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ S
    · simpa only [fill, dite_eq_left hi] using (measurable_pi_apply (⟨i,hi⟩ : S))
    · simp only [fill, dite_eq_right hi]
      exact measurable_const
  have hid : ∀ x : ι → ℝ, F (fill (fun i : S ↦ x i)) = F x := by
    intro x
    apply hdep
    intro i hi
    simp [fill,hi]
  have hST : Disjoint S {j} := by simpa using hj
  have hind : iIndepFun (fun i (x : ι → ℝ) ↦ x i) (Measure.pi μ) :=
    iIndepFun_pi (fun i ↦ (measurable_id : Measurable (id : ℝ → ℝ)).aemeasurable)
  have H := (hind.indepFun_finset S {j} hST (fun i ↦ measurable_pi_apply i)).comp
    (hF.comp hfill) (measurable_pi_apply (⟨j,by simp⟩ : ({j} : Finset ι)))
  simpa only [Function.comp_def, hid] using H

lemma measurable_coordinate (N j : ℕ) : Measurable (coordinate N j) :=
  measurable_pi_apply _

lemma coordinate_eq_apply {N j : ℕ} (hj : j < N+1) (z : Fin (N+1) → ℝ) :
    coordinate N j z = z ⟨j,hj⟩ := by
  simp [coordinate, Nat.mod_eq_of_lt hj]

lemma euler_depends_on_past (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) (z z' : Fin (N+1) → ℝ)
    (h : ∀ i < j, coordinate N i z=coordinate N i z') :
    euler T N γ u z j=euler T N γ u z' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := ih (fun i hi ↦ h i (by omega))
    simp only [euler, hp,h j (by omega)]

lemma measurable_euler (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hU : ∀ k < N, Measurable (u (meshTime T N k))) :
    ∀ j ≤ N, Measurable (fun z ↦ euler T N γ u z j) := by
  intro j hj
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hjN : j < N := by omega
    have hy := ih (by omega)
    have hz := measurable_coordinate N j
    have hu := (hU j hjN).comp hy
    simp only [euler]
    fun_prop

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

lemma coordinate_hasLaw (N j : ℕ) :
    HasLaw (coordinate N j) (gaussianReal 0 1) (gaussianProduct (Fin (N+1))) :=
  (measurePreserving_eval (fun _ : Fin (N+1) ↦ standardGaussian)
    ⟨j % (N+1), Nat.mod_lt _ (Nat.succ_pos _)⟩).hasLaw

lemma DependsBefore.independent {N j : ℕ} {β : Type*} [MeasurableSpace β] (hj : j<N+1)
    {F : (Fin (N+1) → ℝ) → β} (hF : DependsBefore j F) (hm : Measurable F) :
    IndepFun F (coordinate N j) (gaussianProduct (Fin (N+1))) := by
  have H := independent_of_coordinate_not_in (μ := fun _ : Fin (N+1) ↦ standardGaussian)
    (Finset.univ.filter (fun i : Fin (N+1) ↦ (i : ℕ)<j))
    (j := ⟨j,hj⟩) (by simp) hm (fun z z' heq ↦ hF z z' (by simpa using heq))
  have heq : coordinate N j = fun z : Fin (N+1) → ℝ ↦ z ⟨j,hj⟩ :=
    funext (coordinate_eq_apply hj)
  rw [heq]
  exact H

lemma DependsBefore.mono {N i j : ℕ} {β : Type*} {F : (Fin (N+1) → ℝ) → β}
    (hF : DependsBefore i F) (hij : i≤j) : DependsBefore j F :=
  fun z z' h ↦ hF z z' (fun k hk ↦ h k (hk.trans_le hij))

lemma DependsBefore.mul {N j : ℕ} {F G : (Fin (N+1) → ℝ) → ℝ}
    (hF : DependsBefore j F) (hG : DependsBefore j G) :
    DependsBefore j (fun z ↦ F z * G z) := by
  intro z z' h
  dsimp only
  rw [hF z z' h, hG z z' h]

lemma eulerCoefficient_dependsBefore (T : ℝ) {N j : ℕ} (hj : j≤N)
    (γ : ℝ → ℝ) (u a : ℝ → ℝ → ℝ) :
    DependsBefore j (fun z ↦ a (meshTime T N j) (euler T N γ u z j)) := by
  intro z z' h
  apply congrArg (a (meshTime T N j))
  apply euler_depends_on_past
  intro i hi
  have hiN : i<N+1 := by omega
  rw [coordinate_eq_apply hiN, coordinate_eq_apply hiN]
  exact h ⟨i,hiN⟩ hi

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_GaussianSquareVariance
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
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma gaussian_square_memLp_two {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    MemLp (fun ω ↦ (Z ω)^2) 2 μ := by
  have h := (gaussian_memLp hZ 4 (by norm_num)).norm_rpow_div 2
  norm_num [Real.norm_eq_abs, Real.rpow_two, sq_abs] at h
  have he : (4 : ℝ≥0∞)/2=2 := by
    change ((4 : ℝ≥0) : ℝ≥0∞)/((2 : ℝ≥0) : ℝ≥0∞)=((2 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.coe_div] <;> norm_num
  rwa [he] at h

lemma gaussian_centered_square_memLp_two [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    MemLp (fun ω ↦ (Z ω)^2-1) 2 μ :=
  (gaussian_square_memLp_two hZ).sub (memLp_const 1)

lemma gaussian_centered_square_mean [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    (∫ ω, (Z ω)^2-1 ∂μ)=0 := by
  rw [integral_sub (gaussian_memLp hZ 2 (by norm_num)).integrable_sq (integrable_const 1),
    gaussian_second_moment hZ]
  simp

lemma gaussianSquareVariance_nonneg : 0≤gaussianSquareVariance :=
  integral_nonneg fun _ ↦ sq_nonneg _

lemma gaussian_centered_square_variance {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    (∫ ω, ((Z ω)^2-1)^2 ∂μ)=gaussianSquareVariance := by
  exact hZ.integral_comp (f := fun z : ℝ ↦ (z^2-1)^2) (by fun_prop)

lemma predictableCenteredSquare_memLp {N j : ℕ}
    {H : (Fin (N+1) → ℝ) → ℝ} {K : ℝ}
    (hm : Measurable H) (hbound : ∀ z, |H z|≤K) :
    MemLp (fun z ↦ H z*((coordinate N j z)^2-1)) 2 (gaussianProduct (Fin (N+1))) := by
  have hQ := (gaussian_centered_square_memLp_two (coordinate_hasLaw N j))
  have hH : MemLp H ∞ (gaussianProduct (Fin (N+1))) :=
    MemLp.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hbound))
  exact hQ.mul' hH

lemma predictableCenteredSquare_variance {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} {K : ℝ}
    (hK : 0≤K) (hm : Measurable H) (hp : DependsBefore j H) (hbound : ∀ z, |H z|≤K) :
    (∫ z, (H z*((coordinate N j z)^2-1))^2 ∂gaussianProduct (Fin (N+1))) ≤
      K^2*gaussianSquareVariance := by
  have hind := (hp.independent hj hm).comp (measurable_id.pow_const 2)
    ((measurable_id.pow_const 2 |>.sub (measurable_const (a := (1 : ℝ)))).pow_const 2)
  have hi := hind.integral_mul_eq_mul_integral (hm.pow_const 2).aestronglyMeasurable
    (((measurable_coordinate N j).pow_const 2 |>.sub (measurable_const (a := (1 : ℝ)))).pow_const 2).aestronglyMeasurable
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] at hi
  simp_rw [mul_pow]
  rw [hi, gaussian_centered_square_variance (coordinate_hasLaw N j)]
  have hH : MemLp H 2 (gaussianProduct (Fin (N+1))) := MemLp.of_bound hm.aestronglyMeasurable K
    (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hbound))
  have hb : (∫ z, (H z)^2 ∂gaussianProduct (Fin (N+1))) ≤ K^2 := by
    have hi' := integral_mono hH.integrable_sq (integrable_const (K^2))
      (fun z ↦ by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 (hbound z))
    simpa using hi'
  exact mul_le_mul_of_nonneg_right hb gaussianSquareVariance_nonneg

lemma centeredSquare_dependsBefore {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} (hp : DependsBefore j H) :
    DependsBefore (j+1) (fun z ↦ H z*((coordinate N j z)^2-1)) := by
  intro z z' h
  dsimp only
  rw [hp.mono (Nat.le_succ j) z z' h]
  have hz : coordinate N j z=coordinate N j z' := by
    rw [coordinate_eq_apply hj, coordinate_eq_apply hj]
    exact h ⟨j,hj⟩ (Nat.lt_succ_self j)
  rw [hz]

lemma predictableCenteredSquares_orthogonal {N i j : ℕ} (hij : i<j) (hj : j<N+1)
    {H K : (Fin (N+1) → ℝ) → ℝ}
    (hHm : Measurable H) (hKm : Measurable K)
    (hHp : DependsBefore i H) (hKp : DependsBefore j K) :
    (∫ z, (H z*((coordinate N i z)^2-1))*(K z*((coordinate N j z)^2-1))
      ∂gaussianProduct (Fin (N+1)))=0 := by
  have hprev := (centeredSquare_dependsBefore (hij.trans hj) hHp).mono (by omega : i+1≤j)
  have hpm : Measurable (fun z ↦ H z*((coordinate N i z)^2-1)) :=
    hHm.mul (((measurable_coordinate N i).pow_const 2).sub (measurable_const (a := (1 : ℝ))))
  have hind := ((hprev.mul hKp).independent hj (hpm.mul hKm)).comp measurable_id
    ((measurable_id.pow_const 2).sub (measurable_const (a := (1 : ℝ))))
  have ht := hind.integral_mul_eq_mul_integral (hpm.mul hKm).aestronglyMeasurable
    (((measurable_coordinate N j).pow_const 2).sub (measurable_const (a := (1 : ℝ)))).aestronglyMeasurable
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] at ht
  simp_rw [mul_assoc] at ht ⊢
  rw [ht, gaussian_centered_square_mean (coordinate_hasLaw N j), mul_zero]

lemma orthogonal_sum_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Ω → ℝ} (hR : ∀ i, MemLp (R i) 2 μ)
    (horth : ∀ i j, i≠j → (∫ ω, R i ω*R j ω ∂μ)=0) :
    (∫ ω, (∑ i, R i ω)^2 ∂μ)=∑ i, ∫ ω, (R i ω)^2 ∂μ := by
  have hsum : MemLp (fun ω ↦ ∑ i, R i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hR i)
  have hi j : (∫ ω, (∑ i, R i ω)*R j ω ∂μ) = ∫ ω, (R j ω)^2 ∂μ := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum Finset.univ (fun i _ ↦
      show Integrable (fun ω ↦ R i ω*R j ω) μ from (hR i).integrable_mul (hR j))]
    rw [Finset.sum_eq_single j]
    · simp [pow_two]
    · intro i _ hij
      exact horth i j hij
    · simp
  simp_rw [pow_two, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ ↦
    show Integrable (fun ω ↦ R i ω*(∑ j, R j ω)) μ from (hR i).integrable_mul hsum)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (fun ω ↦ R i ω*(∑ j, R j ω))=(fun ω ↦ (∑ j, R j ω)*R i ω)
    from funext (fun _ ↦ mul_comm _ _), hi]
  simp [pow_two]

lemma predictableCenteredSquare_sum_bound {N : ℕ} {δ K : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ} (hK : 0≤K)
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hb : ∀ i z, |H i z|≤K) :
    (∫ z, ((δ/2)*(∑ i : Fin N, H i z*((coordinate N i z)^2-1)))^2
      ∂gaussianProduct (Fin (N+1))) ≤ (δ/2)^2*(N : ℝ)*K^2*gaussianSquareVariance := by
  have hmem (i : Fin N) := predictableCenteredSquare_memLp (j := (i : ℕ)) (hm i) (hb i)
  have hort : ∀ i j : Fin N, i≠j →
      (∫ z, (H i z*((coordinate N i z)^2-1))*(H j z*((coordinate N j z)^2-1))
        ∂gaussianProduct (Fin (N+1)))=0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact predictableCenteredSquares_orthogonal (by exact_mod_cast h) (by omega)
        (hm i) (hm j) (hp i) (hp j)
    · rw [show (fun z ↦ (H i z*((coordinate N i z)^2-1))*(H j z*((coordinate N j z)^2-1))) =
          (fun z ↦ (H j z*((coordinate N j z)^2-1))*(H i z*((coordinate N i z)^2-1)))
          from funext (fun _ ↦ mul_comm _ _)]
      exact predictableCenteredSquares_orthogonal (by exact_mod_cast h) (by omega)
        (hm j) (hm i) (hp j) (hp i)
  simp_rw [mul_pow]
  rw [integral_const_mul, orthogonal_sum_square hmem hort]
  calc
    _ ≤ (δ/2)^2*(∑ _i : Fin N, K^2*gaussianSquareVariance) := by
      gcongr with i
      exact predictableCenteredSquare_variance (by omega) hK (hm i) (hp i) (hb i)
    _ = _ := by simp; ring

lemma cubicEnvelope_nonneg {G K C : ℝ} (hG : 0≤G) (hK : 0≤K) (hC : 0≤C) (z : ℝ) :
    0 ≤ cubicEnvelope G K C z := by unfold cubicEnvelope; positivity

lemma measurable_cubicEnvelope (G K C : ℝ) : Measurable (cubicEnvelope G K C) := by
  unfold cubicEnvelope
  fun_prop

lemma abs_add_cube_memLp {Z : Ω → ℝ} (hz6 : MemLp (fun ω ↦ |Z ω|) 6 μ)
    {G : ℝ} (hG : 0≤G) [IsProbabilityMeasure μ] :
    MemLp (fun ω ↦ (|Z ω|+G)^3) 2 μ := by
  have hbase : MemLp (fun ω ↦ |Z ω|+G) 6 μ := hz6.add (memLp_const G)
  have hpow := hbase.norm_rpow_div 3
  have he : (6 : ℝ≥0∞)/3=2 := by
    change ((6 : ℝ≥0) : ℝ≥0∞)/((3 : ℝ≥0) : ℝ≥0∞)=((2 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.coe_div] <;> norm_num
  have hh : ∀ ω, ‖|Z ω|+G‖=|Z ω|+G := fun ω ↦ Real.norm_of_nonneg (by positivity)
  simpa only [hh, ENNReal.toReal_ofNat, Real.rpow_ofNat, he] using hpow

lemma cubicEnvelope_memLp_two [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) {G : ℝ} (hG : 0≤G) (K C : ℝ) :
    MemLp (fun ω ↦ cubicEnvelope G K C (Z ω)) 2 μ := by
  have hz6 : MemLp (fun ω ↦ |Z ω|) 6 μ := by
    simpa only [Real.norm_eq_abs] using (gaussian_memLp hZ 6 (by norm_num)).norm
  have hp := abs_add_cube_memLp hz6 hG
  have hz2 : MemLp (fun ω ↦ |Z ω|) 2 μ := hz6.mono_exponent (by norm_num)
  have hlin : MemLp (fun ω ↦ 1+|Z ω|+G) 2 μ := ((memLp_const (1 : ℝ)).add hz2).add (memLp_const G)
  have hlast : MemLp (fun ω ↦ |Z ω|+G/2) 2 μ := hz2.add (memLp_const (G/2))
  change MemLp (fun ω ↦ K*(|Z ω|+G)^3+C*(1+|Z ω|+G)+K*G*(|Z ω|+G/2)) 2 μ
  exact ((hp.const_mul K).add (hlin.const_mul C)).add (hlast.const_mul (K*G))

lemma cubicEnvelope_moment_eq {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) (G K C : ℝ) :
    (∫ ω, (cubicEnvelope G K C (Z ω))^2 ∂μ)=cubicEnvelopeMoment G K C :=
  hZ.integral_comp (f := fun z ↦ (cubicEnvelope G K C z)^2)
    ((measurable_cubicEnvelope G K C).pow_const 2).aestronglyMeasurable

lemma finite_sum_square_le {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i)^2≤(Fintype.card ι : ℝ)*(∑ i, (f i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι ↦ (1 : ℝ)) f
  simpa using h

lemma finite_envelope_L2_bound [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {P : ι → Ω → ℝ} {R : Ω → ℝ} {α β M : ℝ}
    (hα : 0≤α) (hβ : 0≤β) (hPm : ∀ i, MemLp (P i) 2 μ)
    (hPpos : ∀ i ω, 0≤P i ω) (hPval : ∀ i, (∫ ω, (P i ω)^2 ∂μ)≤M)
    (hRm : AEStronglyMeasurable R μ)
    (hR : ∀ ω, |R ω|≤α*(∑ i, P i ω)+β) :
    (∫ ω, (R ω)^2 ∂μ) ≤ 2*α^2*(Fintype.card ι : ℝ)^2*M+2*β^2 := by
  have hsum : MemLp (fun ω ↦ ∑ i, P i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hPm i)
  have henv : MemLp (fun ω ↦ α*(∑ i, P i ω)+β) 2 μ := (hsum.const_mul α).add (memLp_const β)
  have hsumpos (ω : Ω) : 0≤∑ i, P i ω := Finset.sum_nonneg (fun i _ ↦ hPpos i ω)
  have henvpos (ω : Ω) : 0≤α*(∑ i, P i ω)+β := add_nonneg (mul_nonneg hα (hsumpos ω)) hβ
  have hRmem : MemLp R 2 μ := henv.mono hRm (Filter.Eventually.of_forall (fun ω ↦ by
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (henvpos ω)]
    exact hR ω))
  have hbound : ∀ ω, (R ω)^2 ≤ 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)+2*β^2 := by
    intro ω
    have he : 0≤α*(∑ i, P i ω)+β := henvpos ω
    have hsq := (sq_le_sq₀ (abs_nonneg _) he).2 (hR ω)
    rw [sq_abs] at hsq
    have hfin := finite_sum_square_le (fun i ↦ P i ω)
    have hmul := mul_le_mul_of_nonneg_left hfin (show 0≤2*α^2 by positivity)
    nlinarith [sq_nonneg (α*(∑ i, P i ω)-β)]
  have hfirst : Integrable (fun ω ↦ 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)) μ :=
    (integrable_finsetSum Finset.univ (fun i _ ↦ (hPm i).integrable_sq)).const_mul _
  have heint : Integrable (fun ω ↦ 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)+2*β^2) μ :=
    hfirst.add (integrable_const _)
  calc
    _ ≤ ∫ ω, 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)+2*β^2 ∂μ :=
      integral_mono hRmem.integrable_sq heint hbound
    _ = 2*α^2*(Fintype.card ι : ℝ)*(∑ i, ∫ ω, (P i ω)^2 ∂μ)+2*β^2 := by
      rw [integral_add hfirst (integrable_const _)]
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ ↦ (hPm i).integrable_sq)]
      simp
    _ ≤ 2*α^2*(Fintype.card ι : ℝ)*(∑ _i : ι, M)+2*β^2 := by gcongr with i; exact hPval i
    _ = _ := by simp; ring

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_SumStepsSub
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
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma sum_steps_sub {N : ℕ} (U : ℕ → ℝ) :
    (∑ i : Fin N, (U (i+1)-U i))=U N-U 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ U (j+1)-U j)]
  exact Finset.sum_range_sub U N

lemma sum_local_residual {N : ℕ} (U : ℕ → ℝ) (V W : Fin N → ℝ) :
    (∑ i : Fin N, (U (i+1)-U i-V i-W i)) = U N-U 0-(∑ i, V i)-(∑ i, W i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_steps_sub]

lemma sum_local_residual_bound {N : ℕ} {U : ℕ → ℝ} {V W P : Fin N → ℝ}
    {Γ : ℕ → ℝ} {α β : ℝ}
    (hlocal : ∀ i : Fin N, |U (i+1)-U i-V i-W i|≤α*P i+β*(Γ (i+1)-Γ i)) :
    |U N-U 0-(∑ i, V i)-(∑ i, W i)|≤α*(∑ i, P i)+β*(Γ N-Γ 0) := by
  rw [← sum_local_residual]
  calc
    _ ≤ ∑ i : Fin N, |U (i+1)-U i-V i-W i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, (α*P i+β*(Γ (i+1)-Γ i)) := Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_steps_sub]

lemma finite_envelope_memLp [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {P : ι → Ω → ℝ} {R : Ω → ℝ} {α β : ℝ}
    (hα : 0≤α) (hβ : 0≤β) (hPm : ∀ i, MemLp (P i) 2 μ)
    (hPpos : ∀ i ω, 0≤P i ω) (hRm : AEStronglyMeasurable R μ)
    (hR : ∀ ω, |R ω|≤α*(∑ i, P i ω)+β) : MemLp R 2 μ := by
  have hsum : MemLp (fun ω ↦ ∑ i, P i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hPm i)
  have henv := (hsum.const_mul α).add (memLp_const β)
  apply henv.mono hRm
  filter_upwards [] with ω
  have hs : 0≤∑ i, P i ω := Finset.sum_nonneg (fun i _ ↦ hPpos i ω)
  have he : 0≤α*(∑ i, P i ω)+β := add_nonneg (mul_nonneg hα hs) hβ
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg he] using hR ω

lemma integral_square_add_le {R Q : Ω → ℝ} (hR : MemLp R 2 μ) (hQ : MemLp Q 2 μ) :
    (∫ ω, (R ω+Q ω)^2 ∂μ)≤2*(∫ ω, (R ω)^2 ∂μ)+2*(∫ ω, (Q ω)^2 ∂μ) := by
  calc
    _ ≤ ∫ ω, 2*(R ω)^2+2*(Q ω)^2 ∂μ := by
      apply integral_mono (hR.add hQ).integrable_sq
        ((hR.integrable_sq.const_mul 2).add (hQ.integrable_sq.const_mul 2))
      intro ω
      change (R ω+Q ω)^2≤2*(R ω)^2+2*(Q ω)^2
      nlinarith [sq_nonneg (R ω-Q ω)]
    _ = _ := by
      rw [integral_add (hR.integrable_sq.const_mul 2) (hQ.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]

lemma discrete_gradient_residual_L2 {N : ℕ} {δ G K C : ℝ} {Γ : ℕ → ℝ}
    {U : ℕ → (Fin (N+1) → ℝ) → ℝ}
    {A H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hδ : 0≤δ) (hG : 0≤G) (hK : 0≤K) (hC : 0≤C)
    (hΓ : Γ 0≤Γ N)
    (hUm : ∀ j ≤ N, Measurable (U j))
    (hAm : ∀ i, Measurable (A i))
    (hHm : ∀ i, Measurable (H i)) (hHp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hHb : ∀ i z, |H i z|≤K)
    (hloc : ∀ (i : Fin N) z,
      |U (i+1) z-U i z-Real.sqrt δ*A i z*coordinate N i z-
        (δ/2)*H i z*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope G K C (coordinate N i z)+δ*K*(Γ (i+1)-Γ i)) :
    (∫ z, (U N z-U 0 z-∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)^2
      ∂gaussianProduct (Fin (N+1))) ≤
      2*((δ/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(δ*Real.sqrt δ)^2*(N : ℝ)^2*cubicEnvelopeMoment G K C+
      4*(δ*K*(Γ N-Γ 0))^2 := by
  let P (i : Fin N) (z : Fin (N+1) → ℝ) := cubicEnvelope G K C (coordinate N i z)
  let Q (z : Fin (N+1) → ℝ) :=
    (δ/2)*(∑ i : Fin N, H i z*((coordinate N i z)^2-1))
  let R (z : Fin (N+1) → ℝ) :=
    U N z-U 0 z-(∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)-Q z
  have hPm (i : Fin N) : MemLp (P i) 2 (gaussianProduct (Fin (N+1))) :=
    cubicEnvelope_memLp_two (coordinate_hasLaw N i) hG K C
  have hPpos (i : Fin N) z : 0≤P i z := cubicEnvelope_nonneg hG hK hC _
  have hPval (i : Fin N) : (∫ z, (P i z)^2 ∂gaussianProduct (Fin (N+1))) ≤ cubicEnvelopeMoment G K C :=
    le_of_eq (cubicEnvelope_moment_eq (coordinate_hasLaw N i) G K C)
  have hQm : MemLp Q 2 (gaussianProduct (Fin (N+1))) :=
    (memLp_finsetSum Finset.univ (fun (i : Fin N) _ ↦
      predictableCenteredSquare_memLp (j := (i:ℕ)) (hHm i) (hHb i))).const_mul (δ/2)
  have hRm : Measurable R := by
    dsimp only [R, Q]
    exact ((hUm N le_rfl).sub (hUm 0 (Nat.zero_le _))).sub (Finset.measurable_fun_sum _ (fun i _ ↦
      ((hAm i).const_mul _).mul (measurable_coordinate N i))) |>.sub
        ((Finset.measurable_fun_sum _ (fun i _ ↦
          (hHm i).mul (((measurable_coordinate N i).pow_const 2).sub measurable_const))).const_mul _)
  have hRbound (z : Fin (N+1) → ℝ) :
      |R z|≤(δ*Real.sqrt δ)*(∑ i, P i z)+δ*K*(Γ N-Γ 0) := by
    have hb := sum_local_residual_bound (U := fun j ↦ U j z)
      (V := fun i ↦ Real.sqrt δ*A i z*coordinate N i z)
      (W := fun i ↦ (δ/2)*H i z*((coordinate N i z)^2-1))
      (P := fun i ↦ P i z) (Γ := Γ) (fun i ↦ hloc i z)
    simpa only [R, Q, P, mul_assoc, Finset.mul_sum] using hb
  have hβ : 0≤δ*K*(Γ N-Γ 0) := mul_nonneg (mul_nonneg hδ hK) (sub_nonneg.mpr hΓ)
  have hRmem := finite_envelope_memLp (by positivity : 0≤δ*Real.sqrt δ) hβ hPm hPpos
    hRm.aestronglyMeasurable hRbound
  have hRb := finite_envelope_L2_bound (by positivity : 0≤δ*Real.sqrt δ) hβ hPm hPpos hPval
    hRm.aestronglyMeasurable hRbound
  have hQb := predictableCenteredSquare_sum_bound (δ := δ) hK hHm hHp hHb
  have heq (z : Fin (N+1) → ℝ) : (U N z-U 0 z-∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)=
      R z+Q z := by dsimp only [R]; ring
  simp_rw [heq]
  have hb := integral_square_add_le hRmem hQm
  simp only [Fintype.card_fin] at hRb
  dsimp only [Q] at hb
  nlinarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ThirdOrderRemainderBound
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
namespace SKValue

lemma third_order_remainder_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 3 f) (hK : 0≤K)
    (hbound : ∀ x, |iteratedDeriv 3 f x|≤K) (x d : ℝ) :
    |f (x+d)-f x-deriv f x*d-(1/2 : ℝ)*deriv (deriv f) x*d^2| ≤ K*|d|^3 := by
  by_cases hd : d=0
  · simp [hd]
  have hne : x ≠ x+d := by
    intro hx
    apply hd
    linarith
  have hu := uniqueDiffOn_uIcc hne
  have hmem : x ∈ uIcc x (x+d) := left_mem_uIcc
  have h1 : iteratedDerivWithin 1 f (uIcc x (x+d)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f (uIcc x (x+d)) x = deriv (deriv f) x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      iteratedDeriv_succ, iteratedDeriv_one]
  have ht : taylorWithinEval f 2 (uIcc x (x+d)) x (x+d) =
      f x+deriv f x*d+(1/2 : ℝ)*deriv (deriv f) x*d^2 := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
    rw [h1, h2]
    norm_num
    ring
  obtain ⟨y,_,hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hne hf.contDiffOn
  rw [ht] at hy
  have heq : f (x+d)-f x-deriv f x*d-(1/2 : ℝ)*deriv (deriv f) x*d^2 =
      iteratedDeriv 3 f y*d^3/6 := by
    norm_num at hy
    linarith
  rw [heq, abs_div, abs_mul, abs_pow]
  norm_num
  have hh : |iteratedDeriv 3 f y| *|d|^3 ≤ K*|d|^3 :=
    mul_le_mul_of_nonneg_right (hbound y) (by positivity)
  have hp : 0≤K*|d|^3 := by positivity
  linarith

lemma gradient_generator_quadrature {γ : ℝ → ℝ} {b p : ℝ → ℝ → ℝ}
    {t δ x y G K L : ℝ} (hδ : 0 ≤ δ) (hG : 0 ≤ G) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0 ≤ γ t) (hγG : γ t ≤ G)
    (hp : ∀ s ∈ Icc t (t+δ), |p s y| ≤ K)
    (hbLip : ∀ s ∈ Icc t (t+δ), |b s y-b t x| ≤ L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), |p s y-p t x| ≤ L*(|s-t|+|y-x|))
    (hbint : IntervalIntegrable (fun s ↦ b s y) volume t (t+δ))
    (hpint : IntervalIntegrable (fun s ↦ γ s*p s y) volume t (t+δ)) :
    |(∫ s in t..(t+δ), (1/2 : ℝ)*b s y+γ s*p s y) -
        δ*((1/2 : ℝ)*b t x+γ t*p t x)| ≤
      δ*((1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t)) := by
  have het : t ∈ Icc t (t+δ) := ⟨le_rfl, by linarith⟩
  have heT : t+δ ∈ Icc t (t+δ) := ⟨by linarith, le_rfl⟩
  have hgap : 0 ≤ γ (t+δ)-γ t := sub_nonneg.mpr (hγ het heT (by linarith))
  have hpw : ∀ s ∈ Icc t (t+δ),
      |((1/2 : ℝ)*b s y+γ s*p s y)-((1/2 : ℝ)*b t x+γ t*p t x)| ≤
      (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t) := by
    intro s hs
    have hst := hγ het hs hs.1
    have hsT := hγ hs heT hs.2
    have hr : |s-t| ≤ δ := by rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    have hb' : |b s y-b t x| ≤ L*(δ+|y-x|) := (hbLip s hs).trans (by gcongr)
    have hp' : |p s y-p t x| ≤ L*(δ+|y-x|) := (hpLip s hs).trans (by gcongr)
    calc
      _ = |((1/2 : ℝ)*(b s y-b t x)+γ t*(p s y-p t x))+(γ s-γ t)*p s y| := by
        congr 1; ring
      _ ≤ |(1/2 : ℝ)*(b s y-b t x)|+|γ t*(p s y-p t x)|+|(γ s-γ t)*p s y| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = (1/2 : ℝ)*|b s y-b t x|+γ t*|p s y-p t x|+(γ s-γ t)*|p s y| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hγ0,
          abs_of_nonneg (sub_nonneg.mpr hst)]
        norm_num
      _ ≤ (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t) := by
        calc
          _ ≤ (1/2 : ℝ)*(L*(δ+|y-x|))+G*(L*(δ+|y-x|))+(γ (t+δ)-γ t)*K := by
            apply add_le_add
            · gcongr
            · calc
                _ ≤ (γ s-γ t)*K :=
                  mul_le_mul_of_nonneg_left (hp s hs) (sub_nonneg.mpr hst)
                _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hsT _) hK
          _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := t+δ)
    (f := fun s ↦ ((1/2 : ℝ)*b s y+γ s*p s y)-((1/2 : ℝ)*b t x+γ t*p t x))
    (C := (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t)) (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le (by linarith : t≤t+δ)] at hs
      exact hpw s ⟨hs.1.le, hs.2⟩)
  rw [intervalIntegral.integral_sub ((hbint.const_mul _).add hpint) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs,
    show t+δ-t=δ by ring, abs_of_nonneg hδ] at hi
  simpa only [mul_comm δ] using hi

lemma euler_cubic_remainder {δ G K C D c v a b vsp vend z : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤1) (hG : 0≤G) (hK : 0≤K) (hC : 0≤C)
    (hc : |c|≤G) (hv : |v|≤1) (hb : |b|≤K)
    (hsp : |vsp-v-a*(Real.sqrt δ*z+δ*c*v)-
      (1/2 : ℝ)*b*(Real.sqrt δ*z+δ*c*v)^2| ≤ K*|Real.sqrt δ*z+δ*c*v|^3)
    (htm : |vend-vsp+δ*((1/2 : ℝ)*b+c*v*a)| ≤
      δ*(C*(δ+|Real.sqrt δ*z+δ*c*v|)+K*D)) :
    |vend-v-a*Real.sqrt δ*z-(1/2 : ℝ)*δ*b*(z^2-1)| ≤
      δ*Real.sqrt δ*(K*(|z|+G)^3+C*(1+|z|+G)+K*G*(|z|+G/2))+δ*K*D := by
  let η := Real.sqrt δ
  let d := η*z+δ*c*v
  have hη : 0≤η := Real.sqrt_nonneg _
  have hηsq : η^2=δ := Real.sq_sqrt hδ
  have hη1 : η≤1 := (Real.sqrt_le_one).2 hδ1
  have hδη : δ≤η := by nlinarith
  have hcv : |c*v|≤G := by
    rw [abs_mul]
    calc |c| *|v| ≤ G*1 := mul_le_mul hc hv (abs_nonneg _) hG
         _ = G := mul_one _
  have hdcv : |δ*c*v|≤δ*G := by
    rw [mul_assoc δ, abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left hcv hδ
  have hd : |d|≤η*(|z|+G) := by
    calc
      |d| ≤ |η*z|+|δ*c*v| := abs_add_le _ _
      _ ≤ η*|z|+δ*G := by rw [abs_mul, abs_of_nonneg hη]; gcongr
      _ ≤ η*(|z|+G) := by nlinarith
  have hcube : K*|d|^3 ≤ δ*η*(K*(|z|+G)^3) := by
    calc
      _ ≤ K*(η*(|z|+G))^3 := by gcongr
      _ = _ := by rw [← hηsq]; ring
  have htbound : δ*(C*(δ+|d|)+K*D) ≤ δ*η*(C*(1+|z|+G))+δ*K*D := by
    have hh : δ+|d| ≤ η*(1+|z|+G) := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hδ hC)
    nlinarith
  have hcross : |(1/2 : ℝ)*b*(d^2-δ*z^2)| ≤ δ*η*(K*G*(|z|+G/2)) := by
    have heq : d^2-δ*z^2 = (δ*c*v)*(2*η*z+δ*c*v) := by
      dsimp only [d]
      rw [← hηsq]
      ring
    have hsum : |2*η*z+δ*c*v| ≤ η*(2*|z|+G) := by
      calc
        _ ≤ |2*η*z|+|δ*c*v| := abs_add_le _ _
        _ ≤ 2*η*|z|+δ*G := by
          rw [abs_mul (2*η), abs_of_nonneg (by positivity : 0≤2*η)]
          gcongr
        _ ≤ η*(2*|z|+G) := by nlinarith
    rw [heq, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ)≤1/2)]
    calc
      _ ≤ (1/2 : ℝ)*K*((δ*G)*(η*(2*|z|+G))) := by gcongr
      _ = _ := by ring
  have heq : vend-v-a*η*z-(1/2 : ℝ)*δ*b*(z^2-1) =
      (vsp-v-a*d-(1/2 : ℝ)*b*d^2)+(vend-vsp+δ*((1/2 : ℝ)*b+c*v*a))+
        (1/2 : ℝ)*b*(d^2-δ*z^2) := by dsimp only [d]; ring
  change |vend-v-a*η*z-(1/2 : ℝ)*δ*b*(z^2-1)| ≤ _
  rw [heq]
  calc
    _ ≤ |vsp-v-a*d-(1/2 : ℝ)*b*d^2|+|vend-vsp+δ*((1/2 : ℝ)*b+c*v*a)|+
        |(1/2 : ℝ)*b*(d^2-δ*z^2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K*|d|^3+δ*(C*(δ+|d|)+K*D)+δ*η*(K*G*(|z|+G/2)) := by gcongr
    _ ≤ δ*η*(K*(|z|+G)^3+C*(1+|z|+G)+K*G*(|z|+G/2))+δ*K*D := by linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientStrip
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
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma mesh_mem_strip_ito {δ T : ℝ} {N j : ℕ} (hδ : 0≤δ)
    (horizon : (N : ℝ)*δ=T) (hj : j≤N) : (j : ℝ)*δ∈Icc (0 : ℝ) T := by
  constructor
  · positivity
  · rw [← horizon]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientErrorConstant
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
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma gaussian_mesh_bound_linear {δ T n K V M J : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hmesh : n*δ=T) :
    2*((δ/2)^2*n*K^2*V)+4*(δ*Real.sqrt δ)^2*n^2*M+4*(δ*K*J)^2 ≤
      δ*(T/2*K^2*V+4*T^2*M+4*K^2*J^2) := by
  have hfirst : 2*((δ/2)^2*n*K^2*V)=δ*(T/2*K^2*V) := by rw [← hmesh]; ring
  have hsecond : 4*(δ*Real.sqrt δ)^2*n^2*M=δ*(4*T^2*M) := by
    rw [mul_pow, Real.sq_sqrt hδ, ← hmesh]
    ring
  have hd2 : δ^2≤δ := by nlinarith
  have hthird := mul_le_mul_of_nonneg_right hd2 (show 0≤4*K^2*J^2 by positivity)
  rw [hfirst, hsecond]
  nlinarith

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshRaw
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
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma mesh_time_mem {T : ℝ} (hT : 0≤T) {N j : ℕ} (hN : 0<N) (hj : j≤N) :
    meshTime T N j∈Icc (0 : ℝ) T := by
  apply mesh_mem_strip_ito (δ := stepSize T N) (div_nonneg hT (Nat.cast_nonneg N)) _ hj
  have hNr : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold stepSize
  field_simp

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_AestronglyMeasurableInitialMax
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
open scoped Topology BigOperators

lemma aestronglyMeasurable_initialMax_on {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} (n : ℕ) (hf : ∀ j≤n, AEStronglyMeasurable (f j) μ) :
    AEStronglyMeasurable (fun ω ↦ initialMax (fun j ↦ f j ω) n) μ := by
  induction n with
  | zero => exact hf 0 le_rfl
  | succ n ih => exact (ih (fun j hj ↦ hf j (by omega))).sup (hf (n+1) le_rfl)

lemma mesh_time_mem_total {T : ℝ} (hT : 0≤T) {N j : ℕ} (hj : j≤N) :
    meshTime T N j∈Icc (0 : ℝ) T := by
  by_cases hN : N=0
  · subst N
    simp only [meshTime, stepSize, Nat.cast_zero, div_zero, mul_zero]
    exact ⟨le_rfl,hT⟩
  · exact mesh_time_mem hT (Nat.pos_of_ne_zero hN) hj

lemma meshMaxError_measurable_on {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : ℝ} {X : ℝ → Ω → ℝ} {Y : ℕ → ℕ → Ω → ℝ} (hT : 0≤T)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hYM : ∀ N j, j≤N → AEStronglyMeasurable (Y N j) μ) (N : ℕ) :
    AEStronglyMeasurable (meshMaxError T X Y N) μ := by
  apply aestronglyMeasurable_initialMax_on
  intro j hj
  exact ((hYM N j hj).sub (hXM _ (mesh_time_mem_total hT hj))).norm

lemma driven_euler_L2_convergence_on {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {T L : ℝ} {u : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {W X : ℝ → Ω → ℝ} {Y : ℕ → ℕ → Ω → ℝ}
    (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0 ≤ γ 0)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |u t x| ≤ 1)
    (hLip : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y| ≤ L*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hYM : ∀ N j, j≤N → AEStronglyMeasurable (Y N j) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        X t ω = W t ω + ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω = 0)
    (hY0 : ∀ N ω, Y N 0 ω = 0)
    (hY : ∀ N > 0, ∀ j < N, ∀ ω,
      Y N (j+1) ω = Y N j ω + W (((j+1 : ℕ) : ℝ)*(T/N)) ω-W ((j : ℝ)*(T/N)) ω +
        (T/N)*γ ((j : ℝ)*(T/N))*u ((j : ℝ)*(T/N)) (Y N j ω)) :
    Tendsto (fun N ↦ ∫ ω, (meshMaxError T X Y N ω)^2 ∂μ) atTop (𝓝 (0 : ℝ)) := by
  have hmeas : ∀ N, AEStronglyMeasurable (fun ω ↦ (meshMaxError T X Y N ω)^2) μ := by
    intro N
    exact (meshMaxError_measurable_on hT hXM hYM N).fun_pow 2
  have hbound : ∀ᶠ N in atTop, ∀ᵐ ω ∂μ,
      ‖(meshMaxError T X Y N ω)^2‖ ≤ (2*T*γ T)^2 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    filter_upwards [hpaths] with ω hω
    have hδ : 0 ≤ T/(N : ℝ) := div_nonneg hT (Nat.cast_nonneg _)
    have horizon : (N : ℝ)*(T/N) = T := by field_simp
    have H := driven_euler_uniform_bound (Y := fun j ↦ Y N j ω) hδ hT horizon hγ hγ0 hu hω.2.2.1 hω.2.2.2
      (hY0 N ω) (fun j hj ↦ hY N hN j hj ω)
    have he : meshMaxError T X Y N ω ≤ 2*T*γ T := initialMax_le_iff.mpr H
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (meshMaxError_nonneg T X Y N ω) he 2
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun N ↦ (meshMaxError T X Y N ω)^2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hpaths] with ω hω
    have H := driven_euler_uniform_convergence (Y := fun N j ↦ Y N j ω) hT hL hγ hγ0 hu hLip hω.1 hω.2.1 hω.2.2.1
      hω.2.2.2 (fun N ↦ hY0 N ω) (fun N hN j hj ↦ hY N hN j hj ω)
    have hzero : Tendsto (fun N ↦ meshMaxError T X Y N ω) atTop (𝓝 (0 : ℝ)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [H ε hε] with N hN
      rw [Real.dist_eq,sub_zero,abs_of_nonneg (meshMaxError_nonneg T X Y N ω)]
      exact initialMax_lt_iff.mpr hN
    simpa using hzero.pow 2
  have H := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω ↦ (2*T*γ T)^2)
    (Eventually.of_forall hmeas) hbound (integrable_const _) hlim
  simpa using H

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
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_BrownianCoordinates
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma brownian_grid_variance (δ : ℝ≥0) (j : ℕ) :
    nndist (↑(((j+1 : ℕ) : ℝ≥0)*δ) : ℝ) (↑((j : ℝ≥0)*δ) : ℝ) = δ := by
  apply NNReal.coe_injective
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  rw [Real.dist_eq]
  have heq : ((j : ℝ)+1)*(δ : ℝ)-(j : ℝ)*δ=δ := by ring
  rw [heq]
  exact abs_of_nonneg δ.property

lemma brownian_coordinate_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {δ : ℝ≥0} (hδ : 0 < δ)
    (n : ℕ) (j : Fin n) :
    HasLaw (fun ω ↦ brownianCoordinates B δ n ω j) standardGaussian μ := by
  have h := gaussianReal_div_const (hB.hasLaw_sub (((j : ℕ)+1 : ℕ)*δ) ((j : ℕ)*δ))
    (Real.sqrt δ)
  erw [brownian_grid_variance δ (j : ℕ)] at h
  have hs : (⟨(Real.sqrt δ)^2, sq_nonneg _⟩ : ℝ≥0) = δ := by
    apply NNReal.coe_injective
    exact Real.sq_sqrt δ.property
  have heq : NNReal.mk ((Real.sqrt (δ : ℝ))^2) (sq_nonneg _) = δ := hs
  rw [heq, div_self (ne_of_gt hδ)] at h
  simpa only [brownianCoordinates, standardGaussian, zero_div, Pi.sub_apply] using h

lemma brownian_coordinates_independent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (δ : ℝ≥0) (n : ℕ) :
    iIndepFun (fun j (ω : Ω) ↦ brownianCoordinates B δ n ω j) μ := by
  have hmono : Monotone (fun j : Fin (n+1) ↦ (j : ℕ)*δ) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have h := (hB.hasIndepIncrements n (fun j : Fin (n+1) ↦ (j : ℕ)*δ) hmono).comp
    (fun (_ : Fin n) (x : ℝ) ↦ x / Real.sqrt δ) (fun _ ↦ measurable_id.div_const _)
  simpa only [brownianCoordinates, Fin.val_succ, Fin.val_castSucc, Function.comp_def] using h

lemma brownian_coordinates_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {δ : ℝ≥0} (hδ : 0 < δ)
    (n : ℕ) :
    HasLaw (brownianCoordinates B δ n) (gaussianProduct (Fin n)) μ := by
  exact iIndepFun.hasLaw_pi (fun j ↦ brownian_coordinate_hasLaw hB hδ n j)
    (brownian_coordinates_independent hB δ n)

lemma brownian_coordinate_exact {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {δ : ℝ≥0}
    (hδ : 0 < δ) (n : ℕ) (ω : Ω) (j : Fin n) :
    Real.sqrt δ * brownianCoordinates B δ n ω j =
      B (((j : ℕ)+1 : ℕ)*δ) ω-B ((j : ℕ)*δ) ω := by
  have hs : Real.sqrt (δ : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hδ)
  simp only [brownianCoordinates]
  field_simp

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_CoupledCoordinates
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
open scoped Topology BigOperators

lemma coupledCoordinates_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) : HasLaw (coupledCoordinates T N B) (gaussianProduct (Fin (N+1))) μ := by
  apply brownian_coordinates_hasLaw hB
  exact Real.toNNReal_pos.mpr (div_pos hT (Nat.cast_pos.mpr hN))

lemma coupled_euler_measurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hT : 0<T)
    (h : GradientStrip T γ u K L) (N j : ℕ) (hj : j≤N) :
    AEStronglyMeasurable (coupledEuler T γ u B N j) μ := by
  change AEStronglyMeasurable (fun ω ↦ if N=0 then 0 else euler T N γ u (coupledCoordinates T N B ω) j) μ
  by_cases hN : N=0
  · simp only [ite_eq_left hN]
    exact aestronglyMeasurable_const
  · have hNpos := Nat.pos_of_ne_zero hN
    simp only [ite_eq_right hN]
    exact ((measurable_euler T N γ u (fun k hk ↦
      (h.smooth _ (mesh_time_mem hT.le hNpos hk.le)).continuous.measurable) j hj).comp_aemeasurable
        (coupledCoordinates_hasLaw hB hT hNpos).aemeasurable).aestronglyMeasurable

lemma coupled_euler_zero {Ω : Type*} (T : ℝ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (N : ℕ) (ω : Ω) : coupledEuler T γ u B N 0 ω=0 := by
  simp only [coupledEuler, euler, ite_self]

lemma coupled_coordinate_exact {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j<N+1) (ω : Ω) :
    Real.sqrt (T/N)*coordinate N j (coupledCoordinates T N B ω)=
      B (Real.toNNReal (((j+1 : ℕ) : ℝ)*(T/N))) ω-B (Real.toNNReal ((j : ℝ)*(T/N))) ω := by
  have hδ : 0<T/(N : ℝ) := div_pos hT (Nat.cast_pos.mpr hN)
  rw [coordinate_eq_apply hj]
  simp only [Real.toNNReal_mul (Nat.cast_nonneg (j+1)), Real.toNNReal_mul (Nat.cast_nonneg j),
    Real.toNNReal_natCast]
  simpa only [coupledCoordinates, Real.coe_toNNReal _ hδ.le, Fin.val_mk] using
    brownian_coordinate_exact B (Real.toNNReal_pos.mpr hδ) (N+1) ω ⟨j,hj⟩

lemma coupled_euler_step {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ} (hT : 0<T)
    (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j<N) (ω : Ω) :
    coupledEuler T γ u B N (j+1) ω = coupledEuler T γ u B N j ω +
      B (Real.toNNReal (((j+1 : ℕ) : ℝ)*(T/N))) ω-B (Real.toNNReal ((j : ℝ)*(T/N))) ω+
      (T/N)*γ ((j : ℝ)*(T/N))*u ((j : ℝ)*(T/N)) (coupledEuler T γ u B N j ω) := by
  simp only [coupledEuler, ite_eq_right (Nat.ne_of_gt hN), euler, stepSize, meshTime]
  rw [coupled_coordinate_exact B hT hN (by omega) ω]
  ring

lemma coupled_euler_L2_convergence {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hLu : 0≤Lu)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0) :
    Tendsto (fun N ↦ ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ)
      atTop (𝓝 (0 : ℝ)) :=
  driven_euler_L2_convergence_on hT.le hLu h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩)
    h.bounded hLip hXM (coupled_euler_measurable hB hT h) hpaths
    (coupled_euler_zero T γ u B) (fun _N hN _j hj ω ↦ coupled_euler_step B hT γ u hN hj ω)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_FirstMomentPerturbation
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
open scoped Topology BigOperators

lemma first_moment_perturbation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g e : Ω → ℝ} {L : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (he : MemLp e 2 μ) (hL : 0≤L)
    (hbound : ∀ᵐ ω ∂μ, |f ω-g ω|≤L*|e ω|) :
    |(∫ ω, f ω ∂μ)-(∫ ω, g ω ∂μ)|≤L*Real.sqrt (∫ ω, (e ω)^2 ∂μ) := by
  have hfi := hf.integrable (by norm_num : (1 : ENNReal)≤2)
  have hgi := hg.integrable (by norm_num : (1 : ENNReal)≤2)
  have hei := he.integrable (by norm_num : (1 : ENNReal)≤2)
  calc
    _ = |∫ ω, f ω-g ω ∂μ| := by rw [integral_sub hfi hgi]
    _ ≤ ∫ ω, |f ω-g ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, L*|e ω| ∂μ := integral_mono_ae (hfi.sub hgi).abs (hei.abs.const_mul L) hbound
    _ = L*(∫ ω, |e ω| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq he) hL

lemma coupled_mesh_error_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) : MemLp (meshMaxError T X (coupledEuler T γ u B) N) 2 μ := by
  apply MemLp.of_bound (meshMaxError_measurable_on hT.le hXM (coupled_euler_measurable hB hT h) N) (2*T*γ T)
  filter_upwards [hpaths] with ω hω
  have hδ : 0≤T/(N : ℝ) := div_nonneg hT.le (Nat.cast_nonneg N)
  have hmesh : (N : ℝ)*(T/N)=T := by field_simp
  have hb := driven_euler_uniform_bound (Y := fun j ↦ coupledEuler T γ u B N j ω)
    hδ hT.le hmesh h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩)
    h.bounded hω.1 hω.2 (coupled_euler_zero T γ u B N ω)
    (fun j hj ↦ coupled_euler_step B hT γ u hN hj ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (meshMaxError_nonneg T X (coupledEuler T γ u B) N ω)]
  exact initialMax_le_iff.mpr hb

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TerminalError
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

lemma gradient_bound (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) : |gradient W γ t x|≤1 := by
  simpa only [gradient, Real.norm_eq_abs, NNReal.coe_one] using
    norm_deriv_le_of_lipschitz (x₀ := x) (phi_lipschitz W γ ht)

lemma terminalError_continuous (γ : OrderParameter) : Continuous (terminalError γ) := by
  have hi : Continuous (fun t ↦ ∫ s in t..1, γ.cutoff s) := by
    convert (γ.cutoff_integrable.continuous_primitive 1).neg using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    simpa only [Pi.neg_apply] using intervalIntegral.integral_symm (μ := volume) (f := γ.cutoff) 1 t
  exact (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).add (continuous_const.mul hi)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_Measurable
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

lemma IsDiffusion.measurable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    Measurable (X t) := by
  simpa only [Real.coe_toNNReal t ht.1, min_eq_left ht.2] using
    (hX.1 t.toNNReal).mono (W.filtration.le t.toNNReal) le_rfl

lemma drift_integral_bound (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ → ℝ) :
    |∫ s in (0 : ℝ)..t, γ.coeff s*gradient W γ s (x s)|≤∫ s in (0 : ℝ)..1, γ.cutoff s := by
  have he : (∫ s in (0 : ℝ)..t, γ.coeff s*gradient W γ s (x s)) =
      ∫ s in (0 : ℝ)..t, γ.cutoff s*gradient W γ s (x s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    change γ.coeff s*gradient W γ s (x s)=γ.cutoff s*gradient W γ s (x s)
    have hs' : s∈Ico (0 : ℝ) 1 := ⟨hs.1.le,hs.2.trans_le ht.2⟩
    rw [OrderParameter.cutoff, Set.indicator_of_mem hs']
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le ht.1
    (f := fun s ↦ γ.cutoff s*gradient W γ s (x s))
    (Eventually.of_forall (fun s hs ↦ by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (γ.cutoff_nonneg s)]
      exact (mul_le_mul_of_nonneg_left (gradient_bound W γ ⟨hs.1.le,hs.2.trans ht.2⟩ (x s))
        (γ.cutoff_nonneg s)).trans_eq (mul_one _)))
    (γ.cutoff_integrable.intervalIntegrable (a := 0) (b := t))
  have hm := intervalIntegral.integral_mono_interval (c := (0 : ℝ)) (d := 1) le_rfl ht.1 ht.2
    (Eventually.of_forall (fun s ↦ γ.cutoff_nonneg s)) γ.cutoff_integrable.intervalIntegrable
  rw [Real.norm_eq_abs] at hb
  exact hb.trans hm

lemma IsDiffusion.drift_bound {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    ∀ᵐ ω ∂W.μ, ∀ t∈Icc (0 : ℝ) 1,
      |X t ω-W.B t.toNNReal ω|≤∫ s in (0 : ℝ)..1, γ.cutoff s := by
  filter_upwards [hX.2] with ω hω t ht
  rw [hω.2 t ht, add_sub_cancel_left]
  exact drift_integral_bound W γ ht (fun s ↦ X s ω)

lemma IsDiffusion.memLp {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1)
    {p : ℝ≥0∞} (hp : p≠∞) : MemLp (X t) p W.μ := by
  have hd : MemLp (fun ω ↦ X t ω-W.B t.toNNReal ω) p W.μ :=
    MemLp.of_bound ((hX.measurable ht).sub (W.measurable _).measurable).aestronglyMeasurable
      (∫ s in (0 : ℝ)..1, γ.cutoff s) (hX.drift_bound.mono (fun ω hω ↦ by
        simpa only [Real.norm_eq_abs] using hω t ht))
  have hb := (W.brownian.hasLaw_eval t.toNNReal).hasGaussianLaw.memLp hp
  convert hd.add hb using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  simp only [Pi.add_apply, sub_add_cancel]

lemma eventually_time_mem : ∀ᶠ t : ℝ in 𝓝[<] 1, t∈Icc (0 : ℝ) 1 := by
  filter_upwards [Ico_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with t ht
  exact ⟨ht.1,ht.2.le⟩

lemma IsDiffusion.ae_tendsto {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    ∀ᵐ ω ∂W.μ, Tendsto (fun t ↦ X t ω) (𝓝[<] (1 : ℝ)) (𝓝 (X 1 ω)) := by
  have ht : Tendsto (id : ℝ → ℝ) (𝓝[<] 1) (𝓝[Icc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds,eventually_time_mem⟩
  filter_upwards [hX.2] with ω hω
  exact Tendsto.comp (hω.1 1 (by norm_num : (1 : ℝ)∈Icc (0 : ℝ) 1)) ht

lemma IsDiffusion.L2_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    Tendsto (fun t ↦ ∫ ω, (X t ω-X 1 ω)^2 ∂W.μ) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let D (t : ℝ) (ω : W.Ω) := X t ω-W.B t.toNNReal ω
  let G := ∫ s in (0 : ℝ)..1, γ.cutoff s
  have hG : 0≤G := intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun s ↦ γ.cutoff_nonneg s)
  have hD (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : MemLp (D t) 2 W.μ :=
    (hX.memLp ht (by norm_num)).sub ((W.brownian.hasLaw_eval t.toNNReal).hasGaussianLaw.memLp_two)
  have hD1 := hD 1 (by norm_num)
  have hDb : ∀ᵐ ω ∂W.μ, ∀ t∈Icc (0 : ℝ) 1, |D t ω|≤G := hX.drift_bound
  have hDC : ∀ᵐ ω ∂W.μ, Tendsto (fun t ↦ D t ω) (𝓝[<] (1 : ℝ)) (𝓝 (D 1 ω)) := by
    filter_upwards [hX.ae_tendsto,W.brownian.cont] with ω hω hBω
    exact hω.sub ((hBω.comp continuous_real_toNNReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hDL : Tendsto (fun t ↦ ∫ ω, (D t ω-D 1 ω)^2 ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := W.μ) (l := 𝓝[<] (1 : ℝ)) (F := fun t ω ↦ (D t ω-D 1 ω)^2) (f := fun _ ↦ (0 : ℝ))
      (fun _ ↦ 4*G^2) ?_ ?_ (integrable_const (4*G^2)) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [eventually_time_mem] with t ht
      exact ((hD t ht).sub hD1).aestronglyMeasurable.aemeasurable.pow_const 2 |>.aestronglyMeasurable
    · filter_upwards [eventually_time_mem] with t ht
      filter_upwards [hDb] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h0 := abs_le.mp (hω t ht)
      have h1 := abs_le.mp (hω 1 (by norm_num))
      nlinarith [sq_nonneg (D t ω-D 1 ω), sq_nonneg (G-(D t ω-D 1 ω)/2),
        sq_nonneg (G+(D t ω-D 1 ω)/2), mul_nonneg (show 0≤2*G-(D t ω-D 1 ω) by linarith)
          (show 0≤2*G+(D t ω-D 1 ω) by linarith)]
    · filter_upwards [hDC] with ω hω
      simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ)≠0)] using (hω.sub (tendsto_const_nhds (x := D 1 ω))).pow 2
  have hb : ∀ t∈Icc (0 : ℝ) 1,
      (∫ ω, (X t ω-X 1 ω)^2 ∂W.μ) ≤
      2*(∫ ω, (D t ω-D 1 ω)^2 ∂W.μ)+2*(1-t) := by
    intro t ht
    have hxint := ((hX.memLp ht (by norm_num : (2 : ℝ≥0∞)≠∞)).sub
      (hX.memLp (by norm_num : (1 : ℝ)∈Icc (0 : ℝ) 1) (by norm_num))).integrable_sq
    have hdint : Integrable (fun ω ↦ (D t ω-D 1 ω)^2) W.μ := ((hD t ht).sub hD1).integrable_sq
    have hbint := (brownian_increment_memLp W t).integrable_sq
    calc
      _ ≤ ∫ ω, 2*(D t ω-D 1 ω)^2+2*(W.B 1 ω-W.B t.toNNReal ω)^2 ∂W.μ := by
        apply integral_mono hxint ((hdint.const_mul 2).add (hbint.const_mul 2))
        intro ω
        dsimp only [D,Pi.add_apply,Pi.sub_apply]
        simp only [Real.toNNReal_one]
        nlinarith [sq_nonneg (X t ω-W.B t.toNNReal ω-(X 1 ω-W.B 1 ω)+(W.B 1 ω-W.B t.toNNReal ω))]
      _ = _ := by
        rw [integral_add (hdint.const_mul 2) (hbint.const_mul 2), integral_const_mul,
          integral_const_mul, brownian_increment_second W ht]
  apply squeeze_zero' (Eventually.of_forall (fun t ↦ integral_nonneg (fun ω ↦ sq_nonneg _)))
    (eventually_time_mem.mono (fun t ht ↦ hb t ht))
  simpa only [sub_self, mul_zero, add_zero,id_eq] using
    (hDL.const_mul 2).add (((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (id : ℝ → ℝ) (𝓝[<] 1) (𝓝 1))).const_mul 2)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_IntegralAbsSqrtSecond
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

lemma integral_abs_le_sqrt_second {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ)≤Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have hab : MemLp (fun ω ↦ |f ω|) 2 μ := by simpa only [Real.norm_eq_abs] using hf.norm
  have hv := variance_nonneg (fun ω ↦ |f ω|) μ
  rw [variance_eq_sub hab] at hv
  simp only [Pi.pow_apply,sq_abs] at hv
  apply (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _)) (integral_nonneg (fun _ ↦ sq_nonneg _))).mpr
  linarith

lemma IsDiffusion.L1_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    Tendsto (fun t ↦ ∫ ω, |X t ω-X 1 ω| ∂W.μ) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  apply squeeze_zero' (Eventually.of_forall (fun t ↦ integral_nonneg (fun _ ↦ abs_nonneg _))) ?_
    (by simpa only [Real.sqrt_zero,Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hX.L2_terminal)
  filter_upwards [eventually_time_mem] with t ht
  exact integral_abs_le_sqrt_second ((hX.memLp ht (by norm_num)).sub
    (hX.memLp (by norm_num : (1 : ℝ)∈Icc (0 : ℝ) 1) (by norm_num)))

lemma IsDiffusion.phi_integrable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    Integrable (fun ω ↦ phi W γ t (X t ω)) W.μ := by
  have hi := (hX.memLp ht (p := 1) (by norm_num)).integrable le_rfl
  apply (hi.abs.add (integrable_const (terminalError γ t))).mono'
    (((phi_lipschitz W γ ht).continuous.measurable.comp (hX.measurable ht)).aestronglyMeasurable)
  filter_upwards [] with ω
  dsimp only [Function.comp_apply,Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg ((abs_nonneg _).trans (phi_lower W γ ht (X t ω)))]
  have h := (phi_terminal_bound W γ ht (X t ω)).2
  change _≤terminalError γ t at h
  linarith

lemma IsDiffusion.phi_expectation_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) :
    Tendsto (fun t ↦ ∫ ω, phi W γ t (X t ω) ∂W.μ) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ ω, |X 1 ω| ∂W.μ)) := by
  have h1 : Integrable (X 1) W.μ := (hX.memLp (by norm_num) (p := 1) (by norm_num)).integrable le_rfl
  have hb : ∀ t∈Icc (0 : ℝ) 1,
      |(∫ ω, phi W γ t (X t ω) ∂W.μ)-(∫ ω, |X 1 ω| ∂W.μ)|≤
      terminalError γ t+(∫ ω, |X t ω-X 1 ω| ∂W.μ) := by
    intro t ht
    have hp := hX.phi_integrable ht
    have hi : Integrable (X t) W.μ := (hX.memLp ht (p := 1) (by norm_num)).integrable le_rfl
    have hdiff : Integrable (fun ω ↦ |X t ω-X 1 ω|) W.μ := (hi.sub h1).abs
    calc
      _ = |∫ ω, (phi W γ t (X t ω)-|X 1 ω|) ∂W.μ| := by rw [integral_sub hp h1.abs]
      _ ≤ ∫ ω, |phi W γ t (X t ω)-(|X 1 ω|)| ∂W.μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, terminalError γ t+|X t ω-X 1 ω| ∂W.μ := by
        apply integral_mono (hp.sub h1.abs).abs ((integrable_const _).add (hi.sub h1).abs)
        intro ω
        dsimp only [Pi.add_apply,Pi.sub_apply]
        have hphi := phi_terminal_bound W γ ht (X t ω)
        have hz : |phi W γ t (X t ω)-(|X t ω|)|≤terminalError γ t := by
          rw [abs_of_nonneg hphi.1]
          exact hphi.2
        have he : phi W γ t (X t ω)-|X 1 ω| =
            (phi W γ t (X t ω)-|X t ω|)+(|X t ω|-|X 1 ω|) := by ring
        rw [he]
        exact (abs_add_le _ _).trans (add_le_add hz (abs_abs_sub_abs_le_abs_sub _ _))
      _ = _ := by
        rw [integral_add (integrable_const (terminalError γ t)) hdiff, integral_const]
        simp
  have he : Tendsto (fun t ↦ terminalError γ t) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [terminalError_one] using ((terminalError_continuous γ).tendsto 1).mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun t ↦ |(∫ ω, phi W γ t (X t ω) ∂W.μ)-(∫ ω, |X 1 ω| ∂W.μ)|)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
    squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _))
      (eventually_time_mem.mono (fun t ht ↦ hb t ht)) (by simpa only [add_zero] using he.add hX.L1_terminal)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hh)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_MonotoneWeightedGridBound
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
open MeasureTheory Set Filter
open scoped Topology BigOperators

lemma monotone_weighted_grid_bound {γ f : ℝ → ℝ} {T δ K ε : ℝ} {N : ℕ}
    (hδ : 0≤δ) (hK : 0≤K) (horizon : (N : ℝ)*δ=T)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hfB : ∀ s∈Icc (0 : ℝ) T, |f s|≤K)
    (hmod : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      |s-t|≤δ → |f s-f t|≤ε) :
    |δ*(∑ j ∈ Finset.range N, γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
      ∫ t in (0 : ℝ)..T, γ t*f t| ≤ T*γ T*ε+δ*K*(γ T-γ 0) := by
  have hT : 0≤T := by rw [←horizon]; positivity
  have hm (j : ℕ) (hj : j≤N) : (j : ℝ)*δ∈Icc (0 : ℝ) T := by
    constructor
    · positivity
    · rw [←horizon]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
  have hs (j : ℕ) (hj : j<N) : Icc ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ)⊆Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨(hm j hj.le).1.trans ht.1, ht.2.trans (hm (j+1) (by omega)).2⟩
  have hjle (j : ℕ) : (j : ℝ)*δ≤((j+1 : ℕ) : ℝ)*δ := by push_cast; nlinarith
  have hint0 : IntervalIntegrable (fun t ↦ γ t*f t) volume 0 T := by
    apply MonotoneOn.intervalIntegrable (by simpa only [uIcc_of_le hT] using hγ) |>.mul_continuousOn
    simpa only [uIcc_of_le hT] using hf
  have hint (j : ℕ) (hj : j<N) : IntervalIntegrable (fun t ↦ γ t*f t) volume
      ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) :=
    hint0.mono_set (by rw [uIcc_of_le hT]; exact uIcc_subset_Icc (hm j hj.le) (hm (j+1) (by omega)))
  have heq : (∑ j ∈ Finset.range N, ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t) =
      ∫ t in (0 : ℝ)..T, γ t*f t := by
    simpa only [Nat.cast_zero, zero_mul, horizon] using intervalIntegral.sum_integral_adjacent_intervals hint
  have hloc (j : ℕ) (hj : j<N) :
      |δ*(γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
        ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t| ≤
      δ*(γ T*ε+K*(γ (((j+1 : ℕ) : ℝ)*δ)-γ ((j : ℝ)*δ))) := by
    let a := (j : ℝ)*δ
    let b := ((j+1 : ℕ) : ℝ)*δ
    have hγa : 0≤γ a := hγ0.trans (hγ ⟨le_rfl,hT⟩ (hm j hj.le) (hm j hj.le).1)
    have hγaT : γ a≤γ T := hγ (hm j hj.le) ⟨hT,le_rfl⟩ (hm j hj.le).2
    have hc : (∫ t in a..b, γ a*f a-γ t*f t) =
        δ*(γ a*f a)-∫ t in a..b, γ t*f t := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint j hj), intervalIntegral.integral_const]
      dsimp only [a,b]
      simp only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
      ring
    rw [←hc]
    have hwidth : b-a=δ := by dsimp only [a,b]; push_cast; ring
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := γ T*ε+K*(γ b-γ a))
      (f := fun t ↦ γ a*f a-γ t*f t) (fun t ht ↦ by
        rw [uIoc_of_le (hjle j)] at ht
        have htstrip := hs j hj ⟨ht.1.le,ht.2⟩
        have hag : γ a≤γ t := hγ (hm j hj.le) htstrip ht.1.le
        have hgb : γ t≤γ b := hγ htstrip (hm (j+1) (by omega)) ht.2
        have hmod' : |f a-f t|≤ε := hmod a (hm j hj.le) t htstrip (by
          rw [abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
          have htb : t≤b := ht.2
          linarith)
        rw [Real.norm_eq_abs]
        calc
          _ = |γ a*(f a-f t)-(γ t-γ a)*f t| := by congr 1; ring
          _ ≤ |γ a*(f a-f t)|+|(γ t-γ a)*f t| := abs_sub _ _
          _ = γ a*|f a-f t|+(γ t-γ a)*|f t| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hγa, abs_of_nonneg (sub_nonneg.mpr hag)]
          _ ≤ γ T*ε+K*(γ b-γ a) := by
            have hfirst : γ a*|f a-f t|≤γ T*ε :=
              (mul_le_mul_of_nonneg_right hγaT (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_left hmod' (hγa.trans hγaT))
            have hsecond : (γ t-γ a)*|f t|≤K*(γ b-γ a) := by
              calc
                _ ≤ (γ t-γ a)*K := mul_le_mul_of_nonneg_left (hfB t htstrip) (sub_nonneg.mpr hag)
                _ ≤ (γ b-γ a)*K := mul_le_mul_of_nonneg_right (sub_le_sub_right hgb _) hK
                _ = _ := mul_comm _ _
            exact add_le_add hfirst hsecond)
    rw [Real.norm_eq_abs, hwidth, abs_of_nonneg hδ] at hb
    exact hb.trans_eq (mul_comm _ _)
  calc
    _ = |∑ j ∈ Finset.range N, (δ*(γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
      ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t)| := by
      rw [Finset.sum_sub_distrib, ←Finset.mul_sum, heq]
    _ ≤ ∑ j ∈ Finset.range N, |δ*(γ ((j : ℝ)*δ)*f ((j : ℝ)*δ))-
      ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), γ t*f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, δ*(γ T*ε+K*(γ (((j+1 : ℕ) : ℝ)*δ)-γ ((j : ℝ)*δ))) :=
      Finset.sum_le_sum (fun j hj ↦ hloc j (Finset.mem_range.mp hj))
    _ = T*γ T*ε+δ*K*(γ T-γ 0) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum, mul_assoc]
      rw [Finset.sum_range_sub (fun j ↦ γ ((j : ℝ)*δ))]
      simp only [Nat.cast_zero,zero_mul,horizon]
      rw [← mul_assoc (N : ℝ) δ, horizon]

lemma monotone_weighted_grid_tendsto {γ f : ℝ → ℝ} {T K : ℝ}
    (hT : 0<T) (hK : 0≤K) (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hfB : ∀ s∈Icc (0 : ℝ) T, |f s|≤K) :
    Tendsto (fun N : ℕ ↦ (T/N)*(∑ j ∈ Finset.range N, γ ((j : ℝ)*(T/N))*f ((j : ℝ)*(T/N))))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
  have hG : 0≤γ T := hγ0.trans (hγ ⟨le_rfl,hT.le⟩ ⟨hT.le,le_rfl⟩ hT.le)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(2*(T*γ T+1))
  have hη : 0<η := div_pos hε (by positivity)
  have hηeq : η*(2*(T*γ T+1))=ε := div_mul_cancel₀ _ (by positivity)
  have hηb : T*γ T*η<ε/2 := by nlinarith
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  have hδ : Tendsto (fun N : ℕ ↦ T/N) atTop (𝓝 (0 : ℝ)) := tendsto_const_div_atTop_nhds_zero_nat T
  have htail : Tendsto (fun N : ℕ ↦ (T/N)*K*(γ T-γ 0)) atTop (𝓝 0) := by
    simpa only [zero_mul] using (hδ.mul_const K).mul_const (γ T-γ 0)
  filter_upwards [hδ.eventually_le_const hθ, htail.eventually_lt_const (half_pos hε),
    eventually_gt_atTop 0] with N hNθ hNe hN
  rw [Real.dist_eq]
  have hb := monotone_weighted_grid_bound (N := N) (div_nonneg hT.le (Nat.cast_nonneg N)) hK
    (by
      have hn : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp)
    hγ hγ0 hf hfB (fun s hs t ht hst ↦ by
      have hh := hmod s hs t ht (by simpa only [Real.dist_eq] using hst.trans hNθ)
      simpa only [Real.dist_eq] using hh)
  exact hb.trans_lt (by nlinarith)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_RawIncrement
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
open scoped Topology BigOperators

lemma rawIncrement_memLp {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H)
    (hH : MemLp H 2 (gaussianProduct (Fin (N+1)))) :
    MemLp (rawIncrement H j) 2 (gaussianProduct (Fin (N+1))) := by
  apply (memLp_two_iff_integrable_sq
    (hm.aestronglyMeasurable.mul (measurable_coordinate N j).aestronglyMeasurable)).2
  have hind := (hp.independent hj hm).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hi := hind.integrable_mul hH.integrable_sq
      (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).integrable_sq
  change Integrable (fun z ↦ (H z)^2 * (coordinate N j z)^2) _ at hi
  simpa only [rawIncrement, Pi.mul_apply, mul_pow] using hi

lemma rawIncrement_mean {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H) :
    (∫ z, rawIncrement H j z ∂gaussianProduct (Fin (N+1))) = 0 := by
  have hi := (hp.independent hj hm).integral_mul_eq_mul_integral
    hm.aestronglyMeasurable (measurable_coordinate N j).aestronglyMeasurable
  change (∫ z, H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) = _ at hi
  change (∫ z, H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) = 0
  rw [hi, gaussian_mean (coordinate_hasLaw N j), mul_zero]

lemma finiteRaw_memLp {N : ℕ} {δ : ℝ} {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) :
    MemLp (finiteRawMartingale δ H) 2 (gaussianProduct (Fin (N+1))) := by
  have hc := memLp_linearCombination
    (fun i : Fin N ↦ rawIncrement_memLp (by omega) (hm i) (hp i) (hH i)) (fun _ ↦ Real.sqrt δ)
  change MemLp (fun z ↦ ∑ i : Fin N, Real.sqrt δ * H i z * coordinate N i z) 2 _
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rawIncrement]
  ring

lemma derivative_joint_continuous {u : ℝ → ℝ → ℝ} {T La : ℝ} (hLa : 0≤La)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|)) :
    ContinuousOn (fun p : ℝ×ℝ ↦ deriv (u p.1) p.2) {p | p.1∈Icc (0 : ℝ) T} := by
  apply (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (2*La)) ?_).continuousOn
  intro p hp q hq
  rw [Real.coe_toNNReal _ (by positivity), Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  calc
    _ ≤ La*(|p.1-q.1|+|p.2-q.2|) := hLip p.1 hp q.1 hq p.2 q.2
    _ ≤ _ := by
      have h₁ := le_max_left |p.1-q.1| |p.2-q.2|
      have h₂ := le_max_right |p.1-q.1| |p.2-q.2|
      nlinarith

lemma mean_derivative_square_continuous {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℝ → Ω → ℝ} {T D La : ℝ} {u : ℝ → ℝ → ℝ}
    (hD0 : 0≤D) (hLa : 0≤La)
    (hd : ∀ t∈Icc (0 : ℝ) T, Continuous (deriv (u t)))
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hXC : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T)) :
    ContinuousOn (fun t ↦ ∫ ω, (deriv (u t) (X t ω))^2 ∂μ) (Icc (0 : ℝ) T) := by
  apply continuousOn_of_dominated (bound := fun _ ↦ D^2)
  · intro t ht
    exact (((hd t ht).measurable.comp_aemeasurable (hXM t ht).aemeasurable).pow_const 2).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hh := hD t ht (X t ω)
      nlinarith [sq_abs (deriv (u t) (X t ω)), abs_nonneg (deriv (u t) (X t ω))])
  · exact integrable_const _
  · filter_upwards [hXC] with ω hω
    exact ((derivative_joint_continuous hLa hLip).comp
      (continuousOn_id.prodMk hω) (fun t ht ↦ ht)).pow 2

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_ValueEulerOneStep
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma value_euler_one_step {V : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {t δ x z G K L : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hG : 0≤G) (hK : 0≤K) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0≤γ t) (hγG : γ t≤G)
    (hu : |deriv (V t) x|≤1) (hsmooth : ContDiff ℝ 3 (V t))
    (ha : |deriv (deriv (V t)) x|≤K)
    (hthird : ∀ y, |iteratedDeriv 3 (V t) y|≤K)
    (hp : ∀ s ∈ Icc t (t+δ), ∀ y, |(1/2 : ℝ)*(deriv (V s) y)^2|≤K)
    (haLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |deriv (deriv (V s)) y-deriv (deriv (V t)) x|≤L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |(1/2 : ℝ)*(deriv (V s) y)^2-(1/2 : ℝ)*(deriv (V t) x)^2|≤L*(|s-t|+|y-x|))
    (haint : ∀ y, IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ))
    (hpint : ∀ y, IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) y)^2)) volume t (t+δ))
    (hPDE : ∀ y, V (t+δ) y-V t y =
      -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) y+γ s*((1/2 : ℝ)*(deriv (V s) y)^2))) :
    let d := Real.sqrt δ*z+δ*γ t*deriv (V t) x
    |V (t+δ) (x+d)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)-
      (1/2 : ℝ)*δ*γ t*(deriv (V t) x)^2| ≤
    δ*Real.sqrt δ*(K*(|z|+G)^3+(1/2+G)*L*(1+|z|+G)+K*G*(|z|+G/2))+
      δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*γ t*deriv (V t) x
  have htm := gradient_generator_quadrature
    (b := fun s y ↦ deriv (deriv (V s)) y)
    (p := fun s y ↦ (1/2 : ℝ)*(deriv (V s) y)^2) (y := x+d)
    hδ hG hK hL hγ hγ0 hγG
    (fun s hs ↦ hp s hs _) (fun s hs ↦ haLip s hs _) (fun s hs ↦ hpLip s hs _)
    (haint _) (hpint _)
  have ht : |(V (t+δ) (x+d)-V t x+deriv (V t) x-
        (1/2 : ℝ)*δ*γ t*(deriv (V t) x)^2)-
      (V t (x+d)-V t x+deriv (V t) x)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*deriv (V t) x*deriv (V t) x)| ≤
      δ*(((1/2 : ℝ)+G)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq : (V (t+δ) (x+d)-V t x+deriv (V t) x-
        (1/2 : ℝ)*δ*γ t*(deriv (V t) x)^2)-
      (V t (x+d)-V t x+deriv (V t) x)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*deriv (V t) x*deriv (V t) x) =
      (V (t+δ) (x+d)-V t (x+d))+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) := by ring
    rw [heq,hPDE]
    rw [show -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
        γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))+
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) =
        -((∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
        γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))-
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2))) by ring,
      abs_neg]
    simpa only [add_sub_cancel_left] using htm
  have hs : |(V t (x+d)-V t x+deriv (V t) x)-deriv (V t) x-
      deriv (V t) x*d-(1/2 : ℝ)*deriv (deriv (V t)) x*d^2| ≤ K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound hsmooth hK hthird x d
  have hh := euler_cubic_remainder hδ hδ1 hG hK (by positivity : 0≤(1/2+G)*L)
    (by rwa [abs_of_nonneg hγ0]) hu ha hs ht
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  dsimp only [d]
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ValueStrip
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma valueMeshCompensated_step (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (j : ℕ) (z : Fin (N+1) → ℝ) :
    valueMeshCompensated T N γ V (j+1) z-valueMeshCompensated T N γ V j z =
    V (meshTime T N (j+1)) (euler T N γ (fun t ↦ deriv (V t)) z (j+1))-
    V (meshTime T N j) (euler T N γ (fun t ↦ deriv (V t)) z j)-
    (stepSize T N/2)*γ (meshTime T N j)*
      (deriv (V (meshTime T N j)) (euler T N γ (fun t ↦ deriv (V t)) z j))^2 := by
  simp only [valueMeshCompensated, valueMeshEnergy, Finset.sum_range_succ]
  ring

lemma valueMeshCompensated_zero (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (z : Fin (N+1) → ℝ) : valueMeshCompensated T N γ V 0 z=V 0 0 := by
  simp [valueMeshCompensated, valueMeshEnergy, meshTime, euler]

lemma valueMeshError_bound {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    valueMeshError T N γ V ≤
      2*((stepSize T N/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(stepSize T N*Real.sqrt (stepSize T N))^2*(N : ℝ)^2*
        cubicEnvelopeMoment (γ T) K ((1/2+γ T)*L)+
      4*(stepSize T N*K*(γ T-γ 0))^2 := by
  let u := fun t ↦ deriv (V t)
  let δ := stepSize T N
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0≤δ := by dsimp [δ, stepSize]; positivity
  have hδ1 : δ≤1 := by
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    dsimp [δ, stepSize]
    exact (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hmesh : (N : ℝ)*δ=T := by dsimp [δ, stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT.le⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hG : 0≤γ T := h.gamma_nonneg T htT
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+δ := by
    dsimp [meshTime, δ]; push_cast; ring
  have hlast : meshTime T N N=T := hmesh
  have hzero : meshTime T N 0=0 := by simp only [meshTime, Nat.cast_zero, zero_mul]
  have huc (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : Continuous (u t) :=
    (h.smooth t ht).continuous_deriv (by norm_num)
  have hY (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ euler T N γ u z j) :=
    measurable_euler T N γ u (fun k hk ↦ (huc _ (htime k hk.le)).measurable) j hj
  have hAm (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) :=
    (huc _ (htime j hj)).measurable.comp (hY j hj)
  have hUm (j : ℕ) (hj : j≤N) : Measurable (valueMeshCompensated T N γ V j) := by
    apply Measurable.sub ((h.smooth _ (htime j hj)).continuous.measurable.comp (hY j hj))
    apply Finset.measurable_fun_sum
    intro i hi
    exact ((hAm i (le_trans (Finset.mem_range.mp hi).le hj)).pow_const 2).const_mul _
  have hHm (i : Fin N) : Measurable (fun z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i)) := by
    have hc := (h.smooth _ (htime i i.isLt.le)).continuous_iteratedDeriv 2 (by norm_num)
    have hc' : Continuous (deriv (u (meshTime T N i))) := by
      simpa only [u, show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hc
    exact hc'.measurable.comp (hY i i.isLt.le)
  have hloc (i : Fin N) (z : Fin (N+1) → ℝ) :
      |valueMeshCompensated T N γ V (i+1) z-valueMeshCompensated T N γ V i z-
        Real.sqrt δ*u (meshTime T N i) (euler T N γ u z i)*coordinate N i z-
        (δ/2)*deriv (u (meshTime T N i)) (euler T N γ u z i)*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N i z)+
        δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [← hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hbint (x : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (V s)) x) volume t (t+δ) := by
      apply (h.second_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hpint (x : ℝ) : IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) x)^2)) volume t (t+δ) := by
      apply (h.product_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hh := value_euler_one_step (x := euler T N γ u z i) (z := coordinate N i z)
      hδ hδ1 hG h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub) (h.gamma_nonneg t ht)
      (h.gamma_mono ht htT ht.2) (h.bounded t ht _) (h.smooth t ht)
      (h.second_bound t ht _) (h.third_bound t ht)
      (fun s hs ↦ h.product_bound s (hsub hs))
      (fun s hs y ↦ h.second_lipschitz t ht s (hsub hs) _ y)
      (fun s hs y ↦ h.product_lipschitz t ht s (hsub hs) _ y)
      hbint hpint (h.pde t ht (t+δ) ht')
    dsimp only at hh
    rw [valueMeshCompensated_step]
    convert hh using 1 <;> simp only [hsucc, euler, cubicEnvelope, t, δ, u]
    all_goals congr 1
    all_goals ring_nf
  have hb := discrete_gradient_residual_L2 (δ := δ) hδ hG h.K_nonneg
    (mul_nonneg (by positivity) h.L_nonneg : 0≤(1/2+γ T)*L)
    (Γ := fun j ↦ γ (meshTime T N j))
    (U := valueMeshCompensated T N γ V)
    (A := fun i z ↦ u (meshTime T N i) (euler T N γ u z i))
    (H := fun i z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i))
    (by simpa only [hlast, hzero] using h.gamma_mono ht0 htT hT.le)
    hUm (fun i ↦ hAm i i.isLt.le) hHm
    (fun i ↦ eulerCoefficient_dependsBefore T i.isLt.le γ u (fun t ↦ deriv (u t)))
    (fun i z ↦ h.second_bound _ (htime i i.isLt.le) _) hloc
  simpa only [valueMeshError, valueMeshCompensated_zero, hlast, hzero, u, δ] using hb

lemma valueMeshError_bound_linear {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    valueMeshError T N γ V ≤ stepSize T N*gradientErrorConstant T K L γ := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hδ : 0≤ stepSize T N := div_nonneg hT.le hNr.le
  have hδ1 : stepSize T N≤1 := (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hm : (N:ℝ)*stepSize T N=T := by unfold stepSize; field_simp
  exact (valueMeshError_bound hT hT1 h hN).trans (gaussian_mesh_bound_linear hδ hδ1 hm)

lemma valueMeshError_tendsto_zero {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) :
    Tendsto (fun N ↦ valueMeshError T N γ V) atTop (𝓝 0) := by
  have hbound : ∀ᶠ N in atTop,
      valueMeshError T N γ V ≤ stepSize T N*gradientErrorConstant T K L γ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact valueMeshError_bound_linear hT hT1 h hN
  have hlim : Tendsto (fun N ↦ stepSize T N*gradientErrorConstant T K L γ) atTop (𝓝 0) := by
    simpa only [stepSize, zero_mul] using
      (tendsto_const_div_atTop_nhds_zero_nat T).mul_const (gradientErrorConstant T K L γ)
  exact squeeze_zero' (Eventually.of_forall (fun N ↦ integral_nonneg (fun _ ↦ sq_nonneg _))) hbound hlim

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_EulerMemLp
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma euler_memLp (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (huM : ∀ j<N, Measurable (u (meshTime T N j)))
    (huB : ∀ j<N, ∀ x, |u (meshTime T N j) x|≤1) :
    ∀ j≤N, MemLp (fun z ↦ euler T N γ u z j) 2 (gaussianProduct (Fin (N+1))) := by
  intro j
  induction j with
  | zero => intro _; exact memLp_const (0 : ℝ)
  | succ j ih =>
    intro hj
    have hlt : j<N := by omega
    have hU : MemLp (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) 2
        (gaussianProduct (Fin (N+1))) :=
      MemLp.of_bound ((huM j hlt).comp (measurable_euler T N γ u huM j hlt.le)).aestronglyMeasurable 1
        (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using huB j hlt _))
    exact ((ih hlt.le).add ((gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).const_mul _)).add
      (hU.const_mul (stepSize T N*γ (meshTime T N j)))

lemma ValueStrip.value_lipschitz {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : ValueStrip T γ V K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    LipschitzWith 1 (V t) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((h.smooth t ht).differentiable (by norm_num))
  intro x
  exact_mod_cast (show ‖deriv (V t) x‖≤(1 : ℝ) by simpa only [Real.norm_eq_abs] using h.bounded t ht x)

lemma ValueStrip.value_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : ValueStrip T γ V K L)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) T) {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    MemLp (fun ω ↦ V t (Y ω)) 2 μ := by
  have hl : LipschitzWith 1 (fun x ↦ V t x - V t 0) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_sub_right] using (h.value_lipschitz ht).dist_le_mul x y
  have hh := hl.comp_memLp (by simp) hY
  convert hh.add (memLp_const (V t 0)) using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  simp

lemma value_mesh_expectation_error {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    |(∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N) ∂gaussianProduct (Fin (N+1)))-V 0 0-
      (∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))| ≤
      Real.sqrt (valueMeshError T N γ V) := by
  let u := fun t ↦ deriv (V t)
  let Y := euler T N γ u
  let μ := gaussianProduct (Fin (N+1))
  let A (i : Fin N) (z : Fin (N+1) → ℝ) := u (meshTime T N i) (Y z i)
  let M (z : Fin (N+1) → ℝ) := ∑ i : Fin N, Real.sqrt (stepSize T N)*A i z*coordinate N i z
  let R (z : Fin (N+1) → ℝ) := valueMeshCompensated T N γ V N z-V 0 0-M z
  have htime (j : ℕ) (hj : j≤N) := mesh_time_mem hT.le hN hj
  have huc (j : ℕ) (hj : j≤N) : Continuous (u (meshTime T N j)) :=
    (h.smooth _ (htime j hj)).continuous_deriv (by norm_num)
  have hY (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ Y z j) :=
    measurable_euler T N γ u (fun i hi ↦ (huc i hi.le).measurable) j hj
  have hAm (i : Fin N) : Measurable (A i) := (huc i i.isLt.le).measurable.comp (hY i i.isLt.le)
  have hAb (i : Fin N) z : |A i z|≤1 := h.bounded _ (htime i i.isLt.le) _
  have hAp (i : Fin N) : DependsBefore i (A i) := eulerCoefficient_dependsBefore T i.isLt.le γ u u
  have hAM (i : Fin N) : MemLp (A i) 2 μ :=
    MemLp.of_bound (hAm i).aestronglyMeasurable 1
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hAb i z))
  have hMm : MemLp M 2 μ := finiteRaw_memLp hAm hAp hAM
  have hMv : (∫ z, M z ∂μ)=0 := by
    have hMi (i : Fin N) : Integrable (fun z ↦ Real.sqrt (stepSize T N)*A i z*coordinate N i z) μ :=
      ((rawIncrement_memLp (by omega : (i : ℕ)<N+1) (hAm i) (hAp i) (hAM i)).const_mul
        (Real.sqrt (stepSize T N))).integrable (by norm_num) |>.congr (by
          filter_upwards [] with z; simp only [rawIncrement]; ring)
    rw [show (∫ z, M z ∂μ)=∑ i : Fin N, ∫ z, Real.sqrt (stepSize T N)*A i z*coordinate N i z ∂μ from
      integral_finsetSum _ (fun i _ ↦ hMi i)]
    have he (i : Fin N) : (∫ z, Real.sqrt (stepSize T N)*A i z*coordinate N i z ∂μ)=0 := by
      simp only [mul_assoc]
      rw [integral_const_mul]
      change Real.sqrt (stepSize T N)*(∫ z, rawIncrement (A i) i z ∂μ)=0
      rw [rawIncrement_mean (by omega) (hAm i) (hAp i),mul_zero]
    simp only [he, Finset.sum_const_zero]
  have hEm : MemLp (valueMeshEnergy T N γ V N) 2 μ := by
    apply memLp_finsetSum
    intro j hj
    have hjN : j<N := Finset.mem_range.mp hj
    apply MemLp.const_mul
    apply MemLp.of_bound (((huc j hjN.le).measurable.comp (hY j hjN.le)).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_pow, sq_le_one_iff_abs_le_one]
    simpa only [abs_abs, u, Function.comp_apply] using h.bounded _ (htime j hjN.le) (Y z j)
  have hYM : MemLp (fun z ↦ Y z N) 2 μ :=
    euler_memLp T N γ u (fun i hi ↦ (huc i hi.le).measurable)
      (fun i hi x ↦ h.bounded _ (htime i hi.le) x) N le_rfl
  have hVM := h.value_memLp (t := T) ⟨hT.le,le_rfl⟩ hYM
  have hlast : meshTime T N N=T := by
    dsimp only [meshTime, stepSize]
    have hn : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
    field_simp
  have hRM : MemLp R 2 μ := by
    dsimp only [R,valueMeshCompensated]
    rw [hlast]
    exact ((hVM.sub hEm).sub (memLp_const (V 0 0))).sub hMm
  have hRint : (∫ z, R z ∂μ)=
      (∫ z, V T (Y z N) ∂μ)-V 0 0-(∫ z, valueMeshEnergy T N γ V N z ∂μ) := by
    dsimp only [R,valueMeshCompensated]
    rw [hlast]
    have hi₁ := integral_sub (((hVM.sub hEm).sub (memLp_const (V 0 0))).integrable (by norm_num)) (hMm.integrable (by norm_num))
    have hi₂ := integral_sub ((hVM.sub hEm).integrable (by norm_num)) (integrable_const (V 0 0))
    simp only [Pi.sub_apply] at hi₁ hi₂
    change (∫ z, V T (Y z N)-valueMeshEnergy T N γ V N z-V 0 0-M z ∂μ)=_
    rw [hi₁, hi₂]
    rw [integral_sub (hVM.integrable (by norm_num)) (hEm.integrable (by norm_num)),hMv,integral_const]
    simp only [probReal_univ, smul_eq_mul, sub_zero]
    ring
  rw [←hRint]
  exact abs_integral_le_integral_abs.trans (integral_abs_le_sqrt_integral_sq hRM)

lemma value_mesh_expectation_error_tendsto {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) :
    Tendsto (fun N ↦ (∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N)
      ∂gaussianProduct (Fin (N+1)))-V 0 0-
      (∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N ↦ Real.sqrt (valueMeshError T N γ V))
  · filter_upwards [eventually_gt_atTop 0] with N hN
    simpa only [Real.norm_eq_abs] using value_mesh_expectation_error hT h hN
  · simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp (valueMeshError_tendsto_zero hT hT1 h)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_LipschitzCompMemLpFinite
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
open scoped Topology BigOperators

lemma lipschitz_comp_memLp_finite {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {q : ℝ → ℝ} {C : ℝ≥0} (hq : LipschitzWith C q)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) : MemLp (fun ω ↦ q (Y ω)) 2 μ := by
  have hl : LipschitzWith C (fun x ↦ q x-q 0) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_sub_right] using hq.dist_le_mul x y
  have hh := hl.comp_memLp (by simp) hY
  convert hh.add (memLp_const (q 0)) using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  simp

lemma coupled_euler_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} (hT : 0<T)
    (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    MemLp (coupledEuler T γ u B N j) 2 μ := by
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hm := euler_memLp T N γ u
    (fun k hk ↦ (h.smooth _ (mesh_time_mem hT.le hN hk.le)).continuous.measurable)
    (fun k hk x ↦ h.bounded _ (mesh_time_mem hT.le hN hk.le) x) j hj
  have hh := (hlaw.map_eq.symm ▸ hm).comp_of_map hlaw.aemeasurable
  change MemLp (fun ω ↦ if N=0 then 0 else euler T N γ u (coupledCoordinates T N B ω) j) 2 μ
  simpa only [Function.comp_def, ite_eq_right (Nat.ne_of_gt hN)] using hh

lemma coupled_lipschitz_expectation_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L)
    (hXM : ∀ t∈Icc (0 : ℝ) T, MemLp (X t) 2 μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) {q : ℝ → ℝ} {C : ℝ≥0}
    (hq : LipschitzWith C q) :
    |(∫ z, q (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))-
      ∫ ω, q (X (meshTime T N j) ω) ∂μ| ≤
      (C : ℝ)*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht := mesh_time_mem hT.le hN hj
  have hFM := lipschitz_comp_memLp_finite hq (coupled_euler_memLp hB hT h hN hj)
  have hGM := lipschitz_comp_memLp_finite hq (hXM _ ht)
  have hEM := coupled_mesh_error_memLp hB hT h (fun t ht ↦ (hXM t ht).aestronglyMeasurable) hpaths hN
  have hFG (ω : Ω) : |q (coupledEuler T γ u B N j ω)-q (X (meshTime T N j) ω)|≤(C : ℝ)*|E ω| := by
    have he : |coupledEuler T γ u B N j ω-X (meshTime T N j) ω|≤E ω :=
      le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) hj
    have hl : |q (coupledEuler T γ u B N j ω)-q (X (meshTime T N j) ω)|≤
        (C : ℝ)*|coupledEuler T γ u B N j ω-X (meshTime T N j) ω| := by
      simpa only [Real.dist_eq] using
        hq.dist_le_mul (coupledEuler T γ u B N j ω) (X (meshTime T N j) ω)
    exact hl.trans (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) C.coe_nonneg)
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hm := measurable_euler T N γ u (fun k hk ↦
    (h.smooth _ (mesh_time_mem hT.le hN hk.le)).continuous.measurable) j hj
  have heq : (∫ z, q (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))=
      ∫ ω, q (coupledEuler T γ u B N j ω) ∂μ := by
    have he := hlaw.integral_comp (hq.continuous.measurable.comp hm).aestronglyMeasurable
    simpa only [Function.comp_apply, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)] using he.symm
  rw [heq]
  exact first_moment_perturbation hFM hGM hEM C.coe_nonneg (Eventually.of_forall hFG)

lemma perturbed_monotone_weighted_grid_tendsto {γ f : ℝ → ℝ} {T K : ℝ}
    {a : (N : ℕ) → Fin N → ℝ} {r : ℕ → ℝ}
    (hT : 0<T) (hK : 0≤K) (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hfB : ∀ s∈Icc (0 : ℝ) T, |f s|≤K)
    (hr : Tendsto r atTop (𝓝 0))
    (ha : ∀ᶠ N in atTop, ∀ j : Fin N, |a N j-f (meshTime T N j)| ≤ r N) :
    Tendsto (fun N ↦ stepSize T N * ∑ j : Fin N, γ (meshTime T N j)*a N j) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
  have hG : 0≤γ T := hγ0.trans (hγ ⟨le_rfl,hT.le⟩ ⟨hT.le,le_rfl⟩ hT.le)
  have hR := monotone_weighted_grid_tendsto hT hK hγ hγ0 hf hfB
  have herr : Tendsto (fun N ↦ stepSize T N * (∑ j : Fin N, γ (meshTime T N j)*a N j)-
      stepSize T N * (∑ j : Fin N, γ (meshTime T N j)*f (meshTime T N j))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦ T*γ T*r N)
    · filter_upwards [ha, eventually_gt_atTop 0] with N hNa hN
      have hδ : 0 ≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
      have hconstant : stepSize T N * ∑ _ : Fin N, γ T*r N=T*γ T*r N := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, stepSize]
        field_simp
      rw [Real.norm_eq_abs, ←mul_sub, abs_mul, abs_of_nonneg hδ, ←Finset.sum_sub_distrib]
      calc
        _ ≤ stepSize T N * ∑ j : Fin N, |γ (meshTime T N j)*a N j-γ (meshTime T N j)*f (meshTime T N j)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hδ
        _ ≤ stepSize T N * ∑ _ : Fin N, γ T*r N := by
          apply mul_le_mul_of_nonneg_left _ hδ
          apply Finset.sum_le_sum
          intro j _
          have ht := mesh_time_mem hT.le hN j.isLt.le
          have hg0 : 0≤γ (meshTime T N j) := hγ0.trans (hγ ⟨le_rfl,hT.le⟩ ht ht.1)
          have hgT := hγ ht ⟨hT.le,le_rfl⟩ ht.2
          rw [←mul_sub, abs_mul, abs_of_nonneg hg0]
          exact (mul_le_mul_of_nonneg_right hgT (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (hNa j) hG)
        _ = _ := hconstant
    · simpa only [mul_zero] using hr.const_mul (T*γ T)
  have hR' : Tendsto (fun N ↦ stepSize T N * ∑ j : Fin N, γ (meshTime T N j)*f (meshTime T N j))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
    convert hR using 1
    all_goals try with_reducible_and_instances rfl
    funext N
    dsimp only [stepSize, meshTime]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ γ ((j : ℝ)*(T/N))*f ((j : ℝ)*(T/N))) ]
  simpa only [sub_add_cancel, zero_add] using herr.add hR'

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma ValueStrip.product_lipschitzWith {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : ValueStrip T γ V K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    LipschitzWith (Real.toNNReal L) (fun x ↦ (1/2 : ℝ)*(deriv (V t) x)^2) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.coe_toNNReal _ h.L_nonneg, Real.dist_eq, Real.dist_eq]
  simpa only [sub_self, abs_zero, zero_add] using h.product_lipschitz t ht t ht y x

lemma valueMeshEnergy_expectation {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    (∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))=
      stepSize T N * ∑ j : Fin N, γ (meshTime T N j)*
        (∫ z, (1/2 : ℝ)*(deriv (V (meshTime T N j))
          (euler T N γ (fun t ↦ deriv (V t)) z j))^2 ∂gaussianProduct (Fin (N+1))) := by
  have hm (j : ℕ) (hj : j<N) : MemLp
      (fun z ↦ (1/2 : ℝ)*(deriv (V (meshTime T N j))
        (euler T N γ (fun t ↦ deriv (V t)) z j))^2) 2 (gaussianProduct (Fin (N+1))) := by
    apply MemLp.of_bound
      ((h.product_lipschitzWith (mesh_time_mem hT.le hN hj.le)).continuous.measurable.comp
        (measurable_euler T N γ (fun t ↦ deriv (V t)) (fun i hi ↦
          ((h.smooth _ (mesh_time_mem hT.le hN hi.le)).continuous_deriv (by norm_num)).measurable)
            j hj.le)).aestronglyMeasurable K
    exact Eventually.of_forall (fun z ↦ by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using h.product_bound _ (mesh_time_mem hT.le hN hj.le) _)
  have heq (z : Fin (N+1) → ℝ) : valueMeshEnergy T N γ V N z =
      ∑ j ∈ Finset.range N, stepSize T N*γ (meshTime T N j)*
        ((1/2 : ℝ)*(deriv (V (meshTime T N j))
          (euler T N γ (fun t ↦ deriv (V t)) z j))^2) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [heq]
  rw [integral_finsetSum _ (fun j hj ↦ ((hm j (Finset.mem_range.mp hj)).integrable (by norm_num)).const_mul _)]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ γ (meshTime T N j)*
    ∫ z, (1/2 : ℝ)*(deriv (V (meshTime T N j))
      (euler T N γ (fun t ↦ deriv (V t)) z j))^2 ∂gaussianProduct (Fin (N+1)))]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem diffusion_value_expectation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L Kg Lg Lu : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L)
    (hg : GradientStrip T γ (fun t ↦ deriv (V t)) Kg Lg) (hLu : 0≤Lu)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (V s) x-deriv (V t) y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, MemLp (X t) 2 μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*deriv (V s) (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*deriv (V s) (X s ω)) ∧ X 0 ω=0) :
    (∫ ω, V T (X T ω) ∂μ) = V 0 0+
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..T, γ t*(∫ ω, (deriv (V t) (X t ω))^2 ∂μ)) := by
  let u := fun t ↦ deriv (V t)
  let E (N : ℕ) := ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ
  let f (t : ℝ) := ∫ ω, (1/2 : ℝ)*(deriv (V t) (X t ω))^2 ∂μ
  have hXa (t : ℝ) (ht : t∈Icc (0 : ℝ) T) := (hXM t ht).aestronglyMeasurable
  have hE : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence hB hT hg hLu huLip hXa hpaths
  have hEs : Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hE
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hvalue : Tendsto (fun N ↦ ∫ z, V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 (∫ ω, V T (X T ω) ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_ hEs
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hh := coupled_lipschitz_expectation_bound hB hT hg hXM
      (hpaths.mono (fun _ hω ↦ hω.2.2)) hN (le_refl N) (h.value_lipschitz ht)
    have hn : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
    have hlast : meshTime T N N=T := by dsimp only [meshTime, stepSize]; field_simp
    simpa only [Real.norm_eq_abs, hlast, NNReal.coe_one, one_mul] using hh
  have hf : ContinuousOn f (Icc (0 : ℝ) T) := by
    have hc := (mean_derivative_square_continuous (by norm_num : (0 : ℝ)≤1) hLu
      (fun t ht ↦ (h.smooth t ht).continuous_deriv (by norm_num)) h.bounded huLip hXa
      (hpaths.mono (fun _ hω ↦ hω.1))).const_mul (1/2 : ℝ)
    simpa only [f, integral_const_mul] using hc
  have hfB (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |f t|≤K := by
    simpa only [f, Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := μ) (C := K)
        (f := fun ω ↦ (1/2 : ℝ)*(deriv (V t) (X t ω))^2)
        (Eventually.of_forall (fun ω ↦ by
          simpa only [Real.norm_eq_abs] using h.product_bound t ht (X t ω))))
  have henergy : Tendsto (fun N ↦ ∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
    have hq : Tendsto (fun N ↦ stepSize T N * ∑ j : Fin N, γ (meshTime T N j)*
        (∫ z, (1/2 : ℝ)*(deriv (V (meshTime T N j))) (euler T N γ u z j)^2
          ∂gaussianProduct (Fin (N+1)))) atTop (𝓝 (∫ t in (0 : ℝ)..T, γ t*f t)) := by
      apply perturbed_monotone_weighted_grid_tendsto (r := fun N ↦ L*Real.sqrt (E N)) hT h.K_nonneg
        h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩) hf hfB
        (by simpa only [mul_zero] using hEs.const_mul L)
      filter_upwards [eventually_gt_atTop 0] with N hN j
      have hh := coupled_lipschitz_expectation_bound hB hT hg hXM
        (hpaths.mono (fun _ hω ↦ hω.2.2)) hN j.isLt.le
          (h.product_lipschitzWith (mesh_time_mem hT.le hN j.isLt.le))
      simpa only [Real.coe_toNNReal _ h.L_nonneg] using hh
    apply hq.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (valueMeshEnergy_expectation hT h hN).symm
  have hlim := (hvalue.sub_const (V 0 0)).sub henergy
  have hzero := value_mesh_expectation_error_tendsto hT hT1 h
  have he : (∫ ω, V T (X T ω) ∂μ)-V 0 0-(∫ t in (0 : ℝ)..T, γ t*f t)=0 :=
    tendsto_nhds_unique hlim hzero
  have hfeq : (∫ t in (0 : ℝ)..T, γ t*f t)=
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..T, γ t*(∫ ω, (deriv (V t) (X t ω))^2 ∂μ)) := by
    dsimp only [f]
    simp_rw [integral_const_mul]
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hfeq] at he
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_StripPaths
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
open scoped Topology BigOperators

lemma IsDiffusion.strip_paths {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {T Lu : ℝ}
    (hT : 0≤T) (hT1 : T<1) (hLu : 0≤Lu)
    (huLip : ∀ t∈Icc (0 : ℝ) T, ∀ s∈Icc (0 : ℝ) T, ∀ x y,
      |gradient W γ s y-gradient W γ t x|≤Lu*(|s-t|+|y-x|)) :
    ∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = W.B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ.coeff s*gradient W γ s (X s ω)) ∧ X 0 ω=0 := by
  filter_upwards [hX.2, W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω h0
  have hsub : Icc (0 : ℝ) T ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hT1.le
  refine ⟨hω.1.mono hsub, ?_, fun t ht ↦ hω.2 t (hsub ht), ?_⟩
  · have hj : ContinuousOn (fun p : ℝ×ℝ ↦ gradient W γ p.1 p.2)
        {p | p.1∈Icc (0 : ℝ) T} :=
      derivative_joint_continuous hLu (fun s hs t ht x y ↦ huLip t ht s hs y x)
    have hp : ContinuousOn (fun t : ℝ ↦ (t, X t ω)) (Icc (0 : ℝ) T) :=
      continuousOn_id.prodMk (hω.1.mono hsub)
    have hc : ContinuousOn (fun t ↦ gradient W γ t (X t ω)) (Icc (0 : ℝ) T) := by
      exact ContinuousOn.comp (g := fun p : ℝ×ℝ ↦ gradient W γ p.1 p.2)
        (f := fun t : ℝ ↦ (t, X t ω)) hj hp (fun t ht ↦ ht)
    have hgi : IntervalIntegrable γ.coeff volume 0 T :=
      γ.intervalIntegrable.mono_set (by
        simpa only [uIcc_of_le hT, uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using
          (Icc_subset_Icc le_rfl hT1.le))
    exact hgi.mul_continuousOn (by simpa only [uIcc_of_le hT] using hc)
  · simpa only [intervalIntegral.integral_same, add_zero, Real.toNNReal_zero, h0]
      using hω.2 0 (by norm_num)

lemma IsDiffusion.value_expectation {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {T K L Kg Lg Lu : ℝ}
    (hT : 0<T) (hT1 : T<1)
    (h : ValueStrip T γ.coeff (phi W γ) K L)
    (hg : GradientStrip T γ.coeff (gradient W γ) Kg Lg)
    (hLu : 0≤Lu)
    (huLip : ∀ t∈Icc (0 : ℝ) T, ∀ s∈Icc (0 : ℝ) T, ∀ x y,
      |gradient W γ s y-gradient W γ t x|≤Lu*(|s-t|+|y-x|)) :
    (∫ ω, phi W γ T (X T ω) ∂W.μ) = phi W γ 0 0+
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..T, γ.coeff t*(∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)) := by
  apply diffusion_value_expectation (μ := W.μ) (B := W.B) (X := X)
    W.brownian.toIsPreBrownianReal hT hT1.le h hg hLu
    (fun s hs t ht x y ↦ huLip t ht s hs y x)
  · intro t ht
    exact hX.memLp ⟨ht.1,ht.2.trans hT1.le⟩ (by norm_num)
  · exact hX.strip_paths hT.le hT1 hLu huLip

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TimeWeightedIntervalIntegrable
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
open scoped Topology

lemma OrderParameter.time_weighted_intervalIntegrable (γ : OrderParameter) :
    IntervalIntegrable (fun t ↦ t*γ.coeff t) volume 0 1 := by
  simpa only [mul_comm, id_eq] using γ.intervalIntegrable.mul_continuousOn continuous_id.continuousOn

lemma OrderParameter.time_weighted_terminal (γ : OrderParameter) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, t*γ.coeff t) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ t in (0 : ℝ)..1, t*γ.coeff t)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval'
    γ.time_weighted_intervalIntegrable (show (0 : ℝ)∈uIcc (0 : ℝ) 1 from left_mem_uIcc)
  have ht : Tendsto (id : ℝ → ℝ) (𝓝[<] 1) (𝓝[uIcc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, by
      simpa only [id_eq, uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using eventually_time_mem⟩
  exact Filter.Tendsto.comp (hc 1 right_mem_uIcc) ht

theorem IsDiffusion.parisi_first_value_oai {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hstrips : ∀ T : ℝ, 0<T → T<1 → ∃ K L Kg Lg Lu : ℝ,
      ValueStrip T γ.coeff (phi W γ) K L ∧
      GradientStrip T γ.coeff (gradient W γ) Kg Lg ∧ 0≤Lu ∧
      ∀ t∈Icc (0 : ℝ) T, ∀ s∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s y-gradient W γ t x|≤Lu*(|s-t|+|y-x|))
    (hmoment : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    parisi W γ=(∫ ω, |X 1 ω| ∂W.μ)-∫ t in (0 : ℝ)..1, t*γ.coeff t := by
  have hid : ∀ T∈Ioo (0 : ℝ) 1, (∫ ω, phi W γ T (X T ω) ∂W.μ)=
      phi W γ 0 0+(1/2 : ℝ)*(∫ t in (0 : ℝ)..T, t*γ.coeff t) := by
    intro T hT
    obtain ⟨K,L,Kg,Lg,Lu,hV,hG,hLu,hu⟩ := hstrips T hT.1 hT.2
    have hh := hX.value_expectation hT.1 hT.2 hV hG hLu hu
    rw [hh]
    congr 2
    apply intervalIntegral.integral_congr_Ioo_of_le hT.1.le
    intro t ht
    change γ.coeff t*(∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t*γ.coeff t
    rw [hmoment t ⟨ht.1.le,ht.2.trans hT.2⟩, mul_comm]
  have hlim : Tendsto (fun T ↦ ∫ ω, phi W γ T (X T ω) ∂W.μ) (𝓝[<] (1 : ℝ))
      (𝓝 (phi W γ 0 0+(1/2 : ℝ)*(∫ t in (0 : ℝ)..1, t*γ.coeff t))) := by
    apply ((γ.time_weighted_terminal.const_mul (1/2 : ℝ)).const_add (phi W γ 0 0)).congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
    exact (hid T hT).symm
  have he := tendsto_nhds_unique hX.phi_expectation_terminal hlim
  unfold parisi
  linarith

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsDiffusion.parisi_first_value_oai := @OAI.SKValue.IsDiffusion.parisi_first_value_oai
