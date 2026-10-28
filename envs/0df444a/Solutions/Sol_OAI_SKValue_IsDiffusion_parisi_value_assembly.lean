-- Prove2me | solution 1 for OAI.SKValue.IsDiffusion.parisi_value_assembly
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:57:28.028372+00:00
-- url     : https://prove2.me/submissions/bedb514c-1820-44ad-bd03-2a34c72ffd99

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_IsDiffusion_curvature_integral_terminal
import Theorems.Thm_OAI_SKValue_IsDiffusion_parisi_first_value

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

lemma controlPayoff_convex {W : BrownianSpace} (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) {α : ℝ≥0 → W.Ω → ℝ} (hα : Admissible W t α) :
    ConvexOn ℝ univ (fun x ↦ controlPayoff W γ t x α) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rw [controlPayoff_eq W γ ht, controlPayoff_eq W γ ht, controlPayoff_eq W γ ht]
  have hxI := controlPayoff_integrable γ ht x hα
  have hyI := controlPayoff_integrable γ ht y hα
  rw [← integral_const_mul a, ← integral_const_mul b, ← integral_add (hxI.const_mul _) (hyI.const_mul _)]
  apply integral_mono (controlPayoff_integrable γ ht (a*x+b*y) hα)
    ((hxI.const_mul _).add (hyI.const_mul _))
  intro ω
  dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  let q := W.B 1 ω-W.B t.toNNReal ω+controlIntegral γ t α 1 ω
  have he : a*x+b*y+q = a*(x+q)+b*(y+q) := by
    calc
      _ = a*x+b*y+(a+b)*q := by rw [hab,one_mul]
      _ = _ := by ring
  have hh : |a*x+b*y+q|≤a*|x+q|+b*|y+q| := by
    rw [he]
    calc
      _ ≤ |a*(x+q)|+|b*(y+q)| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
  dsimp [q] at hh
  have hc : a*((1/2 : ℝ)*controlIntegral γ t α 2 ω)+
      b*((1/2 : ℝ)*controlIntegral γ t α 2 ω) = (1/2 : ℝ)*controlIntegral γ t α 2 ω := by
    rw [← add_mul,hab,one_mul]
  simp only [add_assoc] at hh ⊢
  nlinarith

lemma phi_convex (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) : ConvexOn ℝ univ (phi W γ t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  apply csSup_le (control_values_nonempty W γ t (a*x+b*y))
  rintro r ⟨α,hα,rfl⟩
  have hh := (controlPayoff_convex γ ht hα).2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hh
  apply hh.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (le_csSup (control_values_bddAbove W γ ht x) ⟨α,hα,rfl⟩) ha
  · exact mul_le_mul_of_nonneg_left (le_csSup (control_values_bddAbove W γ ht y) ⟨α,hα,rfl⟩) hb

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

lemma gradient_lower_of_pos (W : BrownianSpace) (γ : OrderParameter) {t x h : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (hh : 0<h) (hx : h≤x)
    (hd : DifferentiableAt ℝ (phi W γ t) x) :
    1-terminalError γ t/h ≤ gradient W γ t x := by
  have hs := (phi_convex W γ ht).slope_le_deriv (mem_univ (x-h)) (mem_univ x) (by linarith) hd
  have hl := phi_lower W γ ht x
  have hu := (phi_terminal_bound W γ ht (x-h)).2
  rw [abs_of_nonneg (hh.le.trans hx)] at hl
  rw [abs_of_nonneg (sub_nonneg.mpr hx)] at hu
  change phi W γ t (x-h)-(x-h)≤terminalError γ t at hu
  change _ ≤ gradient W γ t x at hs
  rw [slope_def_field] at hs
  have hden : x-(x-h)=h := by ring
  rw [hden] at hs
  apply le_trans _ hs
  apply (le_div_iff₀ hh).mpr
  have he : (1-terminalError γ t/h)*h = h-terminalError γ t := by
    field_simp
  rw [he]
  linarith

lemma gradient_upper_of_neg (W : BrownianSpace) (γ : OrderParameter) {t x h : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (hh : 0<h) (hx : x≤-h)
    (hd : DifferentiableAt ℝ (phi W γ t) x) :
    gradient W γ t x ≤ -1+terminalError γ t/h := by
  have hs := (phi_convex W γ ht).deriv_le_slope (mem_univ x) (mem_univ (x+h)) (by linarith) hd
  have hl := phi_lower W γ ht x
  have hu := (phi_terminal_bound W γ ht (x+h)).2
  rw [abs_of_nonpos (by linarith : x≤0)] at hl
  rw [abs_of_nonpos (by linarith : x+h≤0)] at hu
  change phi W γ t (x+h)-(-(x+h))≤terminalError γ t at hu
  change gradient W γ t x≤_ at hs
  rw [slope_def_field] at hs
  have hden : (x+h)-x=h := by ring
  rw [hden] at hs
  apply hs.trans
  apply (div_le_iff₀ hh).mpr
  have he : (-1+terminalError γ t/h)*h = -h+terminalError γ t := by
    field_simp
  rw [he]
  linarith

lemma gradient_terminal_tendsto {ι : Type*} {l : Filter ι}
    (W : BrownianSpace) (γ : OrderParameter) (t x : ι → ℝ) {x₁ : ℝ}
    (ht : Tendsto t l (𝓝 (1 : ℝ))) (hI : ∀ᶠ i in l, t i∈Icc (0 : ℝ) 1)
    (hx : Tendsto x l (𝓝 x₁)) (hne : x₁≠0)
    (hd : ∀ᶠ i in l, DifferentiableAt ℝ (phi W γ (t i)) (x i)) :
    Tendsto (fun i ↦ gradient W γ (t i) (x i)) l (𝓝 (Real.sign x₁)) := by
  have he : Tendsto (fun i ↦ terminalError γ (t i)) l (𝓝 (0 : ℝ)) := by
    simpa only [terminalError_one, Function.comp_def] using (terminalError_continuous γ).continuousAt.tendsto.comp ht
  rcases lt_or_gt_of_ne hne with hn | hp
  · rw [Real.sign_of_neg hn]
    have hhalf : 0 < -x₁/2 := by linarith
    have hx' : ∀ᶠ i in l, x i≤-(-x₁/2) :=
      (hx.eventually (gt_mem_nhds (by linarith : x₁ < -(-x₁/2)))).mono (fun i hi ↦ hi.le)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using tendsto_const_nhds.add (he.div_const (-x₁/2)))
    · filter_upwards [hI] with i hi using (abs_le.mp (gradient_bound W γ hi (x i))).1
    · filter_upwards [hI,hx',hd] with i hi hxi hdi using gradient_upper_of_neg W γ hi hhalf hxi hdi
  · rw [Real.sign_of_pos hp]
    have hhalf : 0<x₁/2 := by linarith
    have hx' : ∀ᶠ i in l, x₁/2≤x i :=
      (hx.eventually (lt_mem_nhds (by linarith : x₁/2<x₁))).mono (fun i hi ↦ hi.le)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using tendsto_const_nhds.sub (he.div_const (x₁/2))) tendsto_const_nhds
    · filter_upwards [hI,hx',hd] with i hi hxi hdi using gradient_lower_of_pos W γ hi hhalf hxi hdi
    · filter_upwards [hI] with i hi using (abs_le.mp (gradient_bound W γ hi (x i))).2

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

lemma IsDiffusion.terminal_gradient_product {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {U : W.Ω → ℝ}
    (hd : ∀ᵐ ω ∂W.μ, ∀ᶠ t in 𝓝[<] (1 : ℝ), DifferentiableAt ℝ (phi W γ t) (X t ω))
    (hU : ∀ᵐ ω ∂W.μ, Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) :
    ∀ᵐ ω ∂W.μ, U ω*X 1 ω=|X 1 ω| := by
  filter_upwards [hX.ae_tendsto,hd,hU] with ω hXω hdω hUω
  by_cases hz : X 1 ω=0
  · simp [hz]
  have hs := gradient_terminal_tendsto W γ id (fun t ↦ X t ω)
    (tendsto_id.mono_left nhdsWithin_le_nhds) eventually_time_mem hXω hz hdω
  have hu : U ω=Real.sign (X 1 ω) := tendsto_nhds_unique hUω hs
  rw [hu]
  rcases lt_or_gt_of_ne hz with hn | hp
  · simp [Real.sign_of_neg hn,abs_of_neg hn]
  · simp [Real.sign_of_pos hp,abs_of_pos hp]

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

lemma intervalIntegrable_substrip {f : ℝ → ℝ} {T a b : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T) (ha : a ∈ Icc (0 : ℝ) T)
    (hb : b ∈ Icc (0 : ℝ) T) : IntervalIntegrable f volume a b := by
  apply hf.mono_set
  rw [uIcc_of_le hT]
  exact uIcc_subset_Icc ha hb

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

lemma gaussian_memLp {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp Z p μ := by
  have H : MemLp (id : ℝ → ℝ) p (μ.map Z) := by
    rw [hZ.map_eq]
    exact memLp_id_gaussianReal' p hp
  simpa using (memLp_map_measure_iff H.aestronglyMeasurable hZ.aemeasurable).1 H

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

lemma gradient_euler_one_step {u : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {t δ x z G K L : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hG : 0≤G) (hK : 0≤K) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0≤γ t) (hγG : γ t≤G)
    (hu : |u t x|≤1) (hsmooth : ContDiff ℝ 3 (u t))
    (hb : |deriv (deriv (u t)) x|≤K) (hthird : ∀ y, |iteratedDeriv 3 (u t) y|≤K)
    (hp : ∀ s ∈ Icc t (t+δ), ∀ y, |u s y*deriv (u s) y|≤K)
    (hbLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |deriv (deriv (u s)) y-deriv (deriv (u t)) x|≤L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |u s y*deriv (u s) y-u t x*deriv (u t) x|≤L*(|s-t|+|y-x|))
    (hbint : ∀ y, IntervalIntegrable (fun s ↦ deriv (deriv (u s)) y) volume t (t+δ))
    (hpint : ∀ y, IntervalIntegrable (fun s ↦ γ s*(u s y*deriv (u s) y)) volume t (t+δ))
    (hPDE : ∀ y, u (t+δ) y-u t y =
      -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (u s)) y+γ s*(u s y*deriv (u s) y))) :
    let d := Real.sqrt δ*z+δ*γ t*u t x
    |u (t+δ) (x+d)-u t x-deriv (u t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (u t)) x*(z^2-1)| ≤
    δ*Real.sqrt δ*(K*(|z|+G)^3+(1/2+G)*L*(1+|z|+G)+K*G*(|z|+G/2))+
      δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*γ t*u t x
  have htm := gradient_generator_quadrature (b := fun s y ↦ deriv (deriv (u s)) y)
    (p := fun s y ↦ u s y*deriv (u s) y) (y := x+d) hδ hG hK hL hγ hγ0 hγG
    (fun s hs ↦ hp s hs _) (fun s hs ↦ hbLip s hs _) (fun s hs ↦ hpLip s hs _)
    (hbint _) (hpint _)
  have ht : |u (t+δ) (x+d)-u t (x+d)+
      δ*((1/2 : ℝ)*deriv (deriv (u t)) x+γ t*u t x*deriv (u t) x)| ≤
      δ*(((1/2 : ℝ)+G)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    rw [hPDE]
    have heq : -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (u s)) (x+d)+
        γ s*(u s (x+d)*deriv (u s) (x+d)))+
        δ*((1/2 : ℝ)*deriv (deriv (u t)) x+γ t*u t x*deriv (u t) x) =
      -((∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (u s)) (x+d)+
        γ s*(u s (x+d)*deriv (u s) (x+d)))-
        δ*((1/2 : ℝ)*deriv (deriv (u t)) x+γ t*(u t x*deriv (u t) x))) := by ring
    rw [heq, abs_neg]
    simpa only [add_sub_cancel_left] using htm
  exact euler_cubic_remainder hδ hδ1 hG hK (by positivity)
    (by rwa [abs_of_nonneg hγ0]) hu hb (third_order_remainder_bound hsmooth hK hthird x d) ht

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

lemma mesh_time_mem_total {T : ℝ} (hT : 0≤T) {N j : ℕ} (hj : j≤N) :
    meshTime T N j∈Icc (0 : ℝ) T := by
  by_cases hN : N=0
  · subst N
    simp only [meshTime, stepSize, Nat.cast_zero, div_zero, mul_zero]
    exact ⟨le_rfl,hT⟩
  · exact mesh_time_mem hT (Nat.pos_of_ne_zero hN) hj

end SKValue

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

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BrownianIncrementIndepPast
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

lemma brownian_increment_indep_past
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F) :
    IndepFun (fun ω ↦ B t ω-B s ω) F μ := by
  have h := (hB.indepFun_shift s).comp (measurable_pi_apply (t-s)) measurable_id
  simp only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] at h
  change Indep (MeasurableSpace.comap (fun ω ↦ B t ω-B s ω) inferInstance)
    (MeasurableSpace.comap (fun ω (r : Iic s) ↦ B r ω) inferInstance) μ at h
  change Indep (MeasurableSpace.comap (fun ω ↦ B t ω-B s ω) inferInstance)
    (MeasurableSpace.comap F inferInstance) μ
  apply indep_of_indep_of_le_right h
  rw [←Filtration.natural_eq_comap B hBm s]
  exact hF.measurable.comap_le

lemma brownian_increment_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    (∫ ω, B t ω-B s ω ∂μ)=0 := by
  change (∫ ω, (B t-B s) ω ∂μ)=0
  rw [(hB.hasLaw_sub t s).integral_eq, integral_id_gaussianReal]

lemma brownian_increment_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {s t : ℝ≥0} (hst : s≤t) :
    (∫ ω, (B t ω-B s ω)^2 ∂μ)=(t : ℝ)-s := by
  have hv := (hB.hasLaw_sub t s).variance_eq
  rw [variance_id_gaussianReal] at hv
  rw [variance_eq_integral (hB.hasLaw_sub t s).aemeasurable] at hv
  simp only [Pi.sub_apply, brownian_increment_integral hB s t, sub_zero] at hv
  have ht' : (s : ℝ)≤t := by exact_mod_cast hst
  exact hv.trans (show (nndist (t:ℝ) (s:ℝ) : ℝ)=(t:ℝ)-s from by
    change |(t:ℝ)-(s:ℝ)|=(t:ℝ)-s
    exact abs_of_nonneg (sub_nonneg.mpr ht'))

lemma brownian_predictable_increment_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F)
    (hFi : Integrable F μ) : Integrable (fun ω ↦ F ω*(B t ω-B s ω)) μ := by
  exact (brownian_increment_indep_past hB hBm hst hF).symm.integrable_mul hFi
    ((hB.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable (by norm_num))

lemma brownian_predictable_increment_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F) :
    (∫ ω, F ω*(B t ω-B s ω) ∂μ)=0 := by
  have hFm := hF.mono (Filtration.le _ s)
  have h := (brownian_increment_indep_past hB hBm hst hF).symm.integral_mul_eq_mul_integral
    hFm.aestronglyMeasurable ((hBm t).sub (hBm s)).aestronglyMeasurable
  simpa only [Pi.mul_apply, brownian_increment_integral hB s t, mul_zero] using h

lemma brownian_predictable_quadratic_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F)
    (hFi : Integrable F μ) :
    Integrable (fun ω ↦ F ω*((B t ω-B s ω)^2-((t : ℝ)-s))) μ := by
  have h := (brownian_increment_indep_past hB hBm hst hF).comp
    (φ := fun x : ℝ ↦ x^2-((t : ℝ)-s))
    ((measurable_id.pow_const 2).sub measurable_const) measurable_id
  have hi : Integrable (fun ω ↦ (B t ω-B s ω)^2-((t : ℝ)-s)) μ :=
    ((hB.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable_sq).sub (integrable_const _)
  exact h.symm.integrable_mul hFi hi

lemma brownian_predictable_quadratic_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F) :
    (∫ ω, F ω*((B t ω-B s ω)^2-((t : ℝ)-s)) ∂μ)=0 := by
  have hFm := hF.mono (Filtration.le _ s)
  have hi : Integrable (fun ω ↦ (B t ω-B s ω)^2) μ :=
    (hB.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable_sq
  have h0 : (∫ ω, (B t ω-B s ω)^2-((t : ℝ)-s) ∂μ)=0 := by
    rw [integral_sub hi (integrable_const _), brownian_increment_second_moment hB hst]
    simp
  have h := (brownian_increment_indep_past hB hBm hst hF).comp
    (φ := fun x : ℝ ↦ x^2-((t : ℝ)-s))
    ((measurable_id.pow_const 2).sub measurable_const) measurable_id
  have hQm : AEStronglyMeasurable (fun ω ↦ (B t ω-B s ω)^2-((t : ℝ)-s)) μ :=
    (((hBm t).sub (hBm s)).pow 2 |>.sub stronglyMeasurable_const).aestronglyMeasurable
  have heq := h.symm.integral_mul_eq_mul_integral hFm.aestronglyMeasurable hQm
  simpa only [Function.comp_def, id_eq, Pi.mul_apply, h0, mul_zero] using heq

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology NNReal ENNReal BigOperators

lemma driftDefect_nonneg (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (X W : ℝ → ℝ) : 0≤driftDefect T N γ u X W :=
  Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

lemma driftDefect_error_bound {T L ε : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} (hT : 0≤T) (hN : 0<N) (hL : 0≤L) (hε : 0≤ε)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hu : ∀ t∈Icc (0 : ℝ) T, ∀ x, |u t x|≤1)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤L*(|s-t|+|x-y|))
    (hXosc : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T,
      |s-t|≤ stepSize T N → |X s-X t|≤ε)
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t∈Icc (0 : ℝ) T, X t=W t+∫ s in (0 : ℝ)..t, γ s*u s (X s)) :
    driftDefect T N γ u X W ≤
      stepSize T N*(γ T-γ 0)+T*γ T*L*(stepSize T N+ε) := by
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hδ : 0≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  have hmesh : (N : ℝ)*stepSize T N=T := by dsimp [stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+stepSize T N := by
    dsimp [meshTime]; push_cast; ring
  have hG : 0≤γ T := hγ0.trans (hγ ht0 htT hT)
  have hγpos (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : 0≤γ t :=
    hγ0.trans (hγ ht0 ht ht.1)
  have hlocal (i : Fin N) :
      |X (meshTime T N (i+1))-X (meshTime T N i)-
        (W (meshTime T N (i+1))-W (meshTime T N i))-
        stepSize T N*γ (meshTime T N i)*u (meshTime T N i) (X (meshTime T N i))|≤
      stepSize T N*(γ (meshTime T N (i+1))-γ (meshTime T N i))+
        stepSize T N*γ T*L*(stepSize T N+ε) := by
    let a := meshTime T N i
    let b := meshTime T N (i+1)
    have ha := htime i i.isLt.le
    have hb := htime (i+1) (by omega)
    have hlen : b-a=stepSize T N := by dsimp [a,b]; rw [hsucc]; ring
    have hab : a≤b := by linarith
    have hsub : Icc a b⊆Icc (0 : ℝ) T := Icc_subset_Icc ha.1 hb.2
    have hh := monotone_drift_local_error hab hG hL hε (hγ.mono hsub)
      (hγpos a ha) (hγ ha htT ha.2) (fun s hs ↦ hu s (hsub hs) _)
      (fun s hs ↦ hLip s (hsub hs) a ha _ _)
      (fun s hs ↦ hXosc s (hsub hs) a ha (by
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        linarith [hs.2]))
      (intervalIntegrable_substrip hT hint ha hb)
    have hdiff : X b-X a-(W b-W a)=∫ s in a..b, γ s*u s (X s) := by
      rw [hX b hb,hX a ha]
      have he := intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_substrip hT hint ht0 hb)
        (intervalIntegrable_substrip hT hint ht0 ha)
      linear_combination he
    dsimp only [a,b] at hdiff hlen
    rw [hdiff]
    simpa only [hlen, a,b] using hh
  calc
    _ ≤ ∑ i : Fin N, (stepSize T N*(γ (meshTime T N (i+1))-γ (meshTime T N i))+
        stepSize T N*γ T*L*(stepSize T N+ε)) := Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = _ := by
      rw [Finset.sum_add_distrib, ←Finset.mul_sum, sum_steps_sub (fun j ↦ γ (meshTime T N j))]
      simp only [meshTime, Nat.cast_zero, zero_mul, hmesh, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      linear_combination (γ T*L*(stepSize T N+ε))*hmesh

lemma driftDefect_tendsto {T L : ℝ} {u : ℝ → ℝ → ℝ} {γ W X : ℝ → ℝ}
    (hT : 0≤T) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hu : ∀ t∈Icc (0 : ℝ) T, ∀ x, |u t x|≤1)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤L*(|s-t|+|x-y|))
    (hXcont : ContinuousOn X (Icc (0 : ℝ) T))
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t∈Icc (0 : ℝ) T, X t=W t+∫ s in (0 : ℝ)..t, γ s*u s (X s)) :
    Tendsto (fun N ↦ driftDefect T N γ u X W) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hG : 0≤γ T := hγ0.trans (hγ ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT)
  let C := T*γ T*L
  have hC : 0≤C := by dsimp [C]; positivity
  let η := ε/(2*(C+1))
  have hη : 0<η := by dsimp [η]; positivity
  have hηeq : η*(2*(C+1))=ε := div_mul_cancel₀ _ (by positivity)
  have hCη : C*η<ε/2 := by nlinarith
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hXcont) η hη
  have hδ : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have htail : Tendsto (fun N : ℕ ↦ stepSize T N*((γ T-γ 0)+C)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hδ.mul_const ((γ T-γ 0)+C)
  have hev : ∀ᶠ N in atTop, dist (driftDefect T N γ u X W) 0<ε := by
    filter_upwards [hδ.eventually_le_const hθ, htail.eventually_lt_const (half_pos hε),
      eventually_gt_atTop 0] with N hNθ hNerr hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (driftDefect_nonneg T N γ u X W)]
    have hh := driftDefect_error_bound hT hN hL hη.le hγ hγ0 hu hLip
      (fun s hs t ht hst ↦ by
        have hst' := hmod s hs t ht (by simpa only [Real.dist_eq] using hst.trans hNθ)
        simpa only [Real.dist_eq] using hst') hint hX
    dsimp only [C] at hCη hNerr
    linarith
  exact eventually_atTop.mp hev

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_DriftDefectUniformBound
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
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology NNReal ENNReal BigOperators

lemma driftDefect_uniform_bound {T : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} (hT : 0≤T)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hu : ∀ t∈Icc (0 : ℝ) T, ∀ x, |u t x|≤1)
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t∈Icc (0 : ℝ) T, X t=W t+∫ s in (0 : ℝ)..t, γ s*u s (X s)) :
    driftDefect T N γ u X W≤2*T*γ T := by
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hG : 0≤γ T := hγ0.trans (hγ ht0 htT hT)
  by_cases hN : N=0
  · subst N
    simp only [driftDefect, Fin.sum_univ_zero]
    positivity
  have hNpos : 0<N := Nat.pos_of_ne_zero hN
  have hδ : 0≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN
  have hmesh : (N : ℝ)*stepSize T N=T := by dsimp [stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+stepSize T N := by
    dsimp [meshTime]; push_cast; ring
  have hγpos (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : 0≤γ t :=
    hγ0.trans (hγ ht0 ht ht.1)
  have hgb (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |γ t*u t (X t)|≤γ T := by
    rw [abs_mul,abs_of_nonneg (hγpos t ht)]
    calc
      γ t*|u t (X t)|≤γ t*1 := mul_le_mul_of_nonneg_left (hu t ht _) (hγpos t ht)
      _ ≤ γ T := by simpa only [mul_one] using hγ ht htT ht.2
  have hlocal (i : Fin N) :
      |X (meshTime T N (i+1))-X (meshTime T N i)-
        (W (meshTime T N (i+1))-W (meshTime T N i))-
        stepSize T N*γ (meshTime T N i)*u (meshTime T N i) (X (meshTime T N i))|≤
      2*stepSize T N*γ T := by
    let a := meshTime T N i
    let b := meshTime T N (i+1)
    have ha := htime i i.isLt.le
    have hb := htime (i+1) (by omega)
    have hlen : b-a=stepSize T N := by dsimp [a,b]; rw [hsucc]; ring
    have hab : a≤b := by linarith
    have hsub : Icc a b⊆Icc (0 : ℝ) T := Icc_subset_Icc ha.1 hb.2
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun s ↦ γ s*u s (X s)) (C:=γ T) (a:=a) (b:=b)
      (fun s hs ↦ by
        rw [Real.norm_eq_abs]
        rw [uIoc_of_le hab] at hs
        exact hgb s (hsub ⟨hs.1.le,hs.2⟩))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), hlen] at hi
    have hdiff : X b-X a-(W b-W a)=∫ s in a..b, γ s*u s (X s) := by
      rw [hX b hb,hX a ha]
      have he := intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_substrip hT hint ht0 hb)
        (intervalIntegrable_substrip hT hint ht0 ha)
      linear_combination he
    change |X b-X a-(W b-W a)-stepSize T N*γ a*u a (X a)|≤_
    rw [hdiff]
    have hic := (abs_sub _ _).trans (add_le_add hi (show
        |stepSize T N*γ a*u a (X a)|≤ stepSize T N*γ T from by
      rw [mul_assoc,abs_mul,abs_of_nonneg hδ]
      exact mul_le_mul_of_nonneg_left (hgb a ha) hδ))
    linarith
  calc
    driftDefect T N γ u X W≤∑ _i : Fin N, 2*stepSize T N*γ T :=
      Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = 2*T*γ T := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      linear_combination (2*γ T)*hmesh

lemma driftDefect_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ} {γ : ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    (hT : 0≤T) (hUm : ∀ t∈Icc (0 : ℝ) T, Continuous (u t))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ) :
    AEStronglyMeasurable (fun ω ↦ driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω)) μ := by
  unfold driftDefect
  apply Finset.aestronglyMeasurable_fun_sum
  intro i _
  have ha := mesh_time_mem_total hT (show (i : ℕ)≤N from i.isLt.le)
  have hb := mesh_time_mem_total hT (show (i : ℕ)+1≤N from i.isLt)
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using ((((hXM _ hb).sub (hXM _ ha)).sub ((hWM _ hb).sub (hWM _ ha))).sub
    (((hUm _ ha).comp_aestronglyMeasurable (hXM _ ha)).const_mul
      (stepSize T N*γ (meshTime T N i)))).norm

lemma driftDefect_integral_tendsto {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {T L : ℝ} {u : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {X W : ℝ → Ω → ℝ} (hT : 0≤T) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hu : ∀ t∈Icc (0 : ℝ) T, ∀ x, |u t x|≤1)
    (hUm : ∀ t∈Icc (0 : ℝ) T, Continuous (u t))
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤L*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) :
    Tendsto (fun N ↦ ∫ ω, driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have H := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω ↦ 2*T*γ T)
    (Eventually.of_forall (fun N ↦ driftDefect_aestronglyMeasurable hT hUm hXM hWM (N:=N)))
    (Eventually.of_forall (fun N ↦ hpaths.mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (driftDefect_nonneg T N γ u _ _)]
      exact driftDefect_uniform_bound hT hγ hγ0 hu hω.2.1 hω.2.2)))
    (integrable_const _) (hpaths.mono (fun ω hω ↦
      driftDefect_tendsto hT hL hγ hγ0 hu hLip hω.1 hω.2.1 hω.2.2))
  simpa only [integral_zero] using H

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientStripCore
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

lemma GradientStrip.toCore {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStrip T γ u K L) : GradientStripCore T γ u K L :=
  ⟨h.K_nonneg,h.L_nonneg,h.gamma_nonneg,h.gamma_mono,h.smooth,h.bounded,
    h.second_bound,h.third_bound,h.product_bound,h.second_lipschitz,
    h.product_lipschitz,h.second_integrable,h.product_integrable,h.pde⟩

lemma pathGradientResidual_bound {T K L Lu : ℝ} {N : ℕ} {γ : ℝ → ℝ}
    {u : ℝ → ℝ → ℝ} {X W : ℝ → ℝ} {Z : Fin N → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hN : 0<N) (_hLu : 0≤Lu)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |u t x-u t y|≤Lu*|x-y|)
    (hZ : ∀ i : Fin N, Real.sqrt (stepSize T N)*Z i=
      W (meshTime T N (i+1))-W (meshTime T N i)) :
    |pathGradientResidual T N u X W|≤Lu*driftDefect T N γ u X W+
      stepSize T N*Real.sqrt (stepSize T N)*
        (∑ i : Fin N, cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i))+
      stepSize T N*K*(γ T-γ 0) := by
  let δ := stepSize T N
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0≤δ := div_nonneg hT.le hNr.le
  have hδ1 : δ≤1 := by
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    exact (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hmesh : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT.le⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+δ := by
    dsimp [meshTime,δ]; push_cast; ring
  have hlast : meshTime T N N=T := hmesh
  have hzero : meshTime T N 0=0 := by simp only [meshTime,Nat.cast_zero,zero_mul]
  have hG : 0≤γ T := h.gamma_nonneg T htT
  let D := fun i : Fin N ↦ W (meshTime T N (i+1))-W (meshTime T N i)
  let R := fun i : Fin N ↦ u (meshTime T N (i+1)) (X (meshTime T N (i+1)))-
    u (meshTime T N i) (X (meshTime T N i))-
    deriv (u (meshTime T N i)) (X (meshTime T N i))*D i-
    (1/2 : ℝ)*deriv (deriv (u (meshTime T N i))) (X (meshTime T N i))*(D i^2-δ)
  let E := fun i : Fin N ↦ |X (meshTime T N (i+1))-X (meshTime T N i)-D i-
    δ*γ (meshTime T N i)*u (meshTime T N i) (X (meshTime T N i))|
  have hlocal (i : Fin N) : |R i|≤Lu*E i+
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i)+
      δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [←hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hbint (x : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (u s)) x) volume t (t+δ) :=
      intervalIntegrable_substrip hT.le (h.second_integrable x) ht ht'
    have hpint (x : ℝ) : IntervalIntegrable (fun s ↦ γ s*(u s x*deriv (u s) x)) volume t (t+δ) :=
      intervalIntegrable_substrip hT.le (h.product_integrable x) ht ht'
    have hh := gradient_euler_one_step (x:=X t) (z:=Z i) hδ hδ1 hG h.K_nonneg h.L_nonneg
      (h.gamma_mono.mono hsub) (h.gamma_nonneg t ht) (h.gamma_mono ht htT ht.2)
      (h.bounded t ht _) (h.smooth t ht) (h.second_bound t ht _) (h.third_bound t ht)
      (fun s hs ↦ h.product_bound s (hsub hs))
      (fun s hs y ↦ h.second_lipschitz t ht s (hsub hs) _ y)
      (fun s hs y ↦ h.product_lipschitz t ht s (hsub hs) _ y)
      hbint hpint (h.pde t ht (t+δ) ht')
    dsimp only at hh
    have hd : (D i)^2=δ*(Z i)^2 := by
      change (W _-W _)^2=_
      rw [←hZ i,mul_pow,Real.sq_sqrt hδ]
    have hh' : |u (t+δ) (X t+(D i+δ*γ t*u t (X t)))-u t (X t)-
        deriv (u t) (X t)*D i-(1/2 : ℝ)*deriv (deriv (u t)) (X t)*(D i^2-δ)|≤
        δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i)+
          δ*K*(γ (t+δ)-γ t) := by
      have hZd : Real.sqrt δ*Z i=D i := hZ i
      have heq : (1/2 : ℝ)*deriv (deriv (u t)) (X t)*(δ*(Z i)^2-δ)=
          (1/2 : ℝ)*δ*deriv (deriv (u t)) (X t)*((Z i)^2-1) := by ring
      rw [←hZd,mul_pow,Real.sq_sqrt hδ,heq]
      simpa only [cubicEnvelope,mul_assoc] using hh
    have hlu := hLip (t+δ) ht' (X (t+δ)) (X t+(D i+δ*γ t*u t (X t)))
    have he : |X (t+δ)-(X t+(D i+δ*γ t*u t (X t)))|=E i := by
      dsimp only [E,t]
      rw [hsucc]
      congr 1
      ring
    rw [he] at hlu
    have hdecomp : R i=(u (t+δ) (X (t+δ))-
        u (t+δ) (X t+(D i+δ*γ t*u t (X t))))+
        (u (t+δ) (X t+(D i+δ*γ t*u t (X t)))-u t (X t)-
          deriv (u t) (X t)*D i-(1/2 : ℝ)*deriv (deriv (u t)) (X t)*(D i^2-δ)) := by
      dsimp only [R,t]
      rw [hsucc]
      ring
    rw [hdecomp]
    have hn := (abs_add_le _ _).trans (add_le_add hlu hh')
    simpa only [t,←hsucc,add_assoc] using hn
  have hsumEq : pathGradientResidual T N u X W=∑ i : Fin N, R i := by
    dsimp only [pathGradientResidual,R,D]
    rw [sum_local_residual (fun j ↦ u (meshTime T N j) (X (meshTime T N j)))]
    rw [hlast,hzero,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsumEq]
  calc
    _ ≤ ∑ i : Fin N, |R i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, (Lu*E i+δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i)+
      δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i))) := Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = _ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum]
      rw [sum_steps_sub (fun j ↦ γ (meshTime T N j)),hlast,hzero]
      rfl

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_CubicEnvelopeMean
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

lemma GradientStripCore.continuous_second {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStripCore T γ u K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    Continuous (deriv (deriv (u t))) := by
  have hc := (h.smooth t ht).continuous_iteratedDeriv 2 (by norm_num)
  simpa only [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hc

lemma GradientStripCore.continuous_deriv {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStripCore T γ u K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    Continuous (deriv (u t)) := by
  simpa only [iteratedDeriv_one] using (h.smooth t ht).continuous_iteratedDeriv 1 (by norm_num)

lemma pathGradientResidual_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T K L : ℝ} {N : ℕ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    (hT : 0≤T) (h : GradientStripCore T γ u K L)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ) :
    AEStronglyMeasurable (fun ω ↦ pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)) μ := by
  have htime (j : ℕ) (hj : j≤N) := mesh_time_mem_total hT hj
  have hprodA (i : Fin N) : AEStronglyMeasurable (fun ω ↦
      deriv (u (meshTime T N i)) (X (meshTime T N i) ω)*
        (W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)) μ :=
    ((h.continuous_deriv (htime i i.isLt.le)).comp_aestronglyMeasurable
      (hXM _ (htime i i.isLt.le))).mul
      ((hWM _ (htime (i+1) i.isLt)).sub (hWM _ (htime i i.isLt.le)))
  have hprodQ (i : Fin N) : AEStronglyMeasurable (fun ω ↦
      deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)*
        ((W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)^2-stepSize T N)) μ :=
    ((h.continuous_second (htime i i.isLt.le)).comp_aestronglyMeasurable
      (hXM _ (htime i i.isLt.le))).mul
      (((hWM _ (htime (i+1) i.isLt)).sub (hWM _ (htime i i.isLt.le))).pow 2 |>.sub aestronglyMeasurable_const)
  exact ((((h.smooth T ⟨hT,le_rfl⟩).continuous.comp_aestronglyMeasurable (hXM T ⟨hT,le_rfl⟩)).sub
    ((h.smooth 0 ⟨le_rfl,hT⟩).continuous.comp_aestronglyMeasurable (hXM 0 ⟨le_rfl,hT⟩))).sub
      (Finset.aestronglyMeasurable_fun_sum _ (fun i _ ↦ hprodA i))).sub
        ((Finset.aestronglyMeasurable_fun_sum _ (fun i _ ↦ hprodQ i)).const_mul (1/2))

lemma pathGradientResidual_L1_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T K L Lu : ℝ} {N : ℕ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    {Z : Fin N → Ω → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hN : 0<N) (hLu : 0≤Lu)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |u t x-u t y|≤Lu*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hZlaw : ∀ i, HasLaw (Z i) standardGaussian μ)
    (hZ : ∀ i : Fin N, ∀ ω, Real.sqrt (stepSize T N)*Z i ω=
      W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)
    (hpaths : ∀ᵐ ω ∂μ,
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) :
    Integrable (fun ω ↦ pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)) μ ∧
    (∫ ω, |pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)| ∂μ)≤
      Lu*(∫ ω, driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)+
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
      stepSize T N*K*(γ T-γ 0) := by
  let D := fun ω ↦ driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω)
  let R := fun ω ↦ pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)
  let P := fun i : Fin N ↦ fun ω ↦ cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i ω)
  have hG : 0≤γ T := h.gamma_nonneg T ⟨hT.le,le_rfl⟩
  have hDi : Integrable D μ := (integrable_const (2*T*γ T)).mono'
    (driftDefect_aestronglyMeasurable hT.le (fun t ht ↦ (h.smooth t ht).continuous) hXM hWM)
    (hpaths.mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (driftDefect_nonneg T N γ u _ _)]
      exact driftDefect_uniform_bound hT.le h.gamma_mono (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩)
        h.bounded hω.1 hω.2))
  have hPi (i : Fin N) : Integrable (P i) μ :=
    (cubicEnvelope_memLp_two (hZlaw i) hG K ((1/2+γ T)*L)).integrable (by norm_num)
  have hPint (i : Fin N) : (∫ ω, P i ω ∂μ)=cubicEnvelopeMean (γ T) K ((1/2+γ T)*L) := by
    exact (hZlaw i).integral_comp (measurable_cubicEnvelope _ _ _).aestronglyMeasurable
  let E := fun ω ↦ Lu*D ω+stepSize T N*Real.sqrt (stepSize T N)*(∑ i : Fin N,P i ω)+
    stepSize T N*K*(γ T-γ 0)
  have hEi : Integrable E μ := ((hDi.const_mul Lu).add
    ((integrable_finsetSum _ (fun i _ ↦ hPi i)).const_mul
      (stepSize T N*Real.sqrt (stepSize T N)))).add (integrable_const _)
  have hRE (ω : Ω) : |R ω|≤E ω := pathGradientResidual_bound hT hT1 hN hLu h hLip (fun i ↦ hZ i ω)
  have hRi : Integrable R μ := hEi.mono'
    (pathGradientResidual_aestronglyMeasurable hT.le h hXM hWM)
    (Eventually.of_forall (fun ω ↦ by rw [Real.norm_eq_abs]; exact hRE ω))
  refine ⟨hRi,?_⟩
  calc
    (∫ ω, |R ω| ∂μ)≤∫ ω, E ω ∂μ := integral_mono hRi.abs hEi hRE
    _ = _ := by
      dsimp only [E]
      rw [integral_add
        (f := fun ω ↦ Lu*D ω+stepSize T N*Real.sqrt (stepSize T N)*(∑ i : Fin N,P i ω))
        (g := fun _ ↦ stepSize T N*K*(γ T-γ 0))
        ((hDi.const_mul Lu).add ((integrable_finsetSum _ (fun i _ ↦ hPi i)).const_mul _))
        (integrable_const _),
        integral_add (f := fun ω ↦ Lu*D ω)
          (g := fun ω ↦ stepSize T N*Real.sqrt (stepSize T N)*(∑ i : Fin N,P i ω))
          (hDi.const_mul Lu) ((integrable_finsetSum _ (fun i _ ↦ hPi i)).const_mul _),
        integral_const_mul,integral_const_mul,integral_finsetSum _ (fun i _ ↦ hPi i)]
      simp only [hPint,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        integral_const,probReal_univ,smul_eq_mul,one_mul]
      have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
      have hm : (N : ℝ)*stepSize T N=T := by dsimp [stepSize]; field_simp
      dsimp only [D]
      linear_combination (Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L))*hm

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma pathGradientResidual_L1_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    {Z : (N : ℕ) → Fin N → Ω → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hLu : 0≤Lu)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hZlaw : ∀ N, 0<N → ∀ i, HasLaw (Z N i) standardGaussian μ)
    (hZ : ∀ N, 0<N → ∀ i : Fin N, ∀ ω, Real.sqrt (stepSize T N)*Z N i ω=
      W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) :
    Tendsto (fun N ↦ ∫ ω, |pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)| ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hD := driftDefect_integral_tendsto hT.le hLu h.gamma_mono
    (h.gamma_nonneg 0 ⟨le_rfl,hT.le⟩) h.bounded
    (fun t ht ↦ (h.smooth t ht).continuous) hLip hXM hWM hpaths
  have hs : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hLim : Tendsto (fun N ↦
      Lu*(∫ ω, driftDefect T N γ u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)+
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
      stepSize T N*K*(γ T-γ 0)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero,mul_zero,zero_mul,add_zero,Function.comp_def] using
      ((hD.const_mul Lu).add (((Real.continuous_sqrt.tendsto 0).comp hs).const_mul T |>.mul_const
        (cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)))).add
        ((hs.mul_const K).mul_const (γ T-γ 0))
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ integral_nonneg (fun ω ↦ abs_nonneg _))) _ hLim
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (pathGradientResidual_L1_bound hT hT1 hN hLu h
    (fun t ht x y ↦ by simpa only [sub_self,abs_zero,zero_add] using hLip t ht t ht x y)
    hXM hWM (hZlaw N hN) (hZ N hN) (hpaths.mono (fun _ hh ↦ hh.2))).2

lemma weighted_pathGradientResidual_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T K L Lu H : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    {F : Ω → ℝ} {Z : (N : ℕ) → Fin N → Ω → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hLu : 0≤Lu) (hH : 0≤H)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hZlaw : ∀ N, 0<N → ∀ i, HasLaw (Z N i) standardGaussian μ)
    (hZ : ∀ N, 0<N → ∀ i : Fin N, ∀ ω, Real.sqrt (stepSize T N)*Z N i ω=
      W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω))
    (hFm : AEStronglyMeasurable F μ) (hFb : ∀ ω, |F ω|≤H) :
    Tendsto (fun N ↦ ∫ ω, F ω*pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hLim := pathGradientResidual_L1_tendsto hT hT1 hLu h hLip hXM hWM hZlaw hZ hpaths
  have hLim' : Tendsto (fun N ↦ H*(∫ ω,
      |pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)| ∂μ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hLim.const_mul H
  apply squeeze_zero_norm' _ hLim'
  filter_upwards [eventually_gt_atTop 0] with N hN
  let R := fun ω ↦ pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)
  have hRi : Integrable R μ := (pathGradientResidual_L1_bound hT hT1 hN hLu h
    (fun t ht x y ↦ by simpa only [sub_self,abs_zero,zero_add] using hLip t ht t ht x y)
    hXM hWM (hZlaw N hN) (hZ N hN) (hpaths.mono (fun _ hh ↦ hh.2))).1
  have hFRi : Integrable (fun ω ↦ F ω*R ω) μ := hRi.bdd_mul hFm
    (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hFb ω))
  rw [Real.norm_eq_abs]
  calc
    |∫ ω, F ω*R ω ∂μ|≤∫ ω, |F ω*R ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, H*|R ω| ∂μ := integral_mono hFRi.abs (hRi.abs.const_mul H) (fun ω ↦ by
      rw [abs_mul]; exact mul_le_mul (hFb ω) le_rfl (abs_nonneg _) hH)
    _ = _ := integral_const_mul _ _

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_ShiftedBrownianCoordinates
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
open scoped Topology NNReal BigOperators

lemma shiftedBrownianCoordinates_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (a : ℝ≥0)
    {T : ℝ} {N : ℕ} (hT : 0<T) (hN : 0<N) (i : Fin N) :
    HasLaw (shiftedBrownianCoordinates B a T N i) standardGaussian μ := by
  apply brownian_coordinate_hasLaw (hB.shift a)
  exact Real.toNNReal_pos.mpr (div_pos hT (by exact_mod_cast hN))

lemma meshTime_toNNReal {T : ℝ} {N : ℕ} (hT : 0≤T) (j : ℕ) :
    Real.toNNReal (meshTime T N j)=(j : ℝ≥0)*Real.toNNReal (stepSize T N) := by
  have hδ : 0≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  apply NNReal.coe_injective
  unfold meshTime
  rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg j) hδ),
    NNReal.coe_mul,NNReal.coe_natCast,Real.coe_toNNReal _ hδ]

lemma shiftedBrownianCoordinates_exact
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {W : ℝ → Ω → ℝ} {a : ℝ≥0}
    {T : ℝ} {N : ℕ} (hT : 0<T) (hN : 0<N)
    (hW : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ ω,
      W t ω-W s ω=B (a+t.toNNReal) ω-B (a+s.toNNReal) ω)
    (i : Fin N) (ω : Ω) :
    Real.sqrt (stepSize T N)*shiftedBrownianCoordinates B a T N i ω=
      W (meshTime T N (i+1)) ω-W (meshTime T N i) ω := by
  have hδ : 0≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
  have hδ' : 0<Real.toNNReal (stepSize T N) :=
    Real.toNNReal_pos.mpr (div_pos hT (by exact_mod_cast hN))
  rw [hW _ (mesh_time_mem_total hT.le i.isLt.le) _ (mesh_time_mem_total hT.le i.isLt) ω]
  rw [meshTime_toNNReal hT.le,meshTime_toNNReal hT.le]
  have hh := brownian_coordinate_exact (fun r ω ↦ B (a+r) ω-B a ω) hδ' N ω i
  simp only [Real.coe_toNNReal _ hδ] at hh
  change Real.sqrt (stepSize T N)*brownianCoordinates _ _ _ _ _=_
  linarith

lemma GradientStripCore.deriv_bound {T Lu : ℝ} {u : ℝ → ℝ → ℝ}
    (hLu : 0≤Lu) (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |u t x-u t y|≤Lu*|x-y|)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) T) (x : ℝ) : |deriv (u t) x|≤Lu := by
  have hl : LipschitzWith ⟨Lu,hLu⟩ (u t) :=
    LipschitzWith.of_dist_le_mul (fun y z ↦ by
      change dist (u t y) (u t z)≤Lu*dist y z
      simpa only [Real.dist_eq] using hLip t ht y z)
  have hh := norm_deriv_le_of_lipschitz (x₀:=x) hl
  change ‖deriv (u t) x‖≤Lu at hh
  simpa only [Real.norm_eq_abs] using hh

lemma weighted_pathGradientResidual_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ} {F : Ω → ℝ}
    (hVT : Integrable (fun ω ↦ F ω*u T (X T ω)) μ)
    (hV0 : Integrable (fun ω ↦ F ω*u 0 (X 0 ω)) μ)
    (hLi : ∀ i : Fin N, Integrable (fun ω ↦ F ω*
      (deriv (u (meshTime T N i)) (X (meshTime T N i) ω)*
        (W (meshTime T N (i+1)) ω-W (meshTime T N i) ω))) μ)
    (hQi : ∀ i : Fin N, Integrable (fun ω ↦ F ω*
      (deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)*
        ((W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)^2-stepSize T N))) μ)
    (hL0 : ∀ i : Fin N, (∫ ω, F ω*
      (deriv (u (meshTime T N i)) (X (meshTime T N i) ω)*
        (W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)) ∂μ)=0)
    (hQ0 : ∀ i : Fin N, (∫ ω, F ω*
      (deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)*
        ((W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)^2-stepSize T N)) ∂μ)=0) :
    (∫ ω, F ω*pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω) ∂μ)=
      (∫ ω, F ω*u T (X T ω) ∂μ)-(∫ ω, F ω*u 0 (X 0 ω) ∂μ) := by
  let P := fun i : Fin N ↦ fun ω ↦ F ω*
    (deriv (u (meshTime T N i)) (X (meshTime T N i) ω)*
      (W (meshTime T N (i+1)) ω-W (meshTime T N i) ω))
  let Q := fun i : Fin N ↦ fun ω ↦ F ω*
    (deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)*
      ((W (meshTime T N (i+1)) ω-W (meshTime T N i) ω)^2-stepSize T N))
  have hPi : Integrable (fun ω ↦ ∑ i : Fin N,P i ω) μ := integrable_finsetSum _ (fun i _ ↦ hLi i)
  have hQi' : Integrable (fun ω ↦ ∑ i : Fin N,Q i ω) μ := integrable_finsetSum _ (fun i _ ↦ hQi i)
  have heq (ω : Ω) : F ω*pathGradientResidual T N u (fun t ↦ X t ω) (fun t ↦ W t ω)=
      (F ω*u T (X T ω)-F ω*u 0 (X 0 ω)-(∑ i : Fin N,P i ω))-
        (1/2 : ℝ)*(∑ i : Fin N,Q i ω) := by
    simp only [pathGradientResidual,P,Q,mul_sub,Finset.mul_sum,mul_left_comm,mul_comm]
  simp_rw [heq]
  rw [integral_sub (f := fun ω ↦ F ω*u T (X T ω)-F ω*u 0 (X 0 ω)-∑ i : Fin N,P i ω)
    (g := fun ω ↦ (1/2 : ℝ)*(∑ i : Fin N,Q i ω)) ((hVT.sub hV0).sub hPi) (hQi'.const_mul _)]
  rw [integral_sub (f := fun ω ↦ F ω*u T (X T ω)-F ω*u 0 (X 0 ω))
    (g := fun ω ↦ ∑ i : Fin N,P i ω) (hVT.sub hV0) hPi]
  rw [integral_sub hVT hV0,integral_const_mul,
    integral_finsetSum _ (fun i _ ↦ hLi i),integral_finsetSum _ (fun i _ ↦ hQi i)]
  simp only [hL0,hQ0,Finset.sum_const_zero,mul_zero,sub_zero]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_DiffusionGradientWeakMartingaleLocal
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
open scoped Topology NNReal BigOperators

lemma diffusion_gradient_weak_martingale_local
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) (a : ℝ≥0)
    {T K L Lu H : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    {F : Ω → ℝ} (hT : 0<T) (hT1 : T≤1) (hLu : 0≤Lu) (hH : 0≤H)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T,
      StronglyMeasurable[Filtration.natural B hBm (a+t.toNNReal)] (X t))
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hW : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ ω,
      W t ω-W s ω=B (a+t.toNNReal) ω-B (a+s.toNNReal) ω)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω))
    (hFm : StronglyMeasurable[Filtration.natural B hBm a] F) (hFb : ∀ ω, |F ω|≤H) :
    (∫ ω, F ω*u T (X T ω) ∂μ)=(∫ ω, F ω*u 0 (X 0 ω) ∂μ) := by
  let ℱ := Filtration.natural B hBm
  have hFM : AEStronglyMeasurable F μ := (hFm.mono (ℱ.le a)).aestronglyMeasurable
  have hXM' (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : AEStronglyMeasurable (X t) μ :=
    ((hXM t ht).mono (ℱ.le _)).aestronglyMeasurable
  have hsp (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x y : ℝ) :
      |u t x-u t y|≤Lu*|x-y| := by
    simpa only [sub_self,abs_zero,zero_add] using hLip t ht t ht x y
  have hVi (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : Integrable (fun ω ↦ F ω*u t (X t ω)) μ := by
    apply Integrable.of_bound (hFM.mul ((h.smooth t ht).continuous.comp_aestronglyMeasurable (hXM' t ht))) H
    filter_upwards [] with ω
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (hFb ω) (h.bounded t ht _) (abs_nonneg _) hH).trans_eq (mul_one H)
  have hlim := weighted_pathGradientResidual_tendsto (Z:=shiftedBrownianCoordinates B a T)
    hT hT1 hLu hH h hLip hXM' hWM
    (fun N hN i ↦ shiftedBrownianCoordinates_hasLaw hB a hT hN i)
    (fun N hN i ω ↦ shiftedBrownianCoordinates_exact hT hN hW i ω) hpaths hFM hFb
  have hmean (N : ℕ) : (∫ ω, F ω*pathGradientResidual T N u (fun t ↦ X t ω)
      (fun t ↦ W t ω) ∂μ)=(∫ ω, F ω*u T (X T ω) ∂μ)-(∫ ω, F ω*u 0 (X 0 ω) ∂μ) := by
    have hδ : 0≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
    have htime (j : ℕ) (hj : j≤N) := mesh_time_mem_total hT.le hj
    let τ := fun j : ℕ ↦ a+(meshTime T N j).toNNReal
    have hτ (i : Fin N) : τ i≤τ (i+1) := by
      dsimp [τ]
      apply add_le_add le_rfl
      apply Real.toNNReal_mono
      dsimp [meshTime]
      push_cast
      nlinarith
    have hτdiff (i : Fin N) : (τ (i+1) : ℝ)-(τ i : ℝ)=stepSize T N := by
      dsimp only [τ]
      rw [NNReal.coe_add,NNReal.coe_add,Real.coe_toNNReal _ (htime (i+1) i.isLt).1,
        Real.coe_toNNReal _ (htime i i.isLt.le).1]
      dsimp [meshTime]
      push_cast
      ring
    have hWeq (i : Fin N) (ω : Ω) :
        W (meshTime T N (i+1)) ω-W (meshTime T N i) ω=B (τ (i+1)) ω-B (τ i) ω :=
      hW _ (htime i i.isLt.le) _ (htime (i+1) i.isLt) ω
    have hFm' (i : Fin N) : StronglyMeasurable[ℱ (τ i)] F :=
      hFm.mono (ℱ.mono (le_add_of_nonneg_right (by positivity)))
    have hDm (i : Fin N) : StronglyMeasurable[ℱ (τ i)]
        (fun ω ↦ F ω*deriv (u (meshTime T N i)) (X (meshTime T N i) ω)) :=
      (hFm' i).mul ((h.continuous_deriv (htime i i.isLt.le)).comp_stronglyMeasurable
        (hXM _ (htime i i.isLt.le)))
    have hD2m (i : Fin N) : StronglyMeasurable[ℱ (τ i)]
        (fun ω ↦ F ω*deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)) :=
      (hFm' i).mul ((h.continuous_second (htime i i.isLt.le)).comp_stronglyMeasurable
        (hXM _ (htime i i.isLt.le)))
    have hDi (i : Fin N) : Integrable
        (fun ω ↦ F ω*deriv (u (meshTime T N i)) (X (meshTime T N i) ω)) μ := by
      apply Integrable.of_bound ((hDm i).mono (ℱ.le _)).aestronglyMeasurable (H*Lu)
      filter_upwards [] with ω
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hFb ω) (GradientStripCore.deriv_bound hLu hsp (htime i i.isLt.le) _)
        (abs_nonneg _) hH
    have hD2i (i : Fin N) : Integrable
        (fun ω ↦ F ω*deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)) μ := by
      apply Integrable.of_bound ((hD2m i).mono (ℱ.le _)).aestronglyMeasurable (H*K)
      filter_upwards [] with ω
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hFb ω) (h.second_bound _ (htime i i.isLt.le) _) (abs_nonneg _) hH
    apply weighted_pathGradientResidual_integral (hVi T ⟨hT.le,le_rfl⟩) (hVi 0 ⟨le_rfl,hT.le⟩)
    · intro i
      simpa only [hWeq,mul_assoc] using
        brownian_predictable_increment_integrable hB hBm (hτ i) (hDm i) (hDi i)
    · intro i
      simpa only [hWeq,hτdiff,mul_assoc] using
        brownian_predictable_quadratic_integrable hB hBm (hτ i) (hD2m i) (hD2i i)
    · intro i
      simpa only [hWeq,mul_assoc] using brownian_predictable_increment_mean hB hBm (hτ i) (hDm i)
    · intro i
      simpa only [hWeq,hτdiff,mul_assoc] using
        brownian_predictable_quadratic_mean hB hBm (hτ i) (hD2m i)
  have hh : (∫ ω, F ω*u T (X T ω) ∂μ)-(∫ ω, F ω*u 0 (X 0 ω) ∂μ)=0 := by
    have hc : Tendsto (fun _ : ℕ ↦ (∫ ω, F ω*u T (X T ω) ∂μ)-
        (∫ ω, F ω*u 0 (X 0 ω) ∂μ)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [hmean] using hlim
    exact tendsto_nhds_unique tendsto_const_nhds hc
  exact sub_eq_zero.mp hh

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_Shift
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
open scoped Topology NNReal BigOperators

lemma GradientStripCore.shift {T K L a b : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStripCore T γ u K L) (ha : 0≤a) (hab : a≤b) (hb : b≤T) :
    GradientStripCore (b-a) (fun t ↦ γ (a+t)) (fun t ↦ u (a+t)) K L := by
  have hT : 0≤T := ha.trans (hab.trans hb)
  have hmem (t : ℝ) (ht : t∈Icc (0 : ℝ) (b-a)) : a+t∈Icc (0 : ℝ) T := by
    constructor <;> linarith [ht.1,ht.2]
  have ha' : a∈Icc (0 : ℝ) T := ⟨ha,hab.trans hb⟩
  have hb' : b∈Icc (0 : ℝ) T := ⟨ha.trans hab,hb⟩
  refine ⟨h.K_nonneg,h.L_nonneg,fun t ht ↦ h.gamma_nonneg _ (hmem t ht),?_,
    fun t ht ↦ h.smooth _ (hmem t ht),fun t ht ↦ h.bounded _ (hmem t ht),
    fun t ht ↦ h.second_bound _ (hmem t ht),fun t ht ↦ h.third_bound _ (hmem t ht),
    fun t ht ↦ h.product_bound _ (hmem t ht),?_,?_,?_,?_,?_⟩
  · intro s hs t ht hst
    exact h.gamma_mono (hmem s hs) (hmem t ht) (add_le_add le_rfl hst)
  · intro t ht s hs x y
    simpa only [add_sub_add_left_eq_sub] using h.second_lipschitz _ (hmem t ht) _ (hmem s hs) x y
  · intro t ht s hs x y
    simpa only [add_sub_add_left_eq_sub] using h.product_lipschitz _ (hmem t ht) _ (hmem s hs) x y
  · intro x
    have hi := intervalIntegrable_substrip hT (h.second_integrable x) ha' hb'
    simpa only [sub_self] using hi.comp_add_left a
  · intro x
    have hi := intervalIntegrable_substrip hT (h.product_integrable x) ha' hb'
    simpa only [sub_self] using hi.comp_add_left a
  · intro t ht s hs x
    rw [intervalIntegral.integral_comp_add_left
      (fun r ↦ (1/2 : ℝ)*deriv (deriv (u r)) x+γ r*(u r x*deriv (u r) x)) a]
    exact h.pde _ (hmem t ht) _ (hmem s hs) x

lemma diffusion_gradient_condExp_local
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) (a : ℝ≥0)
    {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hLu : 0≤Lu)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T,
      StronglyMeasurable[Filtration.natural B hBm (a+t.toNNReal)] (X t))
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hW : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ ω,
      W t ω-W s ω=B (a+t.toNNReal) ω-B (a+s.toNNReal) ω)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) :
    μ[(fun ω ↦ u T (X T ω)) | Filtration.natural B hBm a]=ᵐ[μ](fun ω ↦ u 0 (X 0 ω)) := by
  let ℱ := Filtration.natural B hBm
  have hm (t : ℝ) (ht : t∈Icc (0 : ℝ) T) :
      StronglyMeasurable[ℱ (a+t.toNNReal)] (fun ω ↦ u t (X t ω)) :=
    (h.smooth t ht).continuous.comp_stronglyMeasurable (hXM t ht)
  have hi (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : Integrable (fun ω ↦ u t (X t ω)) μ := by
    apply Integrable.of_bound ((hm t ht).mono (ℱ.le _)).aestronglyMeasurable 1
    filter_upwards [] with ω
    exact (Real.norm_eq_abs _).trans_le (h.bounded t ht _)
  have h0m : StronglyMeasurable[ℱ a] (fun ω ↦ u 0 (X 0 ω)) := by
    have hh := hm 0 ⟨le_rfl,hT.le⟩
    rw [Real.toNNReal_zero,add_zero] at hh
    exact hh
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le a) (hi T ⟨hT.le,le_rfl⟩)
    (fun s _ _ ↦ (hi 0 ⟨le_rfl,hT.le⟩).integrableOn) _ h0m.aestronglyMeasurable
  intro s hs _
  have hF : StronglyMeasurable[ℱ a] (s.indicator (fun _ : Ω ↦ (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hs
  have hFb (ω : Ω) : |s.indicator (fun _ : Ω ↦ (1 : ℝ)) ω|≤1 := by
    by_cases hω : ω∈s <;> simp [hω]
  have heq := diffusion_gradient_weak_martingale_local hB hBm a hT hT1 hLu (by norm_num : (0:ℝ)≤1)
    h hLip hXM hWM hW hpaths hF hFb
  have hprod (t : ℝ) : (fun ω ↦ s.indicator (fun _ : Ω ↦ (1 : ℝ)) ω*u t (X t ω))=
      s.indicator (fun ω ↦ u t (X t ω)) := by
    funext ω
    by_cases hω : ω∈s <;> simp [hω]
  rw [hprod T,hprod 0,integral_indicator (ℱ.le a s hs),integral_indicator (ℱ.le a s hs)] at heq
  exact heq.symm

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_DiffusionGradientCondExp
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
open scoped Topology NNReal BigOperators

lemma diffusion_gradient_condExp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X : ℝ → Ω → ℝ}
    (hT1 : T≤1) (hLu : 0≤Lu) (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T,
      StronglyMeasurable[Filtration.natural B hBm t.toNNReal] (X t))
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=B t.toNNReal ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω))
    {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) (hab : a≤b) :
    μ[(fun ω ↦ u b (X b ω)) | Filtration.natural B hBm a.toNNReal]=ᵐ[μ](fun ω ↦ u a (X a ω)) := by
  let ℱ := Filtration.natural B hBm
  by_cases heq : a=b
  · subst b
    have hh := (h.smooth a ha).continuous.comp_stronglyMeasurable (hXM a ha)
    apply condExp_of_aestronglyMeasurable' (ℱ.le _) hh.aestronglyMeasurable
    exact Integrable.of_bound (hh.mono (ℱ.le _)).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (h.bounded a ha _)))
  have hlt : a<b := lt_of_le_of_ne hab heq
  have hba : 0<b-a := sub_pos.mpr hlt
  have hba1 : b-a≤1 := by linarith [hb.2,ha.1]
  let Y := fun t : ℝ ↦ X (a+t)
  let W := fun t : ℝ ↦ fun ω ↦ X a ω+B (a.toNNReal+t.toNNReal) ω-B a.toNNReal ω
  have hmem (t : ℝ) (ht : t∈Icc (0 : ℝ) (b-a)) : a+t∈Icc (0 : ℝ) T := by
    constructor <;> linarith [ha.1,hb.2,ht.1,ht.2]
  have hLip' : ∀ s∈Icc (0 : ℝ) (b-a), ∀ t∈Icc (0 : ℝ) (b-a), ∀ x y,
      |u (a+s) x-u (a+t) y|≤Lu*(|s-t|+|x-y|) := by
    intro s hs t ht x y
    simpa only [add_sub_add_left_eq_sub] using hLip _ (hmem s hs) _ (hmem t ht) x y
  have hYM (t : ℝ) (ht : t∈Icc (0 : ℝ) (b-a)) :
      StronglyMeasurable[ℱ (a.toNNReal+t.toNNReal)] (Y t) := by
    have hh := hXM _ (hmem t ht)
    rw [Real.toNNReal_add ha.1 ht.1] at hh
    exact hh
  have hWM (t : ℝ) (_ht : t∈Icc (0 : ℝ) (b-a)) : AEStronglyMeasurable (W t) μ :=
    ((((hXM a ha).mono (ℱ.le _)).add (hBm _)).sub (hBm _)).aestronglyMeasurable
  have hW : ∀ s∈Icc (0 : ℝ) (b-a), ∀ t∈Icc (0 : ℝ) (b-a), ∀ ω,
      W t ω-W s ω=B (a.toNNReal+t.toNNReal) ω-B (a.toNNReal+s.toNNReal) ω := by
    intro s _ t _ ω
    dsimp [W]
    ring
  have hpaths' : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y t ω) (Icc (0 : ℝ) (b-a)) ∧
      IntervalIntegrable (fun s ↦ γ (a+s)*u (a+s) (Y s ω)) volume 0 (b-a) ∧
      ∀ t∈Icc (0 : ℝ) (b-a), Y t ω=W t ω+∫ s in (0 : ℝ)..t, γ (a+s)*u (a+s) (Y s ω) := by
    filter_upwards [hpaths] with ω hω
    have hT : 0≤T := ha.1.trans ha.2
    have hi := intervalIntegrable_substrip hT hω.2.1 ha hb
    refine ⟨hω.1.comp (continuous_const.add continuous_id).continuousOn hmem,?_,?_⟩
    · simpa only [sub_self,Y] using hi.comp_add_left a
    · intro t ht
      have hhalf := intervalIntegrable_substrip hT hω.2.1 ha (hmem t ht)
      have hleft := intervalIntegrable_substrip hT hω.2.1 ⟨le_rfl,hT⟩ ha
      have hsum := intervalIntegral.integral_add_adjacent_intervals hleft hhalf
      dsimp only [Y,W]
      rw [intervalIntegral.integral_comp_add_left (fun s ↦ γ s*u s (X s ω)) a,add_zero]
      rw [hω.2.2 _ (hmem t ht),hω.2.2 _ ha,Real.toNNReal_add ha.1 ht.1]
      linarith
  have hh := diffusion_gradient_condExp_local hB hBm a.toNNReal hba hba1 hLu
    (h.shift ha.1 hab hb.2) hLip' hYM hWM hW hpaths'
  simpa only [Y,add_sub_cancel,add_zero] using hh

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_UnitMomentMartingale
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

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {ℱ : Filtration ℝ m} {f : ℝ → Ω → ℝ}

lemma UnitMomentMartingale.integrable (h : UnitMomentMartingale (μ := μ) ℱ f)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : Integrable (f t) μ :=
  Integrable.of_bound ((h.measurable t ht).mono (ℱ.le t)).aestronglyMeasurable 1
    (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (h.bounded t ht ω)))

lemma UnitMomentMartingale.integrable_mul (h : UnitMomentMartingale (μ := μ) ℱ f)
    {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    Integrable (fun ω ↦ f s ω * f t ω) μ :=
  Integrable.of_bound (((h.measurable s hs).mono (ℱ.le s)).mul
    ((h.measurable t ht).mono (ℱ.le t))).aestronglyMeasurable 1
    (Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs,abs_mul]
      nlinarith [h.bounded s hs ω,h.bounded t ht ω,abs_nonneg (f s ω),abs_nonneg (f t ω)]))

lemma UnitMomentMartingale.integral_past_mul (h : UnitMomentMartingale (μ := μ) ℱ f)
    {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) (hst : s ≤ t) :
    ∫ ω, f s ω * f t ω ∂μ = s := by
  have hc := condExp_mul_of_stronglyMeasurable_left (h.measurable s hs)
    (h.integrable_mul hs ht) (h.integrable ht)
  have he : μ[(f s) * (f t) | ℱ s] =ᵐ[μ] fun ω ↦ (f s ω)^2 := by
    filter_upwards [hc,h.condExp s hs t ht hst] with ω hω hω'
    simpa only [Pi.mul_apply,hω',pow_two] using hω
  calc
    _ = ∫ ω, μ[(f s) * (f t) | ℱ s] ω ∂μ := (integral_condExp (ℱ.le s)).symm
    _ = ∫ ω, (f s ω)^2 ∂μ := integral_congr_ae he
    _ = s := h.secondMoment s hs

lemma UnitMomentMartingale.sampled_gap_martingale
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (r : ℕ → ℝ) (hr : Monotone r)
    (hrmem : ∀ n, r n ∈ Ico s 1) :
    Martingale (fun n ω ↦ 1-f s ω*f (r n) ω)
      (⟨fun n ↦ ℱ (r n),fun _ _ hij ↦ ℱ.mono (hr hij),fun n ↦ ℱ.le (r n)⟩ :
        Filtration ℕ m) μ := by
  have ht (n : ℕ) : r n ∈ Ico (0 : ℝ) 1 := ⟨hs.1.trans (hrmem n).1,(hrmem n).2⟩
  refine ⟨fun n ↦ stronglyMeasurable_const.sub
    (((h.measurable s hs).mono (ℱ.mono (hrmem n).1)).mul (h.measurable (r n) (ht n))),?_⟩
  intro i j hij
  have hc := condExp_mul_of_stronglyMeasurable_left
    ((h.measurable s hs).mono (ℱ.mono (hrmem i).1))
    (h.integrable_mul hs (ht j)) (h.integrable (ht j))
  have hc1 := condExp_of_stronglyMeasurable (ℱ.le (r i))
    (stronglyMeasurable_const (b := (1 : ℝ))) (integrable_const (μ := μ) 1)
  filter_upwards [condExp_sub (integrable_const (1 : ℝ))
      (h.integrable_mul hs (ht j)) (ℱ (r i)),hc,
      h.condExp (r i) (ht i) (r j) (ht j) (hr hij)] with ω hsub hmul he
  simp only [Pi.sub_apply] at hsub
  change μ[(fun ω ↦ f s ω*f (r j) ω) | ℱ (r i)] ω =
    f s ω*μ[f (r j) | ℱ (r i)] ω at hmul
  rw [hc1,hmul] at hsub
  simpa only [Pi.sub_def,Pi.mul_def,Pi.mul_apply,he] using hsub

omit [IsProbabilityMeasure μ] in
lemma UnitMomentMartingale.sampled_gap_nonneg
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) (ω : Ω) :
    0 ≤ 1-f s ω*f t ω := by
  have hh : f s ω*f t ω ≤ 1 := calc
    _ ≤ |f s ω*f t ω| := le_abs_self _
    _ = |f s ω| * |f t ω| := abs_mul _ _
    _ ≤ 1 := by nlinarith [h.bounded s hs ω,h.bounded t ht ω,
      abs_nonneg (f s ω),abs_nonneg (f t ω)]
  linarith

lemma UnitMomentMartingale.sampled_gap_integral
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) (hst : s ≤ t) :
    ∫ ω, 1-f s ω*f t ω ∂μ = 1-s := by
  rw [integral_sub (integrable_const 1) (h.integrable_mul hs ht),
    h.integral_past_mul hs ht hst]
  simp

lemma UnitMomentMartingale.finite_gap_maximal
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (S : Finset ℝ)
    (hS : ∀ t ∈ S, t ∈ Ico s 1) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * μ {ω | ∃ t ∈ S, (ε : ℝ) ≤ 1-f s ω*f t ω} ≤
      ENNReal.ofReal (1-s) := by
  classical
  by_cases hne : S.Nonempty
  · have hcard : 0 < S.card := Finset.card_pos.mpr hne
    let e := S.orderEmbOfFin rfl
    let r : ℕ → ℝ := fun n ↦ e ⟨min n (S.card-1),by omega⟩
    have hr : Monotone r := by
      intro i j hij
      exact e.monotone (show min i (S.card-1) ≤ min j (S.card-1) from min_le_min_right _ hij)
    have hrmem (n : ℕ) : r n ∈ Ico s 1 := hS _ (S.orderEmbOfFin_mem rfl _)
    have hm := h.sampled_gap_martingale hs r hr hrmem
    have hn : 0 ≤ (fun n ω ↦ 1-f s ω*f (r n) ω) :=
      fun n ω ↦ h.sampled_gap_nonneg hs ⟨hs.1.trans (hrmem n).1,(hrmem n).2⟩ ω
    have hb := maximal_ineq hm.submartingale hn (ε := ε) (S.card-1)
    have hset : {ω | ∃ t ∈ S, (ε : ℝ) ≤ 1-f s ω*f t ω} ⊆
        {ω | (ε : ℝ) ≤ (Finset.range ((S.card-1)+1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ 1-f s ω*f (r k) ω)} := by
      rintro ω ⟨t,ht,heps⟩
      let i := (S.orderIsoOfFin rfl).symm ⟨t,ht⟩
      have her : r i.val = t := by
        dsimp only [r]
        have hh : (⟨min i.val (S.card-1),by omega⟩ : Fin S.card) = i :=
          Fin.ext (min_eq_left (by omega))
        rw [hh]
        change ((S.orderIsoOfFin rfl) i).val = t
        simp [i]
      refine heps.trans ?_
      rw [← her]
      exact Finset.le_sup' (f := fun k ↦ 1-f s ω*f (r k) ω)
        (Finset.mem_range.mpr (by omega : i.val < (S.card-1)+1))
    calc
      _ ≤ (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤
          (Finset.range ((S.card-1)+1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ 1-f s ω*f (r k) ω)} := by gcongr
      _ ≤ _ := hb
      _ ≤ ENNReal.ofReal (∫ ω, 1-f s ω*f (r (S.card-1)) ω ∂μ) := by
        apply ENNReal.ofReal_le_ofReal
        exact setIntegral_le_integral (integrable_const 1 |>.sub
          (h.integrable_mul hs ⟨hs.1.trans (hrmem _).1,(hrmem _).2⟩))
          (Eventually.of_forall (hn (S.card-1)))
      _ = _ := congrArg ENNReal.ofReal (h.sampled_gap_integral hs
        ⟨hs.1.trans (hrmem _).1,(hrmem _).2⟩ (hrmem _).1)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

lemma UnitMomentMartingale.rational_gap_maximal
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * μ {ω | ∃ q : ℚ, (q : ℝ) ∈ Ico s 1 ∧
      (ε : ℝ) ≤ 1-f s ω*f q ω} ≤ ENNReal.ofReal (1-s) := by
  classical
  let E : Finset ℚ → Set Ω := fun S ↦ {ω | ∃ q ∈ S, (q : ℝ) ∈ Ico s 1 ∧
    (ε : ℝ) ≤ 1-f s ω*f q ω}
  have hd : Directed (· ⊆ ·) E := by
    intro S T
    refine ⟨S∪T, ?_, ?_⟩
    · rintro ω ⟨q,hq,hmem,he⟩
      exact ⟨q,Finset.mem_union_left _ hq,hmem,he⟩
    · rintro ω ⟨q,hq,hmem,he⟩
      exact ⟨q,Finset.mem_union_right _ hq,hmem,he⟩
  have heq : {ω | ∃ q : ℚ, (q : ℝ) ∈ Ico s 1 ∧ (ε : ℝ) ≤ 1-f s ω*f q ω} =
      ⋃ S : Finset ℚ, E S := by
    ext ω
    constructor
    · rintro ⟨q,hmem,he⟩
      exact mem_iUnion.mpr ⟨{q},q,Finset.mem_singleton_self _,hmem,he⟩
    · intro hω
      obtain ⟨S,q,hq,hmem,he⟩ := mem_iUnion.mp hω
      exact ⟨q,hmem,he⟩
  rw [heq,hd.measure_iUnion,ENNReal.mul_iSup]
  refine iSup_le fun S ↦ ?_
  let R : Finset ℝ := (S.filter (fun q : ℚ ↦ (q : ℝ) ∈ Ico s 1)).image (fun q : ℚ ↦ (q : ℝ))
  have hR : ∀ t ∈ R, t ∈ Ico s 1 := by
    intro t ht
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hq).2
  have hE : E S ⊆ {ω | ∃ t ∈ R, (ε : ℝ) ≤ 1-f s ω*f t ω} := by
    rintro ω ⟨q,hq,hmem,he⟩
    exact ⟨(q : ℝ),Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hmem⟩,rfl⟩,he⟩
  calc
    _ ≤ (ε : ℝ≥0∞) * μ {ω | ∃ t ∈ R, (ε : ℝ) ≤ 1-f s ω*f t ω} := by gcongr
    _ ≤ _ := h.finite_gap_maximal hs R hR ε

lemma terminalTime_mem (n : ℕ) : terminalTime n ∈ Ico (0 : ℝ) 1 := by
  have hn : (1 : ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : (0 : ℝ) < n+1 := by positivity
  simp only [terminalTime]
  constructor
  · have hh : (1 : ℝ)/(n+1) ≤ 1 := (div_le_one hp).mpr hn
    linarith
  · have hh : (0 : ℝ) < 1/(n+1) := by positivity
    linarith

lemma terminalTime_monotone : Monotone terminalTime := by
  intro i j hij
  simp only [terminalTime]
  have hh : (1 : ℝ)/(j+1) ≤ 1/(i+1) := one_div_le_one_div_of_le
    (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  linarith

lemma terminalTime_tendsto : Tendsto terminalTime atTop (𝓝[<] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall (fun n ↦ (terminalTime_mem n).2)⟩
  change Tendsto (fun n : ℕ ↦ (1 : ℝ)-1/((n : ℝ)+1)) atTop (𝓝 (1 : ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma UnitMomentMartingale.ae_exists_rational_gap_bound
    (h : UnitMomentMartingale (μ := μ) ℱ f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∃ n, ∀ q : ℚ, (q : ℝ) ∈ Ico (terminalTime n) 1 →
      1-f (terminalTime n) ω*f q ω < ε := by
  let E : ℕ → Set Ω := fun n ↦ {ω | ∃ q : ℚ, (q : ℝ) ∈ Ico (terminalTime n) 1 ∧
    ε ≤ 1-f (terminalTime n) ω*f q ω}
  have hbound (n : ℕ) : ENNReal.ofReal ε * μ (⋂ n, E n) ≤
      ENNReal.ofReal (1-terminalTime n) := calc
    _ ≤ ENNReal.ofReal ε * μ (E n) := by gcongr; exact iInter_subset E n
    _ ≤ _ := by
      have hh := h.rational_gap_maximal (terminalTime_mem n) (NNReal.mk ε hε.le)
      simpa only [E,NNReal.coe_mk,ENNReal.coe_nnreal_eq] using hh
  have hzero : ENNReal.ofReal ε * μ (⋂ n, E n) = 0 := by
    apply le_antisymm _ bot_le
    have hlim : Tendsto (fun n ↦ ENNReal.ofReal (1-terminalTime n)) atTop (𝓝 0) := by
      have hh : Tendsto (fun n ↦ 1-terminalTime n) atTop (𝓝 (0 : ℝ)) := by
        simpa only [sub_self] using ((tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_nhdsWithin_iff.mp terminalTime_tendsto).1)
      simpa only [ENNReal.ofReal_zero,Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
    exact ge_of_tendsto' hlim hbound
  have hn : μ (⋂ n, E n) = 0 := (mul_eq_zero.mp hzero).resolve_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have ha : ∀ᵐ ω ∂μ, ω ∉ ⋂ n, E n := by
    rw [ae_iff]
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    simp only [not_not,Set.ofPred_mem_eq]
  filter_upwards [ha] with ω hω
  simp only [mem_iInter,E,mem_ofPred_eq,not_forall,not_exists,not_and,not_le] at hω
  exact hω

lemma continuous_gap_bound_of_rat {v : ℝ → ℝ}
    (hv : ContinuousOn v (Ico (0 : ℝ) 1)) {s ε : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1)
    (hq : ∀ q : ℚ, (q : ℝ) ∈ Ico s 1 → 1-v s*v q < ε) :
    ∀ t ∈ Ioo s 1, 1-v s*v t ≤ ε := by
  intro t ht
  by_contra! he
  have hvt : ContinuousAt v t := (hv t ⟨hs.1.trans ht.1.le,ht.2⟩).continuousAt
    (Ico_mem_nhds_iff.mpr ⟨hs.1.trans_lt ht.1,ht.2⟩)
  have hgt : ContinuousAt (fun r ↦ 1-v s*v r) t := continuousAt_const.sub
    (continuousAt_const.mul hvt)
  have hevent : {r | ε < 1-v s*v r} ∈ 𝓝 t := hgt (Ioi_mem_nhds he)
  obtain ⟨q,hq'⟩ := Rat.denseRange_cast.mem_nhds (inter_mem hevent (Ioo_mem_nhds ht.1 ht.2))
  exact (hq q ⟨hq'.2.1.le,hq'.2.2⟩).not_gt hq'.1

lemma UnitMomentMartingale.exists_sequence_terminal
    (h : UnitMomentMartingale (μ := μ) ℱ f) :
    ∃ U : Ω → ℝ, StronglyMeasurable[ℱ 1] U ∧
      (∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
        Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω))) := by
  let 𝒢 : Filtration ℕ m := ⟨fun n ↦ ℱ (terminalTime n),
    fun _ _ hij ↦ ℱ.mono (terminalTime_monotone hij),fun n ↦ ℱ.le _⟩
  have hm : Martingale (fun n ↦ f (terminalTime n)) 𝒢 μ :=
    ⟨fun n ↦ h.measurable _ (terminalTime_mem n),fun i j hij ↦
      h.condExp _ (terminalTime_mem i) _ (terminalTime_mem j) (terminalTime_monotone hij)⟩
  have hb (n : ℕ) : eLpNorm (f (terminalTime n)) 1 μ ≤ (1 : ℝ≥0) := by
    have hh := eLpNorm_le_of_ae_bound (μ := μ) (p := (1 : ℝ≥0∞))
      (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le
        (h.bounded _ (terminalTime_mem n) ω)))
    simpa using hh
  let U := 𝒢.limitProcess (fun n ↦ f (terminalTime n)) μ
  have hU : StronglyMeasurable[ℱ 1] U :=
    Filtration.stronglyMeasurable_limitProcess.mono (iSup_le fun n ↦ ℱ.mono (terminalTime_mem n).2.le)
  refine ⟨U,hU,?_⟩
  filter_upwards [hm.submartingale.ae_tendsto_limitProcess hb] with ω hω
  exact ⟨le_of_tendsto' hω.abs (fun n ↦ h.bounded _ (terminalTime_mem n) ω),hω⟩

lemma UnitMomentMartingale.exists_continuous_terminal
    (h : UnitMomentMartingale (μ := μ) ℱ f)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Ico (0 : ℝ) 1)) :
    ∃ U : Ω → ℝ, StronglyMeasurable[ℱ 1] U ∧
      (∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
        Tendsto (fun t ↦ f t ω) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) := by
  obtain ⟨U,hU,hseq⟩ := h.exists_sequence_terminal
  have hg : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ n, ∀ q : ℚ,
      (q : ℝ) ∈ Ico (terminalTime n) 1 →
        1-f (terminalTime n) ω*f q ω < 1/(k+1) := by
    apply ae_all_iff.mpr
    intro k
    exact h.ae_exists_rational_gap_bound (by positivity)
  refine ⟨U,hU,?_⟩
  filter_upwards [hc,hseq,hg] with ω hcont hseqω hgap
  refine ⟨hseqω.1,Metric.tendsto_nhds.mpr (fun δ hδ ↦ ?_)⟩
  obtain ⟨k,hk⟩ : ∃ k : ℕ, (1 : ℝ)/(k+1) < δ^2/32 := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds (show (0 : ℝ) < δ^2/32 by positivity))
    exact hh.exists
  obtain ⟨n,hn⟩ := hgap k
  have hreal := continuous_gap_bound_of_rat hcont (terminalTime_mem n) hn
  have hbound (t : ℝ) (ht : t ∈ Ioo (terminalTime n) 1) :
      |f t ω-f (terminalTime n) ω| ≤ δ/4 := by
    have hbt := h.bounded t ⟨(terminalTime_mem n).1.trans ht.1.le,ht.2⟩ ω
    have hbs := h.bounded _ (terminalTime_mem n) ω
    have he := hreal t ht
    have hsq1 : (f t ω)^2 ≤ 1 := by nlinarith [abs_le.mp hbt]
    have hsq2 : (f (terminalTime n) ω)^2 ≤ 1 := by nlinarith [abs_le.mp hbs]
    have habs : |f t ω-f (terminalTime n) ω|^2 < (δ/4)^2 := by
      rw [sq_abs]
      nlinarith
    nlinarith [abs_nonneg (f t ω-f (terminalTime n) ω)]
  have hUb : |U ω-f (terminalTime n) ω| ≤ δ/4 := by
    apply le_of_tendsto ((hseqω.2.sub_const _).abs)
    have hev : ∀ᶠ k in atTop, terminalTime k ∈ Ioo (terminalTime n) 1 :=
      terminalTime_tendsto.eventually (Ioo_mem_nhdsLT (terminalTime_mem n).2)
    exact hev.mono (fun k hk ↦ hbound _ hk)
  filter_upwards [Ioo_mem_nhdsLT (terminalTime_mem n).2] with t ht
  rw [Real.dist_eq]
  have hh := abs_add_le (f t ω-f (terminalTime n) ω) (f (terminalTime n) ω-U ω)
  have hh' := hbound t ht
  have hUb' : |f (terminalTime n) ω-U ω| ≤ δ/4 := by simpa only [abs_sub_comm] using hUb
  have heq : f t ω-U ω = (f t ω-f (terminalTime n) ω)+(f (terminalTime n) ω-U ω) := by ring
  rw [heq]
  linarith

lemma UnitMomentMartingale.terminal_square
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
      Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω))) :
    ∀ᵐ ω ∂μ, (U ω)^2 = 1 := by
  have hU2i : Integrable (fun ω ↦ (U ω)^2) μ :=
    Integrable.of_bound ((hUm.mono (ℱ.le 1)).pow 2).aestronglyMeasurable 1
      (hU.mono (fun ω hω ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        nlinarith [abs_le.mp hω.1]))
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω ↦ (f (terminalTime n) ω)^2) (fun _ : Ω ↦ (1 : ℝ))
    (fun n ↦ (((h.measurable _ (terminalTime_mem n)).mono (ℱ.le _)).pow 2).aestronglyMeasurable)
    (integrable_const 1)
    (fun n ↦ Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_le.mp (h.bounded _ (terminalTime_mem n) ω)]))
    (hU.mono (fun ω hω ↦ hω.2.pow 2))
  have hi : ∫ ω, (U ω)^2 ∂μ = 1 := by
    have hh : (fun n ↦ ∫ ω, (f (terminalTime n) ω)^2 ∂μ) = terminalTime :=
      funext (fun n ↦ h.secondMoment _ (terminalTime_mem n))
    rw [hh] at ht
    exact tendsto_nhds_unique ht (tendsto_nhdsWithin_iff.mp terminalTime_tendsto).1
  have hnonneg : 0 ≤ᵐ[μ] (fun ω ↦ 1-(U ω)^2) := hU.mono (fun ω hω ↦ by
    dsimp
    nlinarith [abs_le.mp hω.1])
  have hzero : ∫ ω, 1-(U ω)^2 ∂μ = 0 := by
    rw [integral_sub (integrable_const 1) hU2i,hi]
    simp
  have he := (integral_eq_zero_iff_of_nonneg_ae hnonneg ((integrable_const 1).sub hU2i)).mp hzero
  filter_upwards [he] with ω hω
  change 1-(U ω)^2=0 at hω
  linarith

lemma UnitMomentMartingale.terminal_mean_square
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
      Tendsto (fun t ↦ f t ω) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) :
    Tendsto (fun t ↦ ∫ ω, (f t ω-U ω)^2 ∂μ) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ico (0 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with t ht
    exact ⟨ht.1.le,ht.2⟩
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun t ω ↦ (f t ω-U ω)^2) (f := fun _ ↦ (0 : ℝ)) (fun _ : Ω ↦ (4 : ℝ))
    (hev.mono (fun t ht ↦ ((((h.measurable t ht).mono (ℱ.le t)).sub
      (hUm.mono (ℱ.le 1))).pow 2).aestronglyMeasurable))
    (hev.mono (fun t ht ↦ hU.mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb := h.bounded t ht ω
      have hd : |f t ω-U ω| ≤ 2 := (abs_sub _ _).trans (by linarith [hω.1])
      nlinarith [sq_abs (f t ω-U ω),abs_nonneg (f t ω-U ω)])))
    (integrable_const 4)
    (hU.mono (fun ω hω ↦ by
      simpa only [sub_self,zero_pow (by decide : (2 : ℕ) ≠ 0)] using (hω.2.sub_const (U ω)).pow 2))
  simpa only [integral_zero] using ht

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_TerminalCondExp
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
variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℝ m} {f : ℝ → Ω → ℝ}

lemma UnitMomentMartingale.terminal_condExp
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
      Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)))
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) : μ[U | ℱ s] =ᵐ[μ] f s := by
  have hUi : Integrable U μ := Integrable.of_bound (hUm.mono (ℱ.le _)).aestronglyMeasurable 1
    (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hUi
    (fun S _ _ ↦ (h.integrable hs).integrableOn) _ (h.measurable s hs).aestronglyMeasurable
  intro S hS _
  have hlim : Tendsto (fun n ↦ ∫ ω in S, f (terminalTime n) ω ∂μ) atTop (𝓝 (∫ ω in S, U ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ))
      (fun n ↦ ((h.measurable _ (terminalTime_mem n)).mono (ℱ.le _)).aestronglyMeasurable.restrict)
      (integrable_const 1)
      (fun n ↦ Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le
        (h.bounded _ (terminalTime_mem n) ω)))
      (ae_restrict_of_ae (hU.mono (fun _ hω ↦ hω.2)))
  have he : ∀ᶠ n in atTop, (∫ ω in S, f (terminalTime n) ω ∂μ) = ∫ ω in S, f s ω ∂μ := by
    have hsn : ∀ᶠ n in atTop, s ≤ terminalTime n :=
      ((tendsto_nhdsWithin_iff.mp terminalTime_tendsto).1.eventually (Ioi_mem_nhds hs.2)).mono
        (fun _ hn ↦ hn.le)
    filter_upwards [hsn] with n hn
    calc
      _ = ∫ ω in S, μ[f (terminalTime n) | ℱ s] ω ∂μ :=
        (setIntegral_condExp (ℱ.le s) (h.integrable (terminalTime_mem n)) hS).symm
      _ = _ := integral_congr_ae (ae_restrict_of_ae (h.condExp s hs _ (terminalTime_mem n) hn))
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)) hlim

lemma UnitMomentMartingale.terminal_stopped_martingale
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
      Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω))) :
    Martingale (fun t : ℝ≥0 ↦ fun ω ↦ if (t : ℝ)<1 then f t ω else U ω)
      (⟨fun t : ℝ≥0 ↦ ℱ t,fun _ _ hij ↦ ℱ.mono hij,fun t ↦ ℱ.le t⟩ :
        Filtration ℝ≥0 m) μ := by
  have hUi : Integrable U μ := Integrable.of_bound (hUm.mono (ℱ.le _)).aestronglyMeasurable 1
    (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  constructor
  · intro t
    by_cases ht : (t : ℝ)<1
    · simpa only [ht,ite_true,ite_false] using h.measurable t ⟨t.coe_nonneg,ht⟩
    · simpa only [ht,ite_true,ite_false] using hUm.mono (ℱ.mono (not_lt.mp ht))
  · intro s t hst
    by_cases hs : (s : ℝ)<1
    · by_cases ht : (t : ℝ)<1
      · simpa only [hs,ht,ite_true,ite_false] using
          h.condExp s ⟨s.coe_nonneg,hs⟩ t ⟨t.coe_nonneg,ht⟩ hst
      · simpa only [hs,ht,ite_true,ite_false] using h.terminal_condExp hUm hU ⟨s.coe_nonneg,hs⟩
    · have ht : ¬(t : ℝ)<1 := not_lt.mpr ((not_lt.mp hs).trans hst)
      have he := condExp_of_stronglyMeasurable (ℱ.le s)
        (hUm.mono (ℱ.mono (not_lt.mp hs))) hUi
      simpa only [hs,ht,ite_true,ite_false] using Filter.EventuallyEq.of_eq he

lemma UnitMomentMartingale.exists_terminal
    (h : UnitMomentMartingale (μ := μ) ℱ f)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Ico (0 : ℝ) 1)) :
    ∃ U : Ω → ℝ, StronglyMeasurable[ℱ 1] U ∧
      Martingale (fun t : ℝ≥0 ↦ fun ω ↦ if (t : ℝ)<1 then f t ω else U ω)
        (⟨fun t : ℝ≥0 ↦ ℱ t,fun _ _ hij ↦ ℱ.mono hij,fun t ↦ ℱ.le t⟩ :
          Filtration ℝ≥0 m) μ ∧
      (∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧ (U ω)^2=1 ∧
        Tendsto (fun t ↦ f t ω) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
      Tendsto (fun t ↦ ∫ ω, (f t ω-U ω)^2 ∂μ) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  obtain ⟨U,hUm,hU⟩ := h.exists_continuous_terminal hc
  have hseq : ∀ᵐ ω ∂μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)) :=
    hU.mono (fun ω hω ↦ ⟨hω.1,hω.2.comp terminalTime_tendsto⟩)
  refine ⟨U,hUm,h.terminal_stopped_martingale hUm hseq,?_,h.terminal_mean_square hUm hU⟩
  filter_upwards [hU,h.terminal_square hUm hseq] with ω hω hsq
  exact ⟨hω.1,hsq,hω.2⟩

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_RealFiltration
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

lemma IsDiffusion.natural_measurable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    StronglyMeasurable[W.filtration t.toNNReal] (X t) := by
  have hh := hX.1 t.toNNReal
  simpa only [Real.coe_toNNReal t ht.1,min_eq_left ht.2] using hh.stronglyMeasurable

lemma IsDiffusion.unitMomentMartingale {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hreg : ∀ T∈Ico (0 : ℝ) 1, ∃ K L Lu : ℝ, 0≤Lu ∧
      GradientStripCore T γ.coeff (gradient W γ) K L ∧
      ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|))
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)) := by
  constructor
  · intro t ht
    obtain ⟨K,L,Lu,hLu,hg,hLip⟩ := hreg t ht
    exact (hg.smooth t ⟨ht.1,le_rfl⟩).continuous.comp_stronglyMeasurable
      (hX.natural_measurable ⟨ht.1,ht.2.le⟩)
  · intro t ht ω
    obtain ⟨K,L,Lu,hLu,hg,hLip⟩ := hreg t ht
    exact hg.bounded t ⟨ht.1,le_rfl⟩ _
  · intro s hs t ht hst
    obtain ⟨K,L,Lu,hLu,hg,hLip⟩ := hreg t ht
    exact diffusion_gradient_condExp W.brownian.toIsPreBrownianReal W.measurable ht.2.le
      hLu hg hLip (fun r hr ↦ hX.natural_measurable ⟨hr.1,hr.2.trans ht.2.le⟩)
      ((hX.strip_paths ht.1 ht.2 hLu (fun a ha b hb x y ↦ hLip b hb a ha y x)).mono
        (fun _ hω ↦ ⟨hω.1,hω.2.1,hω.2.2.1⟩)) ⟨hs.1,hst⟩ ⟨ht.1,le_rfl⟩ hst
  · exact hmom

lemma IsDiffusion.gradient_continuous {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hreg : ∀ T∈Ico (0 : ℝ) 1, ∃ Lu : ℝ, 0≤Lu ∧
      ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|)) :
    ∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ gradient W γ t (X t ω)) (Ico (0 : ℝ) 1) := by
  filter_upwards [hX.2] with ω hω
  intro t ht
  obtain ⟨T,htT,hT1⟩ := exists_between ht.2
  have hT : T∈Ico (0 : ℝ) 1 := ⟨ht.1.trans htT.le,hT1⟩
  obtain ⟨Lu,hLu,hLip⟩ := hreg T hT
  have hj : ContinuousOn (fun p : ℝ×ℝ ↦ gradient W γ p.1 p.2)
      {p | p.1∈Icc (0 : ℝ) T} :=
    derivative_joint_continuous hLu hLip
  have hp : ContinuousOn (fun s ↦ (s,X s ω)) (Icc (0 : ℝ) T) :=
    continuousOn_id.prodMk (hω.1.mono (Icc_subset_Icc le_rfl hT1.le))
  have hc := ContinuousOn.comp (g := fun p : ℝ×ℝ ↦ gradient W γ p.1 p.2)
    (f := fun s ↦ (s,X s ω)) hj hp (fun s hs ↦ hs)
  apply (hc t ⟨ht.1,htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩

lemma IsDiffusion.exists_gradient_terminal {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hreg : ∀ T∈Ico (0 : ℝ) 1, ∃ K L Lu : ℝ, 0≤Lu ∧
      GradientStripCore T γ.coeff (gradient W γ) K L ∧
      ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|))
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    ∃ U : W.Ω → ℝ, StronglyMeasurable[W.filtration 1] U ∧
      Martingale (gradientStopped W γ X U) W.filtration W.μ ∧
      (∀ᵐ ω ∂W.μ, |U ω|≤1 ∧ (U ω)^2=1 ∧
        Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
      Tendsto (fun t ↦ ∫ ω, (gradient W γ t (X t ω)-U ω)^2 ∂W.μ)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hh := (hX.unitMomentMartingale hreg hmom).exists_terminal
    (hX.gradient_continuous (fun T hT ↦ by
      obtain ⟨K,L,Lu,hLu,hg,hLip⟩ := hreg T hT
      exact ⟨Lu,hLu,hLip⟩))
  have he : (⟨fun t : ℝ≥0 ↦ W.realFiltration t,
      fun _ _ hij ↦ W.realFiltration.mono hij,fun t ↦ W.realFiltration.le t⟩ :
      Filtration ℝ≥0 W.measurableSpace)=W.filtration := by
    ext : 1
    simp only [BrownianSpace.realFiltration,Real.toNNReal_coe]
  obtain ⟨U,hUm,hm,hU,hUt⟩ := hh
  refine ⟨U,?_,?_,hU,hUt⟩
  · change StronglyMeasurable[W.filtration ((1 : ℝ).toNNReal)] U at hUm
    have h1 : (1 : ℝ).toNNReal = (1 : ℝ≥0) := by norm_num
    rw [h1] at hUm
    exact hUm
  · change Martingale (gradientStopped W γ X U)
      (⟨fun t : ℝ≥0 ↦ W.realFiltration t,
        fun _ _ hij ↦ W.realFiltration.mono hij,fun t ↦ W.realFiltration.le t⟩ :
          Filtration ℝ≥0 W.measurableSpace) W.μ at hm
    rw [he] at hm
    exact hm

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

lemma joint_aestronglyMeasurable_of_ae_continuous
    {Ω I : Type*} [MeasurableSpace Ω] [TopologicalSpace I] [TopologicalSpace.MetrizableSpace I]
    [MeasurableSpace I] [SecondCountableTopology I] [OpensMeasurableSpace I]
    {μ : Measure Ω} {ν : Measure I} [SFinite μ] [SFinite ν]
    {f : I → Ω → ℝ} (hm : ∀ t, StronglyMeasurable (f t))
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ f t ω)) :
    AEStronglyMeasurable (Function.uncurry f) (ν.prod μ) := by
  classical
  obtain ⟨s,hsub,hsm,hs0⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  let g (t : I) (ω : Ω) : ℝ := if ω∈s then 0 else f t ω
  have hg : StronglyMeasurable (Function.uncurry g) := by
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    · intro ω
      by_cases hω : ω∈s
      · simpa only [g,ite_eq_left hω] using (continuous_const : Continuous (fun _ : I ↦ (0 : ℝ)))
      · have hh : Continuous (fun t ↦ f t ω) := by
          by_contra hh
          exact hω (hsub hh)
        simpa only [g,ite_eq_right hω] using hh
    · intro t
      exact StronglyMeasurable.ite hsm stronglyMeasurable_const (hm t)
  apply hg.aestronglyMeasurable.congr
  have hs : ∀ᵐ ω ∂μ, ω∉s := by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hs0
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hs] with p hp
  exact ite_eq_right hp

lemma compact_joint_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [SFinite μ] {f : ℝ → Ω → ℝ} {T : ℝ} (hT : 0≤T)
    (hm : ∀ t∈Icc (0 : ℝ) T, StronglyMeasurable (f t))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Icc (0 : ℝ) T)) :
    AEStronglyMeasurable (Function.uncurry f) ((volume.restrict (Ioc (0 : ℝ) T)).prod μ) := by
  let c : ℝ → ℝ := fun t ↦ (projIcc 0 T hT t : ℝ)
  have hcm (t : ℝ) : c t∈Icc (0 : ℝ) T := (projIcc 0 T hT t).2
  have hj : AEStronglyMeasurable (fun p : ℝ×Ω ↦ f (c p.1) p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ) :=
    joint_aestronglyMeasurable_of_ae_continuous (fun t ↦ hm _ (hcm t))
      (hc.mono (fun ω hω ↦ hω.comp_continuous (continuous_subtype_val.comp continuous_projIcc) hcm))
  apply hj.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem measurableSet_Ioc : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T), t∈Ioc (0 : ℝ) T)] with p hp
  simp only [c,projIcc_of_mem hT ⟨hp.1.le,hp.2⟩,Function.uncurry]

lemma compact_weighted_fubini {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℝ → Ω → ℝ} {U : Ω → ℝ}
    {γ : ℝ → ℝ} {T : ℝ} (hT : 0≤T)
    (hm : ∀ t∈Icc (0 : ℝ) T, StronglyMeasurable (f t))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Icc (0 : ℝ) T))
    (hb : ∀ t∈Icc (0 : ℝ) T, ∀ ω, |f t ω|≤1)
    (hUm : AEStronglyMeasurable U μ) (hUb : ∀ᵐ ω ∂μ, |U ω|≤1)
    (hγ : IntervalIntegrable γ volume 0 T) :
    (∫ ω, U ω*(∫ t in (0 : ℝ)..T, γ t*f t ω) ∂μ) =
      ∫ t in (0 : ℝ)..T, γ t*(∫ ω, U ω*f t ω ∂μ) := by
  have hγi : Integrable γ (volume.restrict (Ioc (0 : ℝ) T)) := hγ.1
  have hj := compact_joint_aestronglyMeasurable hT hm hc
  have ht : ∀ᵐ p : ℝ×Ω ∂(volume.restrict (Ioc (0 : ℝ) T)).prod μ,
      p.1∈Ioc (0 : ℝ) T := Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  have hu : ∀ᵐ p : ℝ×Ω ∂(volume.restrict (Ioc (0 : ℝ) T)).prod μ,
      |U p.2|≤1 := Measure.quasiMeasurePreserving_snd.ae hUb
  have hi : Integrable (fun p : ℝ×Ω ↦ γ p.1*(U p.2*f p.1 p.2))
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ) := by
    apply (hγi.abs.comp_fst μ).mono' (hγi.aestronglyMeasurable.comp_fst.mul (hUm.comp_snd.mul hj))
    filter_upwards [ht,hu] with p hp hUp
    change ‖γ p.1*(U p.2*f p.1 p.2)‖≤|γ p.1|
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    have hf := hb p.1 ⟨hp.1.le,hp.2⟩ p.2
    have huf : |U p.2| * |f p.1 p.2| ≤ 1 := by
      nlinarith [abs_nonneg (f p.1 p.2),abs_nonneg (U p.2)]
    exact (mul_le_mul_of_nonneg_left huf (abs_nonneg _)).trans_eq (mul_one _)
  simp only [intervalIntegral.integral_of_le hT]
  have he := integral_integral_swap (f := fun t ω ↦ γ t*(U ω*f t ω)) hi
  calc
    _ = ∫ ω, ∫ t in Ioc (0 : ℝ) T, γ t*(U ω*f t ω) ∂volume ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    _ = ∫ t in Ioc (0 : ℝ) T, ∫ ω, γ t*(U ω*f t ω) ∂μ := he.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact integral_const_mul _ _

lemma UnitMomentMartingale.terminal_past_product
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {f : ℝ → Ω → ℝ}
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω|≤1 ∧ Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)))
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) :
    (∫ ω, U ω*f t ω ∂μ)=t := by
  have hUi : Integrable U μ := Integrable.of_bound (hUm.mono (ℱ.le 1)).aestronglyMeasurable 1
    (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  have hprod : Integrable (fun ω ↦ f t ω*U ω) μ :=
    hUi.bdd_mul ((h.measurable t ht).mono (ℱ.le t)).aestronglyMeasurable
      (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (h.bounded t ht ω)))
  have hc := condExp_mul_of_stronglyMeasurable_left (h.measurable t ht) hprod hUi
  have he : μ[(f t)*U | ℱ t] =ᵐ[μ] (fun ω ↦ (f t ω)^2) := by
    filter_upwards [hc,h.terminal_condExp hUm hU ht] with ω hω hω'
    simpa only [Pi.mul_apply,hω',pow_two] using hω
  calc
    _ = ∫ ω, f t ω*U ω ∂μ := by congr 1; funext ω; ring
    _ = ∫ ω, μ[(f t)*U | ℱ t] ω ∂μ := (integral_condExp (ℱ.le t)).symm
    _ = ∫ ω, (f t ω)^2 ∂μ := integral_congr_ae he
    _ = t := h.secondMoment t ht

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_WeightedTerminalExpectation
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

lemma UnitMomentMartingale.weighted_terminal_expectation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {f : ℝ → Ω → ℝ}
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω|≤1 ∧ Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)))
    {γ : ℝ → ℝ} {T : ℝ} (hT : 0≤T) (hT1 : T<1)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Icc (0 : ℝ) T))
    (hγ : IntervalIntegrable γ volume 0 T) :
    (∫ ω, U ω*(∫ t in (0 : ℝ)..T, γ t*f t ω) ∂μ)=∫ t in (0 : ℝ)..T, t*γ t := by
  have hm (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : t∈Ico (0 : ℝ) 1 := ⟨ht.1,ht.2.trans_lt hT1⟩
  rw [compact_weighted_fubini hT (fun t ht ↦ (h.measurable t (hm t ht)).mono (ℱ.le t))
    hc (fun t ht ↦ h.bounded t (hm t ht)) (hUm.mono (ℱ.le 1)).aestronglyMeasurable
    (hU.mono (fun _ hω ↦ hω.1)) hγ]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  change γ t * (∫ ω, U ω * f t ω ∂μ) = t * γ t
  rw [h.terminal_past_product hUm hU (hm t ht),mul_comm]

lemma bounded_multiplier_integral_difference {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U X Y : Ω → ℝ}
    (hU : AEStronglyMeasurable U μ) (hb : ∀ᵐ ω ∂μ, |U ω|≤1)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    |(∫ ω, U ω*X ω ∂μ)-(∫ ω, U ω*Y ω ∂μ)|≤∫ ω, |X ω-Y ω| ∂μ := by
  have hUb : ∀ᵐ ω ∂μ, ‖U ω‖≤1 := hb.mono (fun ω hω ↦ by simpa only [Real.norm_eq_abs] using hω)
  have hUX := hX.bdd_mul hU hUb
  have hUY := hY.bdd_mul hU hUb
  rw [←integral_sub hUX hUY]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hUX.sub hUY).abs (hX.sub hY).abs
  filter_upwards [hb] with ω hω
  dsimp only [Pi.sub_apply]
  rw [←mul_sub,abs_mul]
  exact (mul_le_mul_of_nonneg_right hω (abs_nonneg _)).trans_eq (one_mul _)

lemma bounded_multiplier_integral_tendsto {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter I} {U : Ω → ℝ} {X : I → Ω → ℝ} {Y : Ω → ℝ}
    (hU : AEStronglyMeasurable U μ) (hb : ∀ᵐ ω ∂μ, |U ω|≤1)
    (hX : ∀ᶠ t in l, Integrable (X t) μ) (hY : Integrable Y μ)
    (hL1 : Tendsto (fun t ↦ ∫ ω, |X t ω-Y ω| ∂μ) l (𝓝 (0 : ℝ))) :
    Tendsto (fun t ↦ ∫ ω, U ω*X t ω ∂μ) l (𝓝 (∫ ω, U ω*Y ω ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_ hL1
  filter_upwards [hX] with t ht
  simpa only [Real.norm_eq_abs] using bounded_multiplier_integral_difference hU hb ht hY

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_L1Terminal
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
open scoped Topology NNReal

lemma BrownianSpace.L1_terminal (W : BrownianSpace) :
    Tendsto (fun t : ℝ ↦ ∫ ω, |W.B t.toNNReal ω-W.B 1 ω| ∂W.μ)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun t : ℝ ↦ (1 : ℝ)-t) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun t : ℝ ↦ (1 : ℝ)-t) (𝓝[<] (1 : ℝ)) (𝓝 (1-1)))
  have hs : Tendsto (fun t : ℝ ↦ Real.sqrt (1-t)) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hi
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))) ?_ hs
  filter_upwards [eventually_time_mem] with t ht
  simpa only [abs_sub_comm] using brownian_increment_abs_bound W ht

lemma IsDiffusion.terminal_compact_product {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
    {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
    (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω)))
    {T : ℝ} (hT : 0≤T) (hT1 : T<1)
    (hc : ∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ gradient W γ t (X t ω)) (Icc (0 : ℝ) T)) :
    (∫ ω, U ω*X T ω ∂W.μ)=(∫ ω, U ω*W.B T.toNNReal ω ∂W.μ)+
      ∫ t in (0 : ℝ)..T, t*γ.coeff t := by
  have hUb : ∀ᵐ ω ∂W.μ, ‖U ω‖≤1 :=
    hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1)
  have hUs : AEStronglyMeasurable U W.μ := (hUm.mono (W.realFiltration.le 1)).aestronglyMeasurable
  have hXi := (hX.memLp ⟨hT,hT1.le⟩ (p := 1) (by norm_num)).integrable le_rfl
  have hBi := ((W.brownian.hasLaw_eval T.toNNReal).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl
  have hγ := γ.intervalIntegrable.mono_set (show uIcc (0 : ℝ) T⊆uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hT,uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact Icc_subset_Icc le_rfl hT1.le)
  have hd : (fun ω ↦ U ω*(∫ s in (0 : ℝ)..T, γ.coeff s*gradient W γ s (X s ω))) =ᵐ[W.μ]
      (fun ω ↦ U ω*(X T ω-W.B T.toNNReal ω)) := by
    filter_upwards [hX.2] with ω hω
    rw [hω.2 T ⟨hT,hT1.le⟩,add_sub_cancel_left]
  have hi := ((hXi.sub hBi).bdd_mul hUs hUb).congr hd.symm
  calc
    _ = ∫ ω, U ω*W.B T.toNNReal ω+
          U ω*(∫ s in (0 : ℝ)..T, γ.coeff s*gradient W γ s (X s ω)) ∂W.μ := by
      apply integral_congr_ae
      filter_upwards [hX.2] with ω hω
      rw [hω.2 T ⟨hT,hT1.le⟩,mul_add]
    _ = _ := by
      rw [integral_add (hBi.bdd_mul hUs hUb) hi,
        hm.weighted_terminal_expectation hUm hU hT hT1 hc hγ]

lemma IsDiffusion.terminal_product_value {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hm : UnitMomentMartingale (μ := W.μ) W.realFiltration (fun t ω ↦ gradient W γ t (X t ω)))
    {U : W.Ω → ℝ} (hUm : StronglyMeasurable[W.realFiltration 1] U)
    (hU : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω)))
    (hc : ∀ᵐ ω ∂W.μ, ContinuousOn (fun t ↦ gradient W γ t (X t ω)) (Ico (0 : ℝ) 1)) :
    (∫ ω, U ω*X 1 ω ∂W.μ)=(∫ ω, U ω*W.B 1 ω ∂W.μ)+
      ∫ t in (0 : ℝ)..1, t*γ.coeff t := by
  have hUs : AEStronglyMeasurable U W.μ := (hUm.mono (W.realFiltration.le 1)).aestronglyMeasurable
  have hUb := hU.mono (fun _ hω ↦ hω.1)
  have hXlim := bounded_multiplier_integral_tendsto hUs hUb
    (eventually_time_mem.mono (fun t ht ↦ (hX.memLp ht (p := 1) (by norm_num)).integrable le_rfl))
    ((hX.memLp (by norm_num : (1 : ℝ)∈Icc (0 : ℝ) 1) (p := 1) (by norm_num)).integrable le_rfl)
    hX.L1_terminal
  have hBlim := bounded_multiplier_integral_tendsto hUs hUb
    (Eventually.of_forall (fun t : ℝ ↦ ((W.brownian.hasLaw_eval t.toNNReal).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl))
    (((W.brownian.hasLaw_eval 1).hasGaussianLaw.memLp (p := 1) (by norm_num)).integrable le_rfl) W.L1_terminal
  have he : (fun T ↦ ∫ ω, U ω*X T ω ∂W.μ) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun T ↦ (∫ ω, U ω*W.B T.toNNReal ω ∂W.μ)+∫ t in (0 : ℝ)..T, t*γ.coeff t) := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
    exact hX.terminal_compact_product hm hUm hU hT.1.le hT.2
      (hc.mono (fun _ hω ↦ hω.mono (fun _ ht ↦ ⟨ht.1,ht.2.trans_lt hT.2⟩)))
  exact tendsto_nhds_unique hXlim ((hBlim.add γ.time_weighted_terminal).congr' he.symm)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_MeanDerivativeContinuous
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

lemma mean_derivative_continuous {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℝ → Ω → ℝ} {T D La : ℝ} {u : ℝ → ℝ → ℝ}
    (hLa : 0≤La)
    (hd : ∀ t∈Icc (0 : ℝ) T, Continuous (deriv (u t)))
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hXC : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T)) :
    ContinuousOn (fun t ↦ ∫ ω, deriv (u t) (X t ω) ∂μ) (Icc (0 : ℝ) T) := by
  have hj : ContinuousOn (fun p : ℝ×ℝ ↦ deriv (u p.1) p.2)
      {p | p.1∈Icc (0 : ℝ) T} := by
    apply (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (2*La)) ?_).continuousOn
    intro p hp q hq
    rw [Real.coe_toNNReal _ (by positivity), Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    calc
      _ ≤ La*(|p.1-q.1|+|p.2-q.2|) := hLip p.1 hp q.1 hq p.2 q.2
      _ ≤ _ := by
        have h₁ := le_max_left |p.1-q.1| |p.2-q.2|
        have h₂ := le_max_right |p.1-q.1| |p.2-q.2|
        nlinarith
  apply continuousOn_of_dominated (bound := fun _ ↦ D)
  · intro t ht
    exact ((hd t ht).measurable.comp_aemeasurable (hXM t ht).aemeasurable).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using hD t ht (X t ω))
  · exact integrable_const D
  · filter_upwards [hXC] with ω hω
    exact hj.comp (continuousOn_id.prodMk hω) (fun t ht ↦ ht)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_StripRegularity
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
open scoped Topology NNReal

lemma SourceStripRegularity.core {W : BrownianSpace} {γ : OrderParameter}
    (h : SourceStripRegularity W γ) :
    ∀ T∈Ico (0 : ℝ) 1, ∃ K L Lu : ℝ, 0≤Lu ∧
      GradientStripCore T γ.coeff (gradient W γ) K L ∧
      ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
        |gradient W γ s x-gradient W γ t y|≤Lu*(|s-t|+|x-y|) := by
  intro T hT
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := h T hT
  exact ⟨K,L,Lu,hLu,hG.toCore,hu⟩

lemma IsDiffusion.curvature_mean_continuous {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ) :
    ContinuousOn (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) (Ico (0 : ℝ) 1) := by
  intro t ht
  obtain ⟨T,htT,hT1⟩ := exists_between ht.2
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨ht.1.trans htT.le,hT1⟩
  have hc := mean_derivative_continuous hLa
    (fun s hs ↦ (hG.smooth s hs).continuous_deriv (by norm_num)) hDb ha
    (fun s hs ↦ (hX.measurable ⟨hs.1,hs.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.2.mono (fun _ hω ↦ hω.1.mono (Icc_subset_Icc le_rfl hT1.le)))
  apply (hc t ⟨ht.1,htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩

lemma IsDiffusion.curvature_memLp {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) (p : ℝ≥0∞) :
    MemLp (fun ω ↦ curvature W γ t (X t ω)) p W.μ := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg t ht
  exact MemLp.of_bound
    (((hG.smooth t ⟨ht.1,le_rfl⟩).continuous_deriv (by norm_num)).measurable.comp
      (hX.measurable ⟨ht.1,ht.2.le⟩)).aestronglyMeasurable D
    (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (hDb t ⟨ht.1,le_rfl⟩ _)))

lemma IsDiffusion.curvature_mean_integrable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (ha : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
    IntervalIntegrable (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) volume 0 1 := by
  have hb (t : ℝ) (ht : t∈Ico (0 : ℝ) 1) :
      |∫ ω, curvature W γ t (X t ω) ∂W.μ|≤1 := by
    apply abs_integral_le_integral_abs.trans
    simpa only [ha t ht,Real.sqrt_one] using integral_abs_le_sqrt_second (hX.curvature_memLp hreg ht 2)
  have hi : IntegrableOn (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) (Ico (0 : ℝ) 1) :=
    Integrable.of_bound ((hX.curvature_mean_continuous hreg).aestronglyMeasurable measurableSet_Ico)
      1 ((ae_restrict_mem measurableSet_Ico).mono (fun t ht ↦ (Real.norm_eq_abs _).trans_le (hb t ht)))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
    (hi.congr_set_ae Ico_ae_eq_Ioc.symm)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_IntegralPrimitiveTerminal
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
open scoped Topology NNReal

lemma integral_primitive_terminal {f : ℝ → ℝ} (hi : IntervalIntegrable f volume 0 1) :
    Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, f t) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (show (0 : ℝ)∈uIcc (0 : ℝ) 1 from left_mem_uIcc)
  have ht : Tendsto (id : ℝ → ℝ) (𝓝[<] 1) (𝓝[uIcc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, by
      simpa only [id_eq,uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using eventually_time_mem⟩
  exact Filter.Tendsto.comp (hc 1 right_mem_uIcc) ht

theorem IsDiffusion.parisi_value_assembly_oai {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t)
    (hamom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1) :
    ∃ U : W.Ω → ℝ,
      Martingale (gradientStopped W γ X U) W.filtration W.μ ∧
      (∀ᵐ ω ∂W.μ, |U ω|≤1 ∧ (U ω)^2=1 ∧
        Tendsto (fun t ↦ gradient W γ t (X t ω)) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
      Tendsto (fun t ↦ ∫ ω, (gradient W γ t (X t ω)-U ω)^2 ∂W.μ)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) ∧
      parisi W γ=(∫ ω, |X 1 ω| ∂W.μ)-∫ t in (0 : ℝ)..1, t*γ.coeff t ∧
      parisi W γ=∫ ω, U ω*W.B 1 ω ∂W.μ ∧
      parisi W γ=∫ t in (0 : ℝ)..1, ∫ ω, curvature W γ t (X t ω) ∂W.μ ∧
      IntervalIntegrable (fun t ↦ ∫ ω, curvature W γ t (X t ω) ∂W.μ) volume 0 1 ∧
      Tendsto (fun T ↦ ∫ t in (0 : ℝ)..T, ∫ ω, curvature W γ t (X t ω) ∂W.μ)
        (𝓝[<] (1 : ℝ)) (𝓝 (parisi W γ)) := by
  obtain ⟨U,hUm,hmart,hU,hU2⟩ := hX.exists_gradient_terminal hreg.core hmom
  have hUmr : StronglyMeasurable[W.realFiltration 1] U := by
    change StronglyMeasurable[W.filtration ((1 : ℝ).toNNReal)] U
    rw [Real.toNNReal_one]
    exact hUm
  have hs : ∀ᵐ ω ∂W.μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ gradient W γ (terminalTime n) (X (terminalTime n) ω)) atTop (𝓝 (U ω)) :=
    hU.mono (fun _ hω ↦ ⟨hω.1,hω.2.2.comp terminalTime_tendsto⟩)
  have hm := hX.unitMomentMartingale hreg.core hmom
  have hc := hX.gradient_continuous (fun T hT ↦ by
    obtain ⟨K,L,Lu,hLu,hG,hu⟩ := hreg.core T hT
    exact ⟨Lu,hLu,hu⟩)
  have hP := hX.parisi_first_value (fun T hT hT1 ↦ by
    obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
    exact ⟨Kv,Lv,K,L,Lu,hV,hG,hLu,fun t ht s hs x y ↦ hu s hs t ht y x⟩) hmom
  have hUX := hX.terminal_gradient_product (Eventually.of_forall (fun ω ↦ by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with t ht
    obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg t ⟨ht.1.le,ht.2⟩
    exact ((hV.smooth t ⟨ht.1.le,le_rfl⟩).differentiable (by norm_num)).differentiableAt))
    (hU.mono (fun _ hω ↦ hω.2.2))
  have hid := hX.terminal_product_value hm hUmr hs hc
  rw [integral_congr_ae hUX] at hid
  have hPB : parisi W γ=∫ ω, U ω*W.B 1 ω ∂W.μ := by linarith
  have hi := hX.curvature_mean_integrable hreg hamom
  have hCov := hX.curvature_integral_terminal hreg hm hUmr hs
  have he := tendsto_nhds_unique hCov (integral_primitive_terminal hi)
  exact ⟨U,hmart,hU,hU2,hP,hPB,hPB.trans he,hi,by simpa only [←hPB] using hCov⟩

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsDiffusion.parisi_value_assembly_oai := @OAI.SKValue.IsDiffusion.parisi_value_assembly_oai
