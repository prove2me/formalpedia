-- Prove2me | solution 1 for OAI.SKValue.IsMinimizer.contact_origin_of_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:00:30.743834+00:00
-- url     : https://prove2.me/submissions/63b6b126-132a-4e04-84e8-8954c17e0beb

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_IsDiffusion_gradientMoment_continuous
import Theorems.Thm_OAI_SKValue_IsDiffusion_moment_difference_integrable
import Theorems.Thm_OAI_SKValue_IsMinimizer_contactPotential_nonneg
import Theorems.Thm_OAI_SKValue_phi_gradient_difference_bound
import Theorems.Thm_OAI_SKValue_sourceStripRegularity

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

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_Controls
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

lemma progressive_clamped_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} (hα : IsProgressive f α) (t : ℝ≥0) :
    @Measurable (ℝ×Ω) ℝ (borel ℝ |>.prod (f t)) inferInstance
      (fun p ↦ α (min (Real.toNNReal p.1) t) p.2) := by
  have hj := hα t
  let : MeasurableSpace Ω := f t
  have hc : Measurable (fun p : ℝ×Ω ↦
      (⟨min (Real.toNNReal p.1) t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Iic t)) :=
    ((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk
  exact hj.comp (hc.prodMk measurable_snd)

lemma controlAccum_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ}
    (hα : IsProgressive f α) (hγ : Measurable γ) (n : ℕ) {t : ℝ} (ht : 0≤t) :
    Measurable[f (Real.toNNReal t)] (controlAccum γ α n t) := by
  let : MeasurableSpace Ω := f (Real.toNNReal t)
  have hm : Measurable (fun p : ℝ×Ω ↦ γ p.1*(α (min (Real.toNNReal p.1) (Real.toNNReal t)) p.2)^n) :=
    (hγ.comp measurable_fst).mul ((progressive_clamped_measurable (m := m) hα _).pow_const n)
  have heq : controlAccum γ α n t = fun ω ↦
      ∫ s in (0 : ℝ)..t, γ s*(α (min (Real.toNNReal s) (Real.toNNReal t)) ω)^n := by
    funext ω
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    dsimp only
    rw [min_eq_left (Real.toNNReal_mono hs.2)]
  rw [heq]
  unfold intervalIntegral
  exact hm.stronglyMeasurable.integral_prod_left.measurable.sub
    hm.stronglyMeasurable.integral_prod_left.measurable

lemma controlAccum_integrand_intervalIntegrable {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) (n : ℕ) (ω : Ω) :
    IntervalIntegrable (fun s ↦ γ s*(α (Real.toNNReal s) ω)^n) volume 0 T := by
  have hm : Measurable (fun s ↦ γ s*(α (min (Real.toNNReal s) (Real.toNNReal T)) ω)^n) := by
    let : MeasurableSpace Ω := f (Real.toNNReal T)
    exact hγ.mul (((progressive_clamped_measurable (m := m) hα _).comp
      (measurable_id.prodMk measurable_const)).pow_const n)
  have hint : IntervalIntegrable (fun s ↦ γ s*(α (min (Real.toNNReal s) (Real.toNNReal T)) ω)^n) volume 0 T := by
    apply hi.norm.mono_fun'
    · exact hm.aestronglyMeasurable
    · exact Eventually.of_forall (fun s ↦ by
        dsimp only
        rw [Real.norm_eq_abs,abs_mul,abs_pow,Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hαb _ _))
          (abs_nonneg _)).trans_eq (mul_one _))
  apply hint.congr
  intro s hs
  rw [uIoc_of_le hT] at hs
  dsimp only
  rw [min_eq_left (Real.toNNReal_mono hs.2)]

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

lemma predictableCenteredSquare_memLp {N j : ℕ}
    {H : (Fin (N+1) → ℝ) → ℝ} {K : ℝ}
    (hm : Measurable H) (hbound : ∀ z, |H z|≤K) :
    MemLp (fun z ↦ H z*((coordinate N j z)^2-1)) 2 (gaussianProduct (Fin (N+1))) := by
  have hQ := (gaussian_centered_square_memLp_two (coordinate_hasLaw N j))
  have hH : MemLp H ∞ (gaussianProduct (Fin (N+1))) :=
    MemLp.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hbound))
  exact hQ.mul' hH

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

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlStability
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

lemma controlAccum_L1_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) (n : ℕ) (ω : Ω) :
    |controlAccum γ α n T ω|≤∫ s in (0 : ℝ)..T, |γ s| := by
  have hint := controlAccum_integrand_intervalIntegrable hα hαb hγ hi hT n ω
  apply (intervalIntegral.abs_integral_le_integral_abs hT).trans
  apply intervalIntegral.integral_mono_on hT hint.abs hi.abs
  intro s hs
  rw [abs_mul,abs_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hαb _ _)) (abs_nonneg _)).trans_eq (mul_one _)

lemma controlAccum_memLp_of_interval {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Filtration ℝ≥0 m}
    {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (controlAccum γ α n T) p μ := by
  apply MemLp.of_bound ((controlAccum_measurable hα hγ n hT).mono (f.le _) le_rfl).aestronglyMeasurable
    (∫ s in (0 : ℝ)..T, |γ s|)
  exact Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (controlAccum_L1_bound hα hαb hγ hi hT n ω))

lemma controlAccum_sub {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ η : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T)
    (hT : 0≤T) (n : ℕ) (ω : Ω) :
    controlAccum γ α n T ω-controlAccum η α n T ω=controlAccum (fun s ↦ γ s-η s) α n T ω := by
  have h1 := controlAccum_integrand_intervalIntegrable hα hαb hγ hiγ hT n ω
  have h2 := controlAccum_integrand_intervalIntegrable hα hαb hη hiη hT n ω
  simp only [controlAccum,sub_mul,intervalIntegral.integral_sub h1 h2]

lemma controlAccum_difference_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ η : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T)
    (hT : 0≤T) (n : ℕ) (ω : Ω) :
    |controlAccum γ α n T ω-controlAccum η α n T ω|≤∫ s in (0 : ℝ)..T, |γ s-η s| := by
  rw [controlAccum_sub hα hαb hγ hη hiγ hiη hT]
  exact controlAccum_L1_bound hα hαb (hγ.sub hη) (hiγ.sub hiη) hT n ω

lemma elapsedPayoff_integrable {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Filtration ℝ≥0 m}
    {α : ℝ≥0 → Ω → ℝ} {ψ γ : ℝ → ℝ} {T x : ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ)
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) :
    Integrable (fun ω ↦ ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω) μ := by
  have h1 := controlAccum_memLp_of_interval (μ := μ) hα hαb hγ hi hT 1 2
  have h2 := controlAccum_memLp_of_interval (μ := μ) hα hαb hγ hi hT 2 2
  have hs := lipschitz_comp_memLp_finite hψ (((memLp_const x).add hZ).add h1)
  exact (hs.integrable (by norm_num)).sub ((h2.integrable (by norm_num)).const_mul _)

lemma elapsedPayoff_difference_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Filtration ℝ≥0 m}
    {α : ℝ≥0 → Ω → ℝ} {ψ χ γ η : ℝ → ℝ} {T x ε : ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    (hε : ∀ y, |ψ y-χ y|≤ε) (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T) (hT : 0≤T) :
    |elapsedPayoff μ Z ψ γ T x α-elapsedPayoff μ Z χ η T x α|≤
      ε+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s-η s|) := by
  let D := ∫ s in (0 : ℝ)..T, |γ s-η s|
  have hp := elapsedPayoff_integrable hZ hψ hα hαb hγ hiγ hT (x := x)
  have hq := elapsedPayoff_integrable hZ hχ hα hαb hη hiη hT (x := x)
  unfold elapsedPayoff
  rw [←integral_sub hp hq]
  apply (abs_integral_le_integral_abs).trans
  have hb : ∀ ω,
      |(ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω)-
        (χ (x+Z ω+controlAccum η α 1 T ω)-(1/2 : ℝ)*controlAccum η α 2 T ω)|≤ε+(3/2 : ℝ)*D := by
    intro ω
    have h1 := controlAccum_difference_bound hα hαb hγ hη hiγ hiη hT 1 ω
    have h2 := controlAccum_difference_bound hα hαb hγ hη hiγ hiη hT 2 ω
    have hl := hχ.dist_le_mul (x+Z ω+controlAccum γ α 1 T ω) (x+Z ω+controlAccum η α 1 T ω)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,add_sub_add_left_eq_sub] at hl
    have htri := abs_sub_le (ψ (x+Z ω+controlAccum γ α 1 T ω))
      (χ (x+Z ω+controlAccum γ α 1 T ω)) (χ (x+Z ω+controlAccum η α 1 T ω))
    have he := hε (x+Z ω+controlAccum γ α 1 T ω)
    have hcost : |(1/2 : ℝ)*controlAccum γ α 2 T ω-(1/2 : ℝ)*controlAccum η α 2 T ω|≤(1/2 : ℝ)*D := by
      rw [←mul_sub,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have htri2 := norm_sub_le (ψ (x+Z ω+controlAccum γ α 1 T ω)-χ (x+Z ω+controlAccum η α 1 T ω))
      ((1/2 : ℝ)*controlAccum γ α 2 T ω-(1/2 : ℝ)*controlAccum η α 2 T ω)
    simp only [Real.norm_eq_abs] at htri2
    have heq : (ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω)-
        (χ (x+Z ω+controlAccum η α 1 T ω)-(1/2 : ℝ)*controlAccum η α 2 T ω)=
        (ψ (x+Z ω+controlAccum γ α 1 T ω)-χ (x+Z ω+controlAccum η α 1 T ω))-
        ((1/2 : ℝ)*controlAccum γ α 2 T ω-(1/2 : ℝ)*controlAccum η α 2 T ω) := by ring
    rw [heq]
    dsimp only [D] at *
    linarith
  exact (integral_mono (hp.sub hq).abs (integrable_const _) hb).trans_eq (by simp [D])

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_Verification
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal ENNReal
namespace SKValue

lemma value_bounded_drift_one_step {V : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {t δ x z r G K L : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hG : 0≤G) (hK : 0≤K) (hL : 0≤L) (hr : |r|≤G)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0≤γ t) (hγG : γ t≤G)
    (hsmooth : ContDiff ℝ 3 (V t))
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
    let d := Real.sqrt δ*z+δ*r
    |V (t+δ) (x+d)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)-
      δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2)| ≤
      δ*Real.sqrt δ*cubicEnvelope G K ((1/2+G)*L) z+
        δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*r
  have htm := gradient_generator_quadrature
    (b := fun s y ↦ deriv (deriv (V s)) y)
    (p := fun s y ↦ (1/2 : ℝ)*(deriv (V s) y)^2) (y := x+d)
    hδ hG hK hL hγ hγ0 hγG
    (fun s hs ↦ hp s hs _) (fun s hs ↦ haLip s hs _) (fun s hs ↦ hpLip s hs _)
    (haint _) (hpint _)
  have ht : |(V (t+δ) (x+d)-V t x+1-
        δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2))-
      (V t (x+d)-V t x+1)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+r*1*deriv (V t) x)| ≤
      δ*(((1/2 : ℝ)+G)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq : (V (t+δ) (x+d)-V t x+1-
        δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2))-
      (V t (x+d)-V t x+1)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+r*1*deriv (V t) x) =
        (V (t+δ) (x+d)-V t (x+d))+
          δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) := by ring
    rw [heq, hPDE]
    convert htm using 1
    · rw [show -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
          γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))+
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) =
        -((∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
          γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))-
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2))) by ring,
        abs_neg]
    · simp only [add_sub_cancel_left]
  have hs : |(V t (x+d)-V t x+1)-1-
      deriv (V t) x*d-(1/2 : ℝ)*deriv (deriv (V t)) x*d^2| ≤ K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound hsmooth hK hthird x d
  have hh := euler_cubic_remainder (v := 1) (c := r)
    hδ hδ1 hG hK (by positivity : 0≤(1/2+G)*L)
    hr (by norm_num) ha (by simpa only [mul_one] using hs)
    (by simpa only [mul_one] using ht)
  convert hh using 1 <;> dsimp only [cubicEnvelope, d]
  all_goals congr 1
  all_goals ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_SupStability
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

lemma elapsed_values_nonempty {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (f : Filtration ℝ≥0 m) (Z : Ω → ℝ) (ψ γ : ℝ → ℝ) (T x : ℝ) :
    {r | ∃ α, IsProgressive f α ∧ (∀ s ω, |α s ω|≤1) ∧ r=elapsedPayoff μ Z ψ γ T x α}.Nonempty := by
  exact ⟨_,fun _ _ ↦ 0,fun _ ↦ measurable_const,by norm_num,rfl⟩

lemma elapsed_values_bddAbove {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f : Filtration ℝ≥0 m)
    {Z : Ω → ℝ} {ψ γ : ℝ → ℝ} {T x : ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) :
    BddAbove {r | ∃ α, IsProgressive f α ∧ (∀ s ω, |α s ω|≤1) ∧ r=elapsedPayoff μ Z ψ γ T x α} := by
  refine ⟨(∫ ω, ψ (x+Z ω) ∂μ)+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s|),?_⟩
  rintro r ⟨α,hα,hαb,rfl⟩
  have hd := elapsedPayoff_difference_bound hZ hψ hψ (fun y ↦ by simp : ∀ y, |ψ y-ψ y|≤(0 : ℝ))
    hα hαb hγ measurable_const hi intervalIntegrable_const hT (x := x) (η := fun _ ↦ 0)
  simp only [elapsedPayoff,controlAccum,zero_mul,intervalIntegral.integral_zero,mul_zero,add_zero,sub_zero,zero_add] at hd
  have hh := (le_abs_self _).trans hd
  change elapsedPayoff μ Z ψ γ T x α≤_
  change elapsedPayoff μ Z ψ γ T x α-(∫ ω, ψ (x+Z ω) ∂μ)≤_ at hh
  linarith

lemma elapsedValue_sub_le {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Filtration ℝ≥0 m}
    {Z : Ω → ℝ} {ψ χ γ η : ℝ → ℝ} {T x ε : ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    (hε : ∀ y, |ψ y-χ y|≤ε) (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T) (hT : 0≤T) :
    elapsedValue μ f Z ψ γ T x≤elapsedValue μ f Z χ η T x+
      (ε+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s-η s|)) := by
  apply csSup_le (elapsed_values_nonempty μ f Z ψ γ T x)
  rintro r ⟨α,hα,hαb,rfl⟩
  have hd := (le_abs_self _).trans (elapsedPayoff_difference_bound hZ hψ hχ hε hα hαb hγ hη hiγ hiη hT (x := x))
  have hu : elapsedPayoff μ Z χ η T x α≤elapsedValue μ f Z χ η T x :=
    le_csSup (elapsed_values_bddAbove f hZ hχ hη hiη hT) ⟨α,hα,hαb,rfl⟩
  linarith

lemma elapsedValue_difference_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Filtration ℝ≥0 m}
    {Z : Ω → ℝ} {ψ χ γ η : ℝ → ℝ} {T x ε : ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    (hε : ∀ y, |ψ y-χ y|≤ε) (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T) (hT : 0≤T) :
    |elapsedValue μ f Z ψ γ T x-elapsedValue μ f Z χ η T x|≤
      ε+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s-η s|) := by
  have h1 := elapsedValue_sub_le (f := f) hZ hψ hχ hε hγ hη hiγ hiη hT (x := x)
  have h2 := elapsedValue_sub_le (f := f) hZ hχ hψ (fun y ↦ by rw [abs_sub_comm]; exact hε y) hη hγ hiη hiγ hT (x := x)
  simp_rw [abs_sub_comm (η _) (γ _)] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

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

lemma controlIntegral_eq_accum (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (α : ℝ≥0 → W.Ω → ℝ) (k : ℕ) (ω : W.Ω) :
    controlIntegral γ t α k ω=controlAccum (fun s ↦ γ.cutoff (t+s)) α k (1-t) ω := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (sub_nonneg.mpr ht.2)] at hs
  dsimp only
  rw [limitedControl_eq α (by linarith [hs.2,ht.1])]

lemma phi_eq_elapsedValue (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    phi W γ t x=elapsedValue W.μ (shiftedFiltration W t)
      (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω) abs (fun s ↦ γ.cutoff (t+s)) (1-t) x := by
  unfold phi elapsedValue
  congr 1
  ext r
  simp only [Admissible,and_assoc,controlPayoff_eq W γ ht,
    controlIntegral_eq_accum W γ ht,elapsedPayoff]

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
-- module Solutions.OAIQ4_Sk.SKValue_Control_Regularity
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

lemma ValueStrip.drift_one_step {T K L G t δ x z r : ℝ}
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : ValueStrip T γ V K L)
    (ht : 0≤t) (hδ : 0≤δ) (hδ1 : δ≤1) (htδ : t+δ≤T)
    (hG : γ T≤G) (hr : |r|≤G) :
    |V (t+δ) (x+Real.sqrt δ*z+δ*r)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)-
      δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2)| ≤
      δ*Real.sqrt δ*cubicEnvelope G K ((1/2+G)*L) z+
        δ*K*(γ (t+δ)-γ t) := by
  have htT : t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have hT : 0≤T := ht.trans htT
  have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht htδ
  have htm : t∈Icc (0 : ℝ) T := ⟨ht,htT⟩
  have hem : t+δ∈Icc (0 : ℝ) T := ⟨by linarith,htδ⟩
  have hTm : T∈Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hbint (y : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ) :=
    (h.second_integrable y).mono_set (by
      rw [uIcc_of_le (by linarith : t≤t+δ),uIcc_of_le hT]
      exact hsub)
  have hpint (y : ℝ) : IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) y)^2)) volume t (t+δ) :=
    (h.product_integrable y).mono_set (by
      rw [uIcc_of_le (by linarith : t≤t+δ),uIcc_of_le hT]
      exact hsub)
  have hh := value_bounded_drift_one_step (V := V) (γ := γ) (x := x) (z := z)
    hδ hδ1 ((h.gamma_nonneg T hTm).trans hG) h.K_nonneg h.L_nonneg hr
    (h.gamma_mono.mono hsub) (h.gamma_nonneg t htm)
    ((h.gamma_mono htm hTm htT).trans hG) (h.smooth t htm)
    (h.second_bound t htm x) (h.third_bound t htm)
    (fun s hs ↦ h.product_bound s (hsub hs))
    (fun s hs y ↦ h.second_lipschitz t htm s (hsub hs) x y)
    (fun s hs y ↦ h.product_lipschitz t htm s (hsub hs) x y)
    hbint hpint (fun y ↦ h.pde t htm (t+δ) hem y)
  simpa only [add_assoc] using hh

lemma crossFeedback_bound {V U : ℝ → ℝ → ℝ} {t x : ℝ}
    (hV : |deriv (V t) x|≤1) (hU : |deriv (U t) x|≤1) :
    |crossFeedback V U t x|≤1 := by
  dsimp [crossFeedback]
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2),div_le_iff₀ (by norm_num : (0 : ℝ)<2)]
  calc |deriv (U t) x+deriv (V t) x| ≤ |deriv (U t) x|+|deriv (V t) x| := abs_add_le _ _
    _ ≤ 1*2 := by linarith

lemma cross_value_one_step {T K L K' L' G t δ x z : ℝ}
    {γ β : ℝ → ℝ} {V U : ℝ → ℝ → ℝ}
    (hV : ValueStrip T γ V K L) (hU : ValueStrip T β U K' L')
    (ht : 0≤t) (hδ : 0≤δ) (hδ1 : δ≤1) (htδ : t+δ≤T)
    (hG : γ T≤G) (hG' : β T≤G) :
    let y := x+Real.sqrt δ*z+δ*(β t*crossFeedback V U t x)
    |(U (t+δ) y-V (t+δ) y)-(U t x-V t x)-
      (deriv (U t) x-deriv (V t) x)*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*(deriv (deriv (U t)) x-deriv (deriv (V t)) x)*(z^2-1)+
      (δ/2)*(β t-γ t)*(deriv (V t) x)^2| ≤
      δ*Real.sqrt δ*(cubicEnvelope G K ((1/2+G)*L) z+
        cubicEnvelope G K' ((1/2+G)*L') z)+
      δ*K*(γ (t+δ)-γ t)+δ*K'*(β (t+δ)-β t) := by
  have htT : t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have htm : t∈Icc (0 : ℝ) T := ⟨ht,htT⟩
  have hβ : 0≤β t := hU.gamma_nonneg t htm
  have hr : |β t*crossFeedback V U t x|≤G := by
    rw [abs_mul,abs_of_nonneg hβ]
    calc β t*|crossFeedback V U t x| ≤ β t*1 :=
        mul_le_mul_of_nonneg_left (crossFeedback_bound (hV.bounded _ htm _) (hU.bounded _ htm _)) hβ
      _ ≤ G := by simpa only [mul_one] using (hU.gamma_mono htm ⟨ht.trans htT,le_rfl⟩ htT).trans hG'
  have hv := hV.drift_one_step (x := x) (z := z) ht hδ hδ1 htδ hG hr
  have hu := hU.drift_one_step (x := x) (z := z) ht hδ hδ1 htδ hG' hr
  dsimp only
  have hab (a b : ℝ) : |a-b|≤|a|+|b| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le a 0 b
  convert (hab _ _).trans (add_le_add hu hv) using 1 <;>
    try dsimp only [crossFeedback]
  all_goals first | with_reducible_and_instances rfl | ring_nf

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_TruncatedStieltjes
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

lemma OrderParameter.truncatedStieltjes_zero (γ : OrderParameter) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) : γ.truncatedStieltjes T hT 0=γ.coeff 0 := by
  simp [OrderParameter.truncatedStieltjes,min_eq_right hT.1]

lemma OrderParameter.truncatedStieltjes_top (γ : OrderParameter) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) : γ.truncatedStieltjes T hT T=γ.coeff T := by
  simp [OrderParameter.truncatedStieltjes,max_eq_right hT.1]

lemma OrderParameter.truncatedMass_univ (γ : OrderParameter) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) :
    γ.truncatedMass T hT univ=ENNReal.ofReal (γ.coeff T) := by
  have h0 := γ.nonneg 0 (by norm_num)
  have hm := γ.monotone (by norm_num : (0 : ℝ)∈Ico (0 : ℝ) 1) hT hT.1
  simp only [OrderParameter.truncatedMass,Measure.add_apply,Measure.restrict_apply_univ,
    Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ (0 : ℝ)),smul_eq_mul,mul_one,
    StieltjesFunction.measure_Ioc,γ.truncatedStieltjes_zero hT,γ.truncatedStieltjes_top hT]
  rw [←ENNReal.ofReal_add (sub_nonneg.mpr hm) h0]
  congr 1
  ring

instance OrderParameter.truncatedMass_finite (γ : OrderParameter) (T : ℝ)
    (hT : T∈Ico (0 : ℝ) 1) : IsFiniteMeasure (γ.truncatedMass T hT) :=
  ⟨by rw [γ.truncatedMass_univ hT]; exact ENNReal.ofReal_lt_top⟩

lemma OrderParameter.truncatedMass_cdf (γ : OrderParameter) {T t : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) (ht : t∈Ico (0 : ℝ) 1) :
    γ.truncatedMass T hT (Iic t)=ENNReal.ofReal (min (γ.coeff t) (γ.coeff T)) := by
  have he : Iic t∩Ioc (0 : ℝ) T=Ioc 0 (min t T) := by
    ext s
    simp only [mem_inter_iff,mem_Iic,mem_Ioc,le_min_iff]
    tauto
  have hmin : min t T∈Ico (0 : ℝ) 1 := ⟨le_min ht.1 hT.1,(min_le_left _ _).trans_lt ht.2⟩
  have hm := γ.monotone (by norm_num : (0 : ℝ)∈Ico (0 : ℝ) 1) hmin hmin.1
  have h0 := γ.nonneg 0 (by norm_num)
  have hc : γ.truncatedStieltjes T hT (min t T)=min (γ.coeff t) (γ.coeff T) := by
    dsimp only [OrderParameter.truncatedStieltjes]
    rw [max_eq_right hmin.1,min_eq_right (min_le_right _ _)]
    rcases le_total t T with h | h
    · rw [min_eq_left h,min_eq_left (γ.monotone ht hT h)]
    · rw [min_eq_right h,min_eq_right (γ.monotone hT ht h)]
  have hm' : γ.coeff 0 ≤ min (γ.coeff t) (γ.coeff T) := by
    exact le_min (γ.monotone (by norm_num) ht ht.1) (γ.monotone (by norm_num) hT hT.1)
  simp only [OrderParameter.truncatedMass,Measure.add_apply,Measure.restrict_apply measurableSet_Iic,
    he,Measure.smul_apply,Measure.dirac_apply_of_mem (show (0 : ℝ)∈Iic t from ht.1),smul_eq_mul,mul_one,
    StieltjesFunction.measure_Ioc,γ.truncatedStieltjes_zero hT,hc]
  rw [←ENNReal.ofReal_add (sub_nonneg.mpr hm') h0]
  congr 1
  ring

lemma OrderParameter.truncatedMass_ae_mem (γ : OrderParameter) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) : ∀ᵐ s ∂γ.truncatedMass T hT,s∈Icc (0 : ℝ) T := by
  rw [ae_iff]
  change γ.truncatedMass T hT (Icc (0 : ℝ) T)ᶜ=0
  simp only [OrderParameter.truncatedMass,Measure.add_apply,
    Measure.restrict_apply measurableSet_Icc.compl,Measure.smul_apply]
  have he : (Icc (0 : ℝ) T)ᶜ∩Ioc 0 T=∅ := by
    exact disjoint_iff_inter_eq_empty.mp (disjoint_compl_left.mono_right Ioc_subset_Icc_self)
  rw [he,measure_empty,zero_add,Measure.dirac_apply]
  have hnot : (0 : ℝ)∉(Icc (0 : ℝ) T)ᶜ := notMem_compl_iff.mpr ⟨le_rfl,hT.1⟩
  rw [indicator_of_notMem hnot]
  simp

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

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_CrossExpectation
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

lemma predictableCenteredSquare_mean {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} (hm : Measurable H) (hp : DependsBefore j H) :
    (∫ z,H z*((coordinate N j z)^2-1) ∂gaussianProduct (Fin (N+1)))=0 := by
  have hind := (hp.independent hj hm).comp measurable_id
    ((measurable_id.pow_const 2).sub (measurable_const (a := (1 : ℝ))))
  have hi := hind.integral_mul_eq_mul_integral hm.aestronglyMeasurable
    (((measurable_coordinate N j).pow_const 2).sub measurable_const).aestronglyMeasurable
  change (∫ z,H z*((coordinate N j z)^2-1) ∂gaussianProduct (Fin (N+1)))=_ at hi
  simp only [Function.comp_apply,Pi.sub_apply,id_eq] at hi
  rw [hi,gaussian_centered_square_mean (coordinate_hasLaw N j),mul_zero]

lemma cross_value_expectation_step {T K L K' L' G t δ : ℝ}
    {γ β : ℝ → ℝ} {V U : ℝ → ℝ → ℝ}
    (hV : ValueStrip T γ V K L) (hU : ValueStrip T β U K' L')
    (ht : 0≤t) (hδ : 0≤δ) (hδ1 : δ≤1) (htδ : t+δ≤T)
    (hG : γ T≤G) (hG' : β T≤G) {N j : ℕ} (hj : j<N+1)
    {Y : (Fin (N+1) → ℝ) → ℝ} (hYm : Measurable Y)
    (hYp : DependsBefore j Y) (hY : MemLp Y 2 (gaussianProduct (Fin (N+1)))) :
    let μ := gaussianProduct (Fin (N+1))
    let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*(β t*crossFeedback V U t (Y z))
    |((∫ z,U (t+δ) (Y' z)-V (t+δ) (Y' z) ∂μ)-
      (∫ z,U t (Y z)-V t (Y z) ∂μ))+
      (δ/2)*(β t-γ t)*(∫ z,(deriv (V t) (Y z))^2 ∂μ)| ≤
      δ*Real.sqrt δ*(cubicEnvelopeMean G K ((1/2+G)*L)+
        cubicEnvelopeMean G K' ((1/2+G)*L'))+
      δ*K*(γ (t+δ)-γ t)+δ*K'*(β (t+δ)-β t) := by
  let μ := gaussianProduct (Fin (N+1))
  let p := fun z ↦ deriv (V t) (Y z)
  let q := fun z ↦ deriv (U t) (Y z)
  let a := fun z ↦ deriv (deriv (V t)) (Y z)
  let b := fun z ↦ deriv (deriv (U t)) (Y z)
  let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*(β t*crossFeedback V U t (Y z))
  let P := fun z ↦ Real.sqrt δ*rawIncrement (fun z ↦ q z-p z) j z
  let Q := fun z ↦ (δ/2)*((b z-a z)*((coordinate N j z)^2-1))
  let D := fun z ↦ U (t+δ) (Y' z)-V (t+δ) (Y' z)-(U t (Y z)-V t (Y z))+
    ((δ/2)*(β t-γ t))*(p z)^2
  let R := fun z ↦ D z-P z-Q z
  let E := fun z ↦ δ*Real.sqrt δ*(cubicEnvelope G K ((1/2+G)*L) (coordinate N j z)+
        cubicEnvelope G K' ((1/2+G)*L') (coordinate N j z))+
      δ*K*(γ (t+δ)-γ t)+δ*K'*(β (t+δ)-β t)
  have htT : t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have htm : t∈Icc (0 : ℝ) T := ⟨ht,htT⟩
  have hem : t+δ∈Icc (0 : ℝ) T := ⟨by linarith,htδ⟩
  have hGn : 0≤G := (hV.gamma_nonneg T ⟨ht.trans htT,le_rfl⟩).trans hG
  have hpm : Measurable p := ((hV.smooth t htm).continuous_deriv (by norm_num)).measurable.comp hYm
  have hqm : Measurable q := ((hU.smooth t htm).continuous_deriv (by norm_num)).measurable.comp hYm
  have ham : Measurable a := by
    have hc := (hV.smooth t htm).continuous_iteratedDeriv 2 (by norm_num)
    simp only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ] at hc
    exact hc.measurable.comp hYm
  have hbm : Measurable b := by
    have hc := (hU.smooth t htm).continuous_iteratedDeriv 2 (by norm_num)
    simp only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ] at hc
    exact hc.measurable.comp hYm
  have hpM : MemLp p 2 μ := MemLp.of_bound hpm.aestronglyMeasurable 1
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hV.bounded t htm (Y z)))
  have hqM : MemLp q 2 μ := MemLp.of_bound hqm.aestronglyMeasurable 1
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hU.bounded t htm (Y z)))
  have hfp : DependsBefore j (fun z ↦ q z-p z) := by
    intro z z' hz
    dsimp only [p,q]
    rw [hYp z z' hz]
  have hap : DependsBefore j (fun z ↦ b z-a z) := by
    intro z z' hz
    dsimp only [a,b]
    rw [hYp z z' hz]
  have hab (z) : |b z-a z|≤K'+K :=
    (abs_sub _ _).trans (add_le_add (hU.second_bound t htm (Y z)) (hV.second_bound t htm (Y z)))
  have hPi : Integrable P μ :=
    ((rawIncrement_memLp hj (hqm.sub hpm) hfp (hqM.sub hpM)).const_mul _).integrable (by norm_num)
  have hQi : Integrable Q μ :=
    ((predictableCenteredSquare_memLp (hbm.sub ham) hab).const_mul _).integrable (by norm_num)
  have hP0 : (∫ z,P z ∂μ)=0 := by
    dsimp only [P]
    rw [integral_const_mul,rawIncrement_mean (H := fun z ↦ q z-p z) hj (hqm.sub hpm) hfp,mul_zero]
  have hQ0 : (∫ z,Q z ∂μ)=0 := by
    dsimp only [Q]
    rw [integral_const_mul,predictableCenteredSquare_mean (H := fun z ↦ b z-a z) hj (hbm.sub ham) hap,mul_zero]
  have hfM : MemLp (fun z ↦ crossFeedback V U t (Y z)) 2 μ := by
    change MemLp (fun z ↦ (q z+p z)/2) 2 μ
    simpa only [div_eq_mul_inv,Pi.add_apply] using (hqM.add hpM).mul_const ((2 : ℝ)⁻¹)
  have hY'M : MemLp Y' 2 μ :=
    (hY.add ((gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).const_mul _)).add
      ((hfM.const_mul (β t)).const_mul δ)
  have hDnext := ((hU.value_memLp hem hY'M).sub (hV.value_memLp hem hY'M)).integrable (by norm_num)
  have hDcur := ((hU.value_memLp htm hY).sub (hV.value_memLp htm hY)).integrable (by norm_num)
  have hDi : Integrable D μ := (hDnext.sub hDcur).add (hpM.integrable_sq.const_mul _)
  have hRi : Integrable R μ := (hDi.sub hPi).sub hQi
  have hE1 := (cubicEnvelope_memLp_two (coordinate_hasLaw N j) hGn K ((1/2+G)*L)).integrable (by norm_num)
  have hE2 := (cubicEnvelope_memLp_two (coordinate_hasLaw N j) hGn K' ((1/2+G)*L')).integrable (by norm_num)
  have hEi : Integrable E μ := (((hE1.add hE2).const_mul _).add (integrable_const _)).add (integrable_const _)
  have hRE (z) : |R z|≤E z := by
    have hh := cross_value_one_step hV hU ht hδ hδ1 htδ hG hG' (x := Y z) (z := coordinate N j z)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [R,D,P,Q,p,q,a,b,Y',E,rawIncrement]
    congr 1
    ring
  have hRmean : (∫ z,R z ∂μ)=(∫ z,D z ∂μ) := by
    dsimp only [R]
    rw [integral_sub (f := fun z ↦ D z-P z) (g := Q) (hDi.sub hPi) hQi,
      integral_sub (f := D) (g := P) hDi hPi,hP0,hQ0,sub_zero,sub_zero]
  have hDmean : (∫ z,D z ∂μ)=
      ((∫ z,U (t+δ) (Y' z)-V (t+δ) (Y' z) ∂μ)-(∫ z,U t (Y z)-V t (Y z) ∂μ))+
      (δ/2)*(β t-γ t)*(∫ z,(p z)^2 ∂μ) := by
    dsimp only [D]
    rw [integral_add (f := fun z ↦ U (t+δ) (Y' z)-V (t+δ) (Y' z)-(U t (Y z)-V t (Y z)))
      (g := fun z ↦ ((δ/2)*(β t-γ t))*(p z)^2) (hDnext.sub hDcur) (hpM.integrable_sq.const_mul _),
      integral_sub (f := fun z ↦ U (t+δ) (Y' z)-V (t+δ) (Y' z))
      (g := fun z ↦ U t (Y z)-V t (Y z)) hDnext hDcur,integral_const_mul]
  have hEmean : (∫ z,E z ∂μ)=
      δ*Real.sqrt δ*(cubicEnvelopeMean G K ((1/2+G)*L)+cubicEnvelopeMean G K' ((1/2+G)*L'))+
      δ*K*(γ (t+δ)-γ t)+δ*K'*(β (t+δ)-β t) := by
    dsimp only [E]
    rw [integral_add (f := fun z ↦ δ*Real.sqrt δ*(cubicEnvelope G K ((1/2+G)*L) (coordinate N j z)+
      cubicEnvelope G K' ((1/2+G)*L') (coordinate N j z))+δ*K*(γ (t+δ)-γ t))
      (g := fun _ ↦ δ*K'*(β (t+δ)-β t))
      (((hE1.add hE2).const_mul _).add (integrable_const _)) (integrable_const _),
      integral_add (f := fun z ↦ δ*Real.sqrt δ*(cubicEnvelope G K ((1/2+G)*L) (coordinate N j z)+
      cubicEnvelope G K' ((1/2+G)*L') (coordinate N j z))) (g := fun _ ↦ δ*K*(γ (t+δ)-γ t))
      ((hE1.add hE2).const_mul _) (integrable_const _),integral_const_mul,
      integral_add (f := fun z ↦ cubicEnvelope G K ((1/2+G)*L) (coordinate N j z))
      (g := fun z ↦ cubicEnvelope G K' ((1/2+G)*L') (coordinate N j z)) hE1 hE2]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    have hm (K L : ℝ) : (∫ z,cubicEnvelope G K L (coordinate N j z) ∂gaussianProduct (Fin (N+1)))=
        cubicEnvelopeMean G K L := by
      simpa only [Function.comp_def,cubicEnvelopeMean,standardGaussian] using
        (coordinate_hasLaw N j).integral_comp (measurable_cubicEnvelope G K L).aestronglyMeasurable
    rw [hm,hm]
  change |((∫ z,U (t+δ) (Y' z)-V (t+δ) (Y' z) ∂μ)-(∫ z,U t (Y z)-V t (Y z) ∂μ))+
    (δ/2)*(β t-γ t)*(∫ z,(p z)^2 ∂μ)|≤_
  rw [←hDmean,←hRmean,←hEmean]
  exact (abs_integral_le_integral_abs).trans (integral_mono hRi.norm hEi hRE)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_CrossMesh
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

lemma abs_telescope_source {N : ℕ} {A b Γ Δ : ℕ → ℝ} {c d e : ℝ}
    (h : ∀ j<N,|A (j+1)-A j+b j| ≤ c+d*(Γ (j+1)-Γ j)+e*(Δ (j+1)-Δ j)) :
    |A N-A 0+∑ j∈Finset.range N,b j|≤
      (N : ℝ)*c+d*(Γ N-Γ 0)+e*(Δ N-Δ 0) := by
  have hs := (Finset.abs_sum_le_sum_abs (fun j ↦ A (j+1)-A j+b j) (Finset.range N)).trans
    (Finset.sum_le_sum (fun j hj ↦ h j (Finset.mem_range.mp hj)))
  simpa only [Finset.sum_add_distrib,Finset.sum_range_sub,←Finset.mul_sum,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hs

lemma cross_value_mesh_expectation {T K L K' L' G : ℝ}
    {γ β : ℝ → ℝ} {V U : ℝ → ℝ → ℝ}
    (hV : ValueStrip T γ V K L) (hU : ValueStrip T β U K' L')
    (hT : 0<T) (hT1 : T≤1) (hG : γ T≤G) (hG' : β T≤G) {N : ℕ} (hN : 0<N) :
    |(∫ z,U T (euler T N β (crossFeedback V U) z N)-
      V T (euler T N β (crossFeedback V U) z N) ∂gaussianProduct (Fin (N+1)))-
      (U 0 0-V 0 0)+crossMeshSource T N γ β V U|≤
    T*Real.sqrt (stepSize T N)*(cubicEnvelopeMean G K ((1/2+G)*L)+
      cubicEnvelopeMean G K' ((1/2+G)*L'))+
      stepSize T N*K*(γ T-γ 0)+stepSize T N*K'*(β T-β 0) := by
  let δ := stepSize T N
  let Y := euler T N β (crossFeedback V U)
  let A := fun j ↦ ∫ z,U (meshTime T N j) (Y z j)-V (meshTime T N j) (Y z j)
    ∂gaussianProduct (Fin (N+1))
  let b := fun j ↦ (δ/2)*(β (meshTime T N j)-γ (meshTime T N j))*
    (∫ z,(deriv (V (meshTime T N j)) (Y z j))^2 ∂gaussianProduct (Fin (N+1)))
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0≤δ := div_nonneg hT.le hNr.le
  have hδ1 : δ≤1 := by
    apply (div_le_iff₀ hNr).mpr
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    simpa only [one_mul] using hT1.trans hN1
  have htime (j : ℕ) (hj : j≤N) := mesh_time_mem hT.le hN hj
  have hs (j : ℕ) : meshTime T N j+δ=meshTime T N (j+1) := by
    dsimp [meshTime]; push_cast; ring
  have hlast : meshTime T N N=T := by dsimp [meshTime,stepSize]; field_simp
  have hzero : meshTime T N 0=0 := by simp [meshTime]
  have hfm (j : ℕ) (hj : j<N) : Measurable (crossFeedback V U (meshTime T N j)) :=
    (((hU.smooth _ (htime j hj.le)).continuous_deriv (by norm_num)).measurable.add
      ((hV.smooth _ (htime j hj.le)).continuous_deriv (by norm_num)).measurable).div_const 2
  have hfb (j : ℕ) (hj : j<N) (x : ℝ) : |crossFeedback V U (meshTime T N j) x|≤1 :=
    crossFeedback_bound (hV.bounded _ (htime j hj.le) x) (hU.bounded _ (htime j hj.le) x)
  have hstep (j : ℕ) (hj : j<N) : |A (j+1)-A j+b j|≤
      δ*Real.sqrt δ*(cubicEnvelopeMean G K ((1/2+G)*L)+cubicEnvelopeMean G K' ((1/2+G)*L'))+
      δ*K*(γ (meshTime T N (j+1))-γ (meshTime T N j))+
      δ*K'*(β (meshTime T N (j+1))-β (meshTime T N j)) := by
    have hYp : DependsBefore j (fun z ↦ Y z j) :=
      eulerCoefficient_dependsBefore T hj.le β (crossFeedback V U) (fun _ y ↦ y)
    have he := cross_value_expectation_step hV hU (htime j hj.le).1 hδ hδ1
      (by rw [hs]; exact (htime (j+1) (by omega)).2) hG hG' (by omega : j<N+1)
      (measurable_euler T N β (crossFeedback V U) hfm j hj.le) hYp
      (euler_memLp T N β (crossFeedback V U) hfm hfb j hj.le)
    dsimp only at he
    rw [hs] at he
    simpa only [A,b,Y,euler,δ,mul_assoc] using he
  have hh := abs_telescope_source (A := A) (b := b)
    (Γ := fun j ↦ γ (meshTime T N j)) (Δ := fun j ↦ β (meshTime T N j)) hstep
  have hA0 : A 0=U 0 0-V 0 0 := by simp [A,Y,meshTime,euler]
  rw [hA0,show A N=(∫ z,U T (Y z N)-V T (Y z N) ∂gaussianProduct (Fin (N+1))) by
    dsimp only [A]; rw [hlast],hlast,hzero] at hh
  have hNd : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  convert hh using 1
  · rfl
  · dsimp only [δ] at hNd ⊢
    simp only [←mul_assoc,hNd]

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma euler_same_noise_bound {T G L d e : ℝ} {N : ℕ} {γ β : ℝ → ℝ}
    {u v : ℝ → ℝ → ℝ} (hT : 0≤T) (hN : 0<N)
    (hG : 0≤G) (hL : 0≤L) (hd : 0≤d) (he : 0≤e)
    (hg : ∀ j<N,|γ (meshTime T N j)|≤G)
    (hc : ∀ j<N,|β (meshTime T N j)-γ (meshTime T N j)|≤d)
    (hv : ∀ j<N,∀ x,|v (meshTime T N j) x|≤1)
    (hs : ∀ j<N,∀ x,|v (meshTime T N j) x-u (meshTime T N j) x|≤e)
    (hu : ∀ j<N,∀ x y,|u (meshTime T N j) x-u (meshTime T N j) y|≤L*|x-y|)
    (z : Fin (N+1) → ℝ) {j : ℕ} (hj : j≤N) :
    |euler T N β v z j-euler T N γ u z j|≤T*(d+G*e)*Real.exp (T*G*L) := by
  let δ := stepSize T N
  have hδ : 0≤δ := div_nonneg hT (Nat.cast_nonneg _)
  have hNd : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  have hrec (k : ℕ) (hk : k<N) :
      |euler T N β v z (k+1)-euler T N γ u z (k+1)|≤
        (1+δ*G*L)*|euler T N β v z k-euler T N γ u z k|+δ*(d+G*e) := by
    let y := euler T N β v z k
    let x := euler T N γ u z k
    let t := meshTime T N k
    have hb : |β t*v t y-γ t*u t x|≤d+G*e+G*L*|y-x| := by
      calc
        |β t*v t y-γ t*u t x| = |(β t-γ t)*v t y+γ t*(v t y-u t y)+γ t*(u t y-u t x)| := by congr 1; ring
        _ ≤ |(β t-γ t)*v t y|+|γ t*(v t y-u t y)|+|γ t*(u t y-u t x)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ d*1+G*e+G*(L*|y-x|) := by
          simp only [abs_mul]
          gcongr
          · exact hc k hk
          · exact hv k hk y
          · exact hg k hk
          · exact hs k hk y
          · exact hg k hk
          · exact hu k hk y x
        _ = _ := by ring
    change |y+Real.sqrt δ*coordinate N k z+δ*β t*v t y-
      (x+Real.sqrt δ*coordinate N k z+δ*γ t*u t x)|≤_
    calc
      _ = |(y-x)+δ*(β t*v t y-γ t*u t x)| := by congr 1; ring
      _ ≤ |y-x|+δ*|β t*v t y-γ t*u t x| := by simpa only [abs_mul,abs_of_nonneg hδ] using abs_add_le (y-x) (δ*(β t*v t y-γ t*u t x))
      _ ≤ |y-x|+δ*(d+G*e+G*L*|y-x|) := add_le_add_right (mul_le_mul_of_nonneg_left hb hδ) _
      _ = _ := by ring
  have h := finite_discrete_gronwall (e := fun k ↦ |euler T N β v z k-euler T N γ u z k|) (mul_nonneg (mul_nonneg hδ hG) hL)
    (show |euler T N β v z 0-euler T N γ u z 0|=0 by simp [euler])
    (fun k hk ↦ mul_nonneg hδ (add_nonneg hd (mul_nonneg hG he))) hrec j hj
  have hsum : (∑ k∈Finset.range j,δ*(d+G*e))≤T*(d+G*e) := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [←hNd]
    have hjs : (j : ℝ)≤N := by exact_mod_cast hj
    nlinarith [mul_nonneg hG he,mul_nonneg hd hδ,mul_nonneg hδ (mul_nonneg hG he)]
  apply h.trans
  apply mul_le_mul hsum
  · apply Real.exp_le_exp.mpr
    calc
      (j : ℝ)*(δ*G*L)≤(N : ℝ)*(δ*G*L) := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (mul_nonneg (mul_nonneg hδ hG) hL)
      _=T*G*L := by rw [←hNd]; ring
  · positivity
  · positivity

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_CrossMeshComparison
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

lemma crossMeshSource_half_form (T : ℝ) (N : ℕ) (γ β : ℝ → ℝ) (V U : ℝ → ℝ → ℝ) :
    crossMeshSource T N γ β V U=stepSize T N*∑ j : Fin N,(β (meshTime T N j)-γ (meshTime T N j))*
      (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j))
        (euler T N β (crossFeedback V U) z j))^2 ∂gaussianProduct (Fin (N+1))) := by
  unfold crossMeshSource
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ (β (meshTime T N j)-γ (meshTime T N j))*
    (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j))
      (euler T N β (crossFeedback V U) z j))^2 ∂gaussianProduct (Fin (N+1))))]
  simp only [integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma crossMeshSource_difference_bound {T K L K' L' d R : ℝ}
    {γ β : ℝ → ℝ} {V U : ℝ → ℝ → ℝ}
    (hV : ValueStrip T γ V K L) (hU : ValueStrip T β U K' L')
    (hT : 0≤T) {N : ℕ} (hN : 0<N) (hd : 0≤d) (hR : 0≤R)
    (hc : ∀ t∈Icc (0 : ℝ) T,|β t-γ t|≤d)
    (hY : ∀ z : Fin (N+1) → ℝ,∀ j≤N,
      |euler T N β (crossFeedback V U) z j-euler T N γ (fun t ↦ deriv (V t)) z j|≤R) :
    |crossMeshSource T N γ β V U-ordinaryMeshSource T N γ β V|≤T*d*L*R := by
  have hδ : 0 ≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg _)
  have htime (j : ℕ) (hj : j≤N) := mesh_time_mem hT hN hj
  have hfm (j : ℕ) (hj : j<N) : Measurable (crossFeedback V U (meshTime T N j)) :=
    (((hU.smooth _ (htime j hj.le)).continuous_deriv (by norm_num)).measurable.add
      ((hV.smooth _ (htime j hj.le)).continuous_deriv (by norm_num)).measurable).div_const 2
  have hfb (j : ℕ) (hj : j<N) (x : ℝ) : |crossFeedback V U (meshTime T N j) x|≤1 :=
    crossFeedback_bound (hV.bounded _ (htime j hj.le) x) (hU.bounded _ (htime j hj.le) x)
  have hm (j : Fin N) :
      |(∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N β (crossFeedback V U) z j))^2
        ∂gaussianProduct (Fin (N+1)))-
       (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N γ (fun t ↦ deriv (V t)) z j))^2
        ∂gaussianProduct (Fin (N+1)))|≤L*R := by
    have hLip := hV.product_lipschitzWith (htime j j.isLt.le)
    have hM1 := lipschitz_comp_memLp_finite hLip (euler_memLp T N β (crossFeedback V U) hfm hfb j j.isLt.le)
    have hM2 := lipschitz_comp_memLp_finite hLip (euler_memLp T N γ (fun t ↦ deriv (V t))
      (fun k hk ↦ ((hV.smooth _ (htime k hk.le)).continuous_deriv (by norm_num)).measurable)
      (fun k hk x ↦ hV.bounded _ (htime k hk.le) x) j j.isLt.le)
    rw [←integral_sub (f := fun z ↦ (1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N β (crossFeedback V U) z j))^2)
      (g := fun z ↦ (1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N γ (fun t ↦ deriv (V t)) z j))^2)
      (hM1.integrable (by norm_num)) (hM2.integrable (by norm_num))]
    apply (abs_integral_le_integral_abs).trans
    calc
      _ ≤ ∫ _ : Fin (N+1) → ℝ,|L*R| ∂gaussianProduct (Fin (N+1)) := by
        apply integral_mono ((hM1.integrable (by norm_num)).sub (hM2.integrable (by norm_num))).norm (integrable_const _)
        intro z
        have hh := hLip.dist_le_mul (euler T N β (crossFeedback V U) z j) (euler T N γ (fun t ↦ deriv (V t)) z j)
        rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ hV.L_nonneg] at hh
        exact (hh.trans (mul_le_mul_of_nonneg_left (hY z j j.isLt.le) hV.L_nonneg)).trans
          (le_abs_self (L*R))
      _=L*R := by simp [abs_of_nonneg (mul_nonneg hV.L_nonneg hR)]
  rw [crossMeshSource_half_form,ordinaryMeshSource,←mul_sub,←Finset.sum_sub_distrib,
    abs_mul,abs_of_nonneg hδ]
  calc
    _ ≤ stepSize T N*∑ j : Fin N,|(β (meshTime T N j)-γ (meshTime T N j))*
      ((∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N β (crossFeedback V U) z j))^2 ∂gaussianProduct (Fin (N+1)))-
       (∫ z,(1/2 : ℝ)*(deriv (V (meshTime T N j)) (euler T N γ (fun t ↦ deriv (V t)) z j))^2 ∂gaussianProduct (Fin (N+1))))| := by
      simp_rw [←mul_sub]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hδ
    _ ≤ stepSize T N*∑ _ : Fin N,d*(L*R) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hc _ (htime j j.isLt.le)) (hm j) (abs_nonneg _) hd
    _=T*d*L*R := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,stepSize]
      field_simp

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_WeightedMoments
attribute [-instance] _root_.OAI.SKValue.OrderParameter.truncatedMass_finite _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma IsDiffusion.weightedEulerMoment_tendsto {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (η : OrderParameter)
    {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    Tendsto (weightedEulerMoment W γ η T) atTop
      (𝓝 (∫ t in (0 : ℝ)..T,η.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ))) := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := sourceStripRegularity W γ T ⟨hT.le,hT1⟩
  let E (N : ℕ) := ∫ ω,(meshMaxError T X (coupledEuler T γ.coeff (gradient W γ) W.B) N ω)^2 ∂W.μ
  let f (t : ℝ) := ∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ
  have hXM (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : MemLp (X t) 2 W.μ := hX.memLp ⟨ht.1,ht.2.trans hT1.le⟩ (by norm_num)
  have hpaths := hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x)
  have hEl : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence W.brownian.toIsPreBrownianReal
    hT hG hLu hu (fun t ht ↦ (hXM t ht).aestronglyMeasurable) hpaths
  have hEs : Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hEl
  have hf : ContinuousOn f (Icc (0 : ℝ) T) := by
    have hc := (mean_derivative_square_continuous (by norm_num : (0 : ℝ)≤1) hLu
      (fun t ht ↦ (hG.smooth t ht).continuous) hG.bounded hu
      (fun t ht ↦ (hXM t ht).aestronglyMeasurable) (hpaths.mono (fun _ hω ↦ hω.1))).const_mul (1/2 : ℝ)
    simpa only [f,gradient,integral_const_mul] using hc
  have hfB (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |f t|≤Kv := by
    simpa only [f,Real.norm_eq_abs,probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ := W.μ) (C := Kv)
        (f := fun ω ↦ (1/2 : ℝ)*(gradient W γ t (X t ω))^2)
        (Eventually.of_forall (fun ω ↦ by
          simpa only [Real.norm_eq_abs,gradient] using hV.product_bound t ht (X t ω))))
  apply perturbed_monotone_weighted_grid_tendsto (r := fun N ↦ Lv*Real.sqrt (E N)) hT hV.K_nonneg
    (η.monotone.mono (fun t ht ↦ ⟨ht.1,ht.2.trans_lt hT1⟩)) (η.nonneg 0 (by norm_num)) hf hfB
    (by simpa only [mul_zero] using hEs.const_mul Lv)
  filter_upwards [eventually_gt_atTop 0] with N hN j
  have hh := coupled_lipschitz_expectation_bound W.brownian.toIsPreBrownianReal hT hG
    (fun t ht ↦ hXM t ht) (hpaths.mono (fun _ hω ↦ hω.2.2)) hN j.isLt.le
    (hV.product_lipschitzWith (mesh_time_mem hT.le hN j.isLt.le))
  simpa only [Real.coe_toNNReal _ hV.L_nonneg,E,f,gradient] using hh

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma phi_difference_bound (W : BrownianSpace) (γ β : OrderParameter)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    |phi W β t x-phi W γ t x|≤(3/2 : ℝ)*(∫ s in t..1,|β.cutoff s-γ.cutoff s|) := by
  have hψ : LipschitzWith 1 (abs : ℝ → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub a b
  have hi (η : OrderParameter) : IntervalIntegrable (fun s ↦ η.cutoff (t+s)) volume 0 (1-t) := by
    simpa only [sub_self] using (η.cutoff_integrable.intervalIntegrable (a := t) (b := 1)).comp_add_left t
  have he := elapsedValue_difference_bound (f := shiftedFiltration W t)
    (brownian_increment_memLp W t) hψ hψ (fun y ↦ by simp : ∀ y : ℝ,|abs y-abs y|≤(0 : ℝ))
    (β.cutoff_measurable.comp (measurable_const.add measurable_id))
    (γ.cutoff_measurable.comp (measurable_const.add measurable_id)) (hi β) (hi γ)
    (sub_nonneg.mpr ht.2) (x := x)
  simp only [Function.comp_def,Pi.add_apply, id_eq] at he
  rw [←phi_eq_elapsedValue W β ht x,←phi_eq_elapsedValue W γ ht x] at he
  have hshift := intervalIntegral.integral_comp_add_left (fun s ↦ |β.cutoff s-γ.cutoff s|)
    (a := (0 : ℝ)) (b := 1-t) t
  simp only [add_zero,add_sub_cancel] at hshift
  rw [hshift] at he
  simpa only [zero_add] using he

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_CrossValueBound
attribute [-instance] _root_.OAI.SKValue.OrderParameter.truncatedMass_finite _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma ordinaryMeshSource_eq (W : BrownianSpace) (γ β : OrderParameter) (T : ℝ) (N : ℕ) :
    ordinaryMeshSource T N γ.coeff β.coeff (phi W γ)=
      weightedEulerMoment W γ β T N-weightedEulerMoment W γ γ T N := by
  have he : gradient W γ=(fun t ↦ deriv (phi W γ t)) := rfl
  simp only [ordinaryMeshSource,weightedEulerMoment,he,←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma IsDiffusion.cross_value_bound {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (β : OrderParameter)
    {T Kv Lv Lu d e : ℝ} (hT : 0<T) (hT1 : T<1)
    (hV : ValueStrip T γ.coeff (phi W γ) Kv Lv)
    (hLu : 0≤Lu) (hd : 0≤d) (he : 0≤e)
    (hc : ∀ t∈Icc (0 : ℝ) T,|(β.coeff t)-(γ.coeff t)|≤d)
    (hu : ∀ t∈Icc (0 : ℝ) T,∀ x y,|gradient W γ t x-gradient W γ t y|≤Lu*|x-y|)
    (hs : ∀ t∈Icc (0 : ℝ) T,∀ x,|gradient W β t x-gradient W γ t x|≤e) :
    phi W β 0 0-phi W γ 0 0≤
      (3/2 : ℝ)*(∫ t in T..1,|β.cutoff t-γ.cutoff t|)+
      ((∫ t in (0 : ℝ)..T,β.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ))-
       (∫ t in (0 : ℝ)..T,γ.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ)))+
      T*d*Lv*(T*(d+γ.coeff T*e)*Real.exp (T*γ.coeff T*Lu)) := by
  obtain ⟨Kv',Lv',K',L',D',Lu',La',hU,rest⟩ := sourceStripRegularity W β T ⟨hT.le,hT1⟩
  let G := max (γ.coeff T) (β.coeff T)
  let R := T*(d+γ.coeff T*e)*Real.exp (T*γ.coeff T*Lu)
  let B := (3/2 : ℝ)*(∫ t in T..1,|β.cutoff t-γ.cutoff t|)
  let err (N : ℕ) :=
    T*Real.sqrt (stepSize T N)*(cubicEnvelopeMean G Kv ((1/2+G)*Lv)+
      cubicEnvelopeMean G Kv' ((1/2+G)*Lv'))+
      stepSize T N*Kv*(γ.coeff T-γ.coeff 0)+stepSize T N*Kv'*(β.coeff T-β.coeff 0)
  have hγT : 0≤γ.coeff T := γ.nonneg T ⟨hT.le,hT1⟩
  have hR : 0≤R := by dsimp [R]; positivity
  have heN (N : ℕ) (hN : 0<N) : phi W β 0 0-phi W γ 0 0≤
      B+(weightedEulerMoment W γ β T N-weightedEulerMoment W γ γ T N)+T*d*Lv*R+err N := by
    have htime (j : ℕ) (hj : j≤N) := mesh_time_mem hT.le hN hj
    have hfb (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
        |crossFeedback (phi W γ) (phi W β) t x|≤1 :=
      crossFeedback_bound (hV.bounded t ht x) (hU.bounded t ht x)
    have hfs (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
        |crossFeedback (phi W γ) (phi W β) t x-gradient W γ t x|≤e := by
      have hh := hs t ht x
      have hh' : |crossFeedback (phi W γ) (phi W β) t x-gradient W γ t x|=
          |gradient W β t x-gradient W γ t x|/2 := by
        dsimp only [crossFeedback,gradient]
        rw [show (deriv (phi W β t) x+deriv (phi W γ t) x)/2-deriv (phi W γ t) x=
          (deriv (phi W β t) x-deriv (phi W γ t) x)/2 by ring,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
      rw [hh']
      linarith
    have hY (z : Fin (N+1) → ℝ) (j : ℕ) (hj : j≤N) :
        |euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z j-
          euler T N γ.coeff (gradient W γ) z j|≤R := by
      apply euler_same_noise_bound hT.le hN hγT hLu hd he
      · intro k hk
        rw [abs_of_nonneg (γ.nonneg _ ⟨(htime k hk.le).1,(htime k hk.le).2.trans_lt hT1⟩)]
        exact γ.monotone ⟨(htime k hk.le).1,(htime k hk.le).2.trans_lt hT1⟩ ⟨hT.le,hT1⟩ (htime k hk.le).2
      · intro k hk; exact hc _ (htime k hk.le)
      · intro k hk; exact hfb _ (htime k hk.le)
      · intro k hk; exact hfs _ (htime k hk.le)
      · intro k hk; exact hu _ (htime k hk.le)
      · exact hj
    have htelescope := cross_value_mesh_expectation hV hU hT hT1.le
      (le_max_left _ _ : γ.coeff T≤G) (le_max_right _ _ : β.coeff T≤G) hN
    have hcompare := crossMeshSource_difference_bound hV hU hT.le hN hd hR hc hY
    rw [ordinaryMeshSource_eq] at hcompare
    have hterminal : (∫ z,phi W β T (euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z N)-
        phi W γ T (euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z N)
        ∂gaussianProduct (Fin (N+1)))≤B := by
      apply (le_abs_self _).trans
      simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
        (norm_integral_le_of_norm_le_const (μ := gaussianProduct (Fin (N+1))) (C := B)
          (f := fun z ↦ phi W β T (euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z N)-
            phi W γ T (euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z N))
          (Eventually.of_forall (fun z ↦ phi_difference_bound W γ β ⟨hT.le,hT1.le⟩ _)))
    have htlow := (abs_le.mp htelescope).1
    have hcup := (abs_le.mp hcompare).2
    dsimp only [err]
    linarith
  have hδ : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 (0 : ℝ)) := tendsto_const_div_atTop_nhds_zero_nat T
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hδ
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err,Function.comp_def,Real.sqrt_zero,mul_zero,zero_mul,zero_add] using
      (((hsqrt.const_mul T).mul_const (cubicEnvelopeMean G Kv ((1/2+G)*Lv)+
        cubicEnvelopeMean G Kv' ((1/2+G)*Lv'))).add
        ((hδ.mul_const Kv).mul_const (γ.coeff T-γ.coeff 0))).add
        ((hδ.mul_const Kv').mul_const (β.coeff T-β.coeff 0))
  have hlim := (((((hX.weightedEulerMoment_tendsto β hT hT1).sub
    (hX.weightedEulerMoment_tendsto γ hT hT1)).const_add B).add_const (T*d*Lv*R)).add herr)
  have hh := ge_of_tendsto hlim (by filter_upwards [eventually_gt_atTop 0] with N hN using heN N hN)
  simpa only [add_zero,B,R] using hh

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_OrderVariations
attribute [-instance] _root_.OAI.SKValue.OrderParameter.truncatedMass_finite _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma OrderParameter.mix_coeff_sub (γ η : OrderParameter) {ε : ℝ} (hε : ε∈Icc (0 : ℝ) 1) (t : ℝ) :
    (γ.mix η ε hε).coeff t-γ.coeff t=ε*(η.coeff t-γ.coeff t) := by dsimp [OrderParameter.mix]; ring

lemma OrderParameter.mix_cutoff_sub (γ η : OrderParameter) {ε : ℝ} (hε : ε∈Icc (0 : ℝ) 1) (t : ℝ) :
    (γ.mix η ε hε).cutoff t-γ.cutoff t=ε*(η.cutoff t-γ.cutoff t) := by
  by_cases ht : t∈Ico (0 : ℝ) 1
  · simp only [OrderParameter.cutoff,indicator_of_mem ht]
    exact γ.mix_coeff_sub η hε t
  · simp only [OrderParameter.cutoff,indicator_of_notMem ht,sub_self,mul_zero]

lemma OrderParameter.mix_difference_integral (γ η : OrderParameter) {ε : ℝ}
    (hε : ε∈Icc (0 : ℝ) 1) (a b : ℝ) :
    (∫ t in a..b,|(γ.mix η ε hε).cutoff t-γ.cutoff t|)=
      ε*(∫ t in a..b,|η.cutoff t-γ.cutoff t|) := by
  simp_rw [γ.mix_cutoff_sub η hε,abs_mul,abs_of_nonneg hε.1]
  exact intervalIntegral.integral_const_mul ε _

lemma OrderParameter.mix_strip_difference_bound (γ η : OrderParameter) {ε T : ℝ}
    (hε : ε∈Icc (0 : ℝ) 1) (hT : T∈Ico (0 : ℝ) 1) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    |(γ.mix η ε hε).coeff t-γ.coeff t|≤ε*(η.coeff T+γ.coeff T) := by
  rw [γ.mix_coeff_sub η hε,abs_mul,abs_of_nonneg hε.1]
  apply mul_le_mul_of_nonneg_left _ hε.1
  have ht' : t∈Ico (0 : ℝ) 1 := ⟨ht.1,ht.2.trans_lt hT.2⟩
  calc |η.coeff t-γ.coeff t|≤|η.coeff t|+|γ.coeff t| := abs_sub _ _
    _=η.coeff t+γ.coeff t := by rw [abs_of_nonneg (η.nonneg t ht'),abs_of_nonneg (γ.nonneg t ht')]
    _≤η.coeff T+γ.coeff T := add_le_add (η.monotone ht' hT ht.2) (γ.monotone ht' hT ht.2)

lemma OrderParameter.weighted_intervalIntegrable (γ : OrderParameter) :
    IntervalIntegrable (fun t ↦ t*γ.coeff t) volume 0 1 :=
  γ.intervalIntegrable.continuousOn_mul continuousOn_id

lemma IsMinimizer.mix_value_inequality {W : BrownianSpace} {γ : OrderParameter}
    (hγ : IsMinimizer W γ) (η : OrderParameter) {ε : ℝ} (hε : ε∈Icc (0 : ℝ) 1) :
    (ε/2)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))≤
      phi W (γ.mix η ε hε) 0 0-phi W γ 0 0 := by
  have hh := hγ (γ.mix η ε hε)
  have hi : (∫ t in (0 : ℝ)..1,t*(γ.mix η ε hε).coeff t)-
      (∫ t in (0 : ℝ)..1,t*γ.coeff t)=ε*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t)) := by
    rw [←intervalIntegral.integral_sub (γ.mix η ε hε).weighted_intervalIntegrable γ.weighted_intervalIntegrable,
      ←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [OrderParameter.mix]
    ring
  dsimp only [parisi] at hh
  linarith

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma gradientMoment_nonneg (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) (t : ℝ) : 0≤gradientMoment W γ X t :=
  integral_nonneg (fun _ ↦ sq_nonneg _)

lemma gradientMoment_bound (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    |gradientMoment W γ X t|≤1 := by
  simpa only [gradientMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ := W.μ) (C := (1 : ℝ))
      (f := fun ω ↦ (gradient W γ t (X t ω))^2)
      (Eventually.of_forall (fun ω ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_one_iff_abs_le_one _).mpr (gradient_bound W γ ht _))))

lemma IsDiffusion.weightedMoment_integrable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (η : OrderParameter) :
    IntervalIntegrable (fun t ↦ η.coeff t*gradientMoment W γ X t) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
  have hm := hX.gradientMoment_continuous.aestronglyMeasurable (μ := volume) measurableSet_Ico
  rw [restrict_Ico_eq_restrict_Ioc] at hm
  exact η.integrable.mul_bdd hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using gradientMoment_bound W γ X ⟨ht.1.le,ht.2⟩)

lemma IsDiffusion.weightedMean_integrable {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (η : OrderParameter) :
    IntervalIntegrable (fun t ↦ η.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ)) volume 0 1 := by
  have hi := (hX.weightedMoment_integrable η).const_mul (1/2 : ℝ)
  simpa only [integral_const_mul,mul_left_comm,gradientMoment] using hi

lemma IsDiffusion.mix_moment_integral {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (η : OrderParameter)
    {ε T : ℝ} (hε : ε∈Icc (0 : ℝ) 1) (hT : T∈Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..T,(γ.mix η ε hε).coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ))-
    (∫ t in (0 : ℝ)..T,γ.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ))=
    (ε/2)*(∫ t in (0 : ℝ)..T,(η.coeff t-γ.coeff t)*gradientMoment W γ X t) := by
  have ht : uIcc (0 : ℝ) T⊆uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le hT.1,uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using Icc_subset_Icc le_rfl hT.2
  rw [←intervalIntegral.integral_sub ((hX.weightedMean_integrable _).mono_set ht)
    ((hX.weightedMean_integrable _).mono_set ht),←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [integral_const_mul]
  dsimp only [OrderParameter.mix,gradientMoment]
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_FirstVariationCompact
attribute [-instance] _root_.OAI.SKValue.OrderParameter.truncatedMass_finite _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma IsMinimizer.compact_variation_inequality {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    (η : OrderParameter) {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))≤
      (3/2 : ℝ)*(∫ t in T..1,|η.cutoff t-γ.cutoff t|)+
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..T,(η.coeff t-γ.coeff t)*gradientMoment W γ X t) := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := sourceStripRegularity W γ T ⟨hT.le,hT1⟩
  let A := ∫ t in (0 : ℝ)..1,|η.cutoff t-γ.cutoff t|
  let C := η.coeff T+γ.coeff T
  let R (h : ℝ) := T*(h^2*C+γ.coeff T*(h*(Lu+3*A)))*Real.exp (T*γ.coeff T*Lu)
  let B := (3/2 : ℝ)*(∫ t in T..1,|η.cutoff t-γ.cutoff t|)+
    (1/2 : ℝ)*(∫ t in (0 : ℝ)..T,(η.coeff t-γ.coeff t)*gradientMoment W γ X t)
  have hA : 0≤A := intervalIntegral.integral_nonneg (by norm_num) (fun t ht ↦ abs_nonneg _)
  have hC : 0≤C := add_nonneg (η.nonneg T ⟨hT.le,hT1⟩) (γ.nonneg T ⟨hT.le,hT1⟩)
  have hAi : IntervalIntegrable (fun t ↦ |η.cutoff t-γ.cutoff t|) volume 0 1 :=
    (η.cutoff_integrable.sub γ.cutoff_integrable).norm.intervalIntegrable
  have htA (t : ℝ) (ht : t∈Icc (0 : ℝ) T) :
      (∫ s in t..1,|η.cutoff s-γ.cutoff s|)≤A := by
    exact intervalIntegral.integral_mono_interval ht.1 (ht.2.trans hT1.le) le_rfl
      (Eventually.of_forall (fun s ↦ abs_nonneg _)) hAi
  have hul (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x y : ℝ) :
      |gradient W γ t x-gradient W γ t y|≤Lu*|x-y| := by
    simpa only [sub_self,abs_zero,zero_add] using hu t ht t ht x y
  have hh (h : ℝ) (hh0 : 0<h) (hh1 : h≤1) :
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))≤B+T*C*Lv*R h := by
    have hε : h^2∈Icc (0 : ℝ) 1 := ⟨sq_nonneg _,(sq_le_one_iff_abs_le_one _).mpr (by rw [abs_of_pos hh0]; exact hh1)⟩
    let β := γ.mix η (h^2) hε
    have hph (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
        |phi W β t x-phi W γ t x|≤(3/2 : ℝ)*h^2*A := by
      have hb := phi_difference_bound W γ β ⟨ht.1,ht.2.trans hT1.le⟩ x
      rw [γ.mix_difference_integral η hε] at hb
      exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left (htA t ht) (sq_nonneg h)])
    have hgs (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
        |gradient W β t x-gradient W γ t x|≤h*(Lu+3*A) := by
      have hb := phi_gradient_difference_bound W γ β ⟨hT.le,hT1⟩ hul hph hh0 ht x
      have heq : Lu*h+2*((3/2 : ℝ)*h^2*A)/h=h*(Lu+3*A) := by field_simp
      rwa [heq] at hb
    have hv := hX.cross_value_bound β hT hT1 hV hLu
      (mul_nonneg (sq_nonneg h) hC) (mul_nonneg hh0.le (by positivity : 0≤Lu+3*A))
      (fun t ht ↦ γ.mix_strip_difference_bound η hε ⟨hT.le,hT1⟩ ht) hul hgs
    rw [γ.mix_difference_integral η hε,hX.mix_moment_integral η hε ⟨hT.le,hT1.le⟩] at hv
    have hm := hγ.mix_value_inequality η hε
    have hv' : (h^2/2)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))≤
        h^2*(B+T*C*Lv*R h) := by
      calc
        _≤phi W β 0 0-phi W γ 0 0 := hm
        _≤_ := hv
        _=h^2*(B+T*C*Lv*R h) := by dsimp only [B,R,C] at *; ring
    have heq : (h^2/2)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))=
        h^2*((1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))) := by ring
    rw [heq] at hv'
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hh0)).mp hv'
  have hzero : Tendsto (fun h : ℝ ↦ h) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hRlim : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [R,zero_pow (by norm_num : (2 : ℕ)≠0),zero_mul,mul_zero,add_zero] using
      (((hzero.pow 2).mul_const C).add ((hzero.mul_const (Lu+3*A)).const_mul (γ.coeff T))).const_mul T |>.mul_const (Real.exp (T*γ.coeff T*Lu))
  have hlim := (hRlim.const_mul (T*C*Lv)).const_add B
  have hb := ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ)<1)] with h hhs
    exact hh h hhs.1 hhs.2.le)
  simpa only [mul_zero,add_zero,B] using hb

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma tail_integral_tendsto_zero {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    Tendsto (fun T ↦ ∫ t in T..1,f t) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hlim := (integral_primitive_terminal hf).const_sub (∫ t in (0 : ℝ)..1,f t)
  have hlim' : Tendsto (fun T ↦ (∫ t in (0 : ℝ)..1,f t)-(∫ t in (0 : ℝ)..T,f t))
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by simpa only [sub_self] using hlim
  apply hlim'.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
  have hi : IntervalIntegrable f volume 0 T := hf.mono_set (by simpa only [uIcc_of_le hT.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using Icc_subset_Icc le_rfl hT.2.le)
  have hi' : IntervalIntegrable f volume T 1 := hf.mono_set (by simpa only [uIcc_of_le hT.2.le,uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using Icc_subset_Icc hT.1.le le_rfl)
  linarith [intervalIntegral.integral_add_adjacent_intervals hi hi']

lemma IsMinimizer.variation_inequality {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    (η : OrderParameter) :
    0≤∫ t in (0 : ℝ)..1,(η.coeff t-γ.coeff t)*(gradientMoment W γ X t-t) := by
  have hAi : IntervalIntegrable (fun t ↦ |η.cutoff t-γ.cutoff t|) volume 0 1 :=
    (η.cutoff_integrable.sub γ.cutoff_integrable).norm.intervalIntegrable
  have hqi : IntervalIntegrable (fun t ↦ (η.coeff t-γ.coeff t)*gradientMoment W γ X t) volume 0 1 := by
    simpa only [sub_mul] using (hX.weightedMoment_integrable η).sub (hX.weightedMoment_integrable γ)
  have hti : IntervalIntegrable (fun t ↦ t*(η.coeff t-γ.coeff t)) volume 0 1 := by
    simpa only [mul_sub] using η.weighted_intervalIntegrable.sub γ.weighted_intervalIntegrable
  have hlim := ((tail_integral_tendsto_zero hAi).const_mul (3/2 : ℝ)).add
    ((integral_primitive_terminal hqi).const_mul (1/2 : ℝ))
  have hh := ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
    exact hγ.compact_variation_inequality hX η hT.1 hT.2)
  have heq : (∫ t in (0 : ℝ)..1,(η.coeff t-γ.coeff t)*(gradientMoment W γ X t-t))=
      (∫ t in (0 : ℝ)..1,(η.coeff t-γ.coeff t)*gradientMoment W γ X t)-
        (∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t)) := by
    rw [←intervalIntegral.integral_sub hqi hti]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [heq]
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_ContactVariations
attribute [-instance] _root_.OAI.SKValue.OrderParameter.truncatedMass_finite _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma OrderParameter.removeBelow_sub (γ : OrderParameter) (c t : ℝ) :
    (γ.removeBelow c).coeff t-γ.coeff t= -min (γ.coeff t) c := by
  dsimp only [OrderParameter.removeBelow]
  by_cases h : γ.coeff t ≤ c
  · rw [max_eq_right (sub_nonpos.mpr h),min_eq_left h]; ring
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge h)),min_eq_right (le_of_not_ge h)]; ring

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma integral_atom_mul (s : ℝ) (hs : s∈Icc (0 : ℝ) 1) (f : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..1,(OrderParameter.atom s).coeff t*f t)=∫ t in s..1,f t := by
  have he : (fun t ↦ (OrderParameter.atom s).coeff t*f t)=(Ici s).indicator f := by
    funext t
    simp only [OrderParameter.atom,indicator,mem_Ici]
    split_ifs <;> simp
  have hs' : Ici s∩Icc (0 : ℝ) 1=Icc s 1 := by
    ext t
    simp only [mem_inter_iff,mem_Ici,mem_Icc]
    constructor
    · rintro ⟨hst,_,ht1⟩; exact ⟨hst,ht1⟩
    · rintro ⟨hst,ht1⟩; exact ⟨hst,hs.1.trans hst,ht1⟩
  rw [he,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),
    ←integral_Icc_eq_integral_Ioc,integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,hs',
    intervalIntegral.integral_of_le hs.2,integral_Icc_eq_integral_Ioc]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_ContactIntegral
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

lemma IsDiffusion.contact_fubini {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) {T : ℝ}
    (hT : T∈Ico (0 : ℝ) 1) :
    Integrable (contactPotential W γ X) (γ.truncatedMass T hT) ∧
    (∫ s,contactPotential W γ X s ∂γ.truncatedMass T hT)=
      ∫ t in (0 : ℝ)..1,min (γ.coeff t) (γ.coeff T)*(gradientMoment W γ X t-t) := by
  let μ := γ.truncatedMass T hT
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  let F : ℝ×ℝ → ℝ := {p : ℝ×ℝ | p.1≤p.2}.indicator (fun p ↦ gradientMoment W γ X p.2-p.2)
  have hi : Integrable (fun t ↦ gradientMoment W γ X t-t) ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mp hX.moment_difference_integrable
  have hF : Integrable F (μ.prod ν) := by
    apply Integrable.of_bound (hi.aestronglyMeasurable.comp_snd.indicator
      (measurableSet_le measurable_fst measurable_snd)) 1
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (μ := volume) measurableSet_Ioc)] with p hp
    by_cases hs : p.1≤p.2
    · rw [indicator_of_mem (show p∈{a : ℝ×ℝ | a.1≤a.2} from hs),Real.norm_eq_abs]
      apply abs_le.mpr
      have h0 := gradientMoment_nonneg W γ X p.2
      have h1 := (abs_le.mp (gradientMoment_bound W γ X ⟨hp.1.le,hp.2⟩)).2
      constructor <;> linarith [hp.1,hp.2]
    · rw [indicator_of_notMem (show p∉{a : ℝ×ℝ | a.1≤a.2} from hs),norm_zero]; norm_num
  have hleft : (fun s ↦ ∫ t,F (s,t) ∂ν)=ᵐ[μ] contactPotential W γ X := by
    filter_upwards [γ.truncatedMass_ae_mem hT] with s hs
    have hs' : s∈Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans hT.2.le⟩
    change (∫ t in Ioc (0 : ℝ) 1,F (s,t))=contactPotential W γ X s
    rw [←intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
    calc
      (∫ t in (0 : ℝ)..1,F (s,t))=
          ∫ t in (0 : ℝ)..1,(OrderParameter.atom s).coeff t*(gradientMoment W γ X t-t) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [F,OrderParameter.atom,indicator]
        split_ifs <;> simp
      _=contactPotential W γ X s := integral_atom_mul s hs' _
  have hright : (fun t ↦ ∫ s,F (s,t) ∂μ)=ᵐ[ν]
      (fun t ↦ min (γ.coeff t) (γ.coeff T)*(gradientMoment W γ X t-t)) := by
    have hν : ∀ᵐ t ∂ν,t∈Ico (0 : ℝ) 1 := by
      dsimp [ν]
      rw [←restrict_Ico_eq_restrict_Ioc]
      exact ae_restrict_mem measurableSet_Ico
    filter_upwards [hν] with t ht
    have he : (fun s ↦ F (s,t))=(Iic t).indicator (fun _ ↦ gradientMoment W γ X t-t) := rfl
    rw [he,integral_indicator measurableSet_Iic,integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,μ,γ.truncatedMass_cdf hT ht,
      ENNReal.toReal_ofReal (le_min (γ.nonneg t ht) (γ.nonneg T hT)),smul_eq_mul]
  refine ⟨hF.integral_prod_left.congr hleft,?_⟩
  rw [←integral_congr_ae hleft]
  have hswap := integral_integral_swap (f := fun s t ↦ F (s,t)) hF
  rw [hswap,integral_congr_ae hright]
  exact (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)).symm

lemma IsMinimizer.contactPotential_ae_zero {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    {T : ℝ} (hT : T∈Ico (0 : ℝ) 1) :
    ∀ᵐ s ∂γ.truncatedMass T hT,contactPotential W γ X s=0 := by
  have hh := hγ.variation_inequality hX (γ.removeBelow (γ.coeff T))
  simp_rw [γ.removeBelow_sub,neg_mul] at hh
  rw [intervalIntegral.integral_neg] at hh
  obtain ⟨hi,he⟩ := hX.contact_fubini hT
  have hnn : 0≤ᵐ[γ.truncatedMass T hT] contactPotential W γ X := by
    filter_upwards [γ.truncatedMass_ae_mem hT] with s hs
    exact hγ.contactPotential_nonneg hX ⟨hs.1,hs.2.trans hT.2.le⟩
  apply (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp
  have hpos := integral_nonneg_of_ae hnn
  rw [he] at hpos ⊢
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_ContactOrigin
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue
lemma IsMinimizer.contact_origin_of_positive_oai {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hγ:IsMinimizer W γ) (hX:IsDiffusion W γ X) (hc:0<γ.coeff 0):contactPotential W γ X 0=0 := by
  have hz:=hγ.contactPotential_ae_zero hX (T:=0) (by constructor <;> norm_num)
  have hh:∀ᵐ s ∂(ENNReal.ofReal (γ.coeff 0) • Measure.dirac (0:ℝ)),contactPotential W γ X s=0 := by
    simpa only [OrderParameter.truncatedMass,Ioc_self,Measure.restrict_empty,zero_add] using hz
  have ha:∀ᵐ s ∂Measure.dirac (0:ℝ),contactPotential W γ X s=0 := by
    exact (Measure.ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hc))).mp hh
  simpa only [ae_dirac_eq, Filter.eventually_pure] using ha
end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsMinimizer.contact_origin_of_positive_oai := @OAI.SKValue.IsMinimizer.contact_origin_of_positive_oai
