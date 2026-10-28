-- Prove2me | solution 1 for OAI.SKValue.value_consequences
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:09:53.202998+00:00
-- url     : https://prove2.me/submissions/f6f7a759-14dc-4f71-867a-399118e5fe47

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_IsDiffusion_finite_gaussian_fixed_strip
import Theorems.Thm_OAI_SKValue_IsDiffusion_parisi_value_assembly
import Theorems.Thm_OAI_SKValue_IsMinimizer_gradient_moment_contact
import Theorems.Thm_OAI_SKValue_phi_evolution
import Theorems.Thm_OAI_SKValue_shiftedCoefficientSum_le_groundState
import Theorems.Thm_OAI_SKValue_smoothApprox_tendsto
import Theorems.Thm_OAI_SKValue_sourceStripRegularity
import Theorems.Thm_OAI_SKValueG_weak_profile_guerra_upper

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

lemma square_difference_bound {x y K L e : ℝ}
    (_hK : 0≤K) (hL : 0≤L) (he : 0≤e)
    (hx : |x|≤K) (hy : |y|≤K) (hxy : |x-y|≤L*e) :
    |x^2-y^2| ≤ (2*K*L)*e := by
  have hs : |x+y|≤2*K := (abs_add_le _ _).trans (by linarith)
  calc
    |x^2-y^2| = |x-y| * |x+y| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (L*e)*(2*K) := mul_le_mul hxy hs (abs_nonneg _) (mul_nonneg hL he)
    _ = _ := by ring

lemma second_moment_perturbation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g e : Ω → ℝ} {K L : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (he : MemLp e 2 μ)
    (hK : 0≤K) (hL : 0≤L)
    (hbound : ∀ᵐ ω ∂μ, |f ω|≤K ∧ |g ω|≤K ∧ |f ω-g ω|≤L*|e ω|) :
    |(∫ ω, (f ω)^2 ∂μ)-(∫ ω, (g ω)^2 ∂μ)| ≤
      (2*K*L)*Real.sqrt (∫ ω, (e ω)^2 ∂μ) := by
  have hfi : Integrable (fun ω ↦ (f ω)^2) μ := hf.integrable_sq
  have hgi : Integrable (fun ω ↦ (g ω)^2) μ := hg.integrable_sq
  have hei : Integrable (fun ω ↦ |e ω|) μ := by
    simpa only [Real.norm_eq_abs] using (he.integrable (by norm_num : (1 : ENNReal)≤2)).norm
  calc
    _ = |∫ ω, (f ω)^2-(g ω)^2 ∂μ| := by rw [integral_sub hfi hgi]
    _ ≤ ∫ ω, |(f ω)^2-(g ω)^2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (2*K*L)*|e ω| ∂μ := by
      apply integral_mono_ae
      · exact (hfi.sub hgi).abs
      · exact hei.const_mul _
      · filter_upwards [hbound] with ω hω
        exact square_difference_bound hK hL (abs_nonneg _) hω.1 hω.2.1 hω.2.2
    _ = (2*K*L)*(∫ ω, |e ω| ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq he) (by positivity)

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

lemma GradientStrip.measurable_second {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (h : GradientStrip T γ u K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    Measurable (deriv (deriv (u t))) := by
  have hc := (h.smooth t ht).continuous_iteratedDeriv 2 (by norm_num)
  simpa only [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hc.measurable

lemma gradientMeshError_nonneg (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    0≤gradientMeshError T N γ u := integral_nonneg (fun _ ↦ sq_nonneg _)

lemma gradientMeshError_bound {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    gradientMeshError T N γ u ≤
      2*((stepSize T N/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(stepSize T N*Real.sqrt (stepSize T N))^2*(N : ℝ)^2*
        cubicEnvelopeMoment (γ T) K ((1/2+γ T)*L)+
      4*(stepSize T N*K*(γ T-γ 0))^2 := by
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
  have hUm (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) :=
    (h.smooth _ (htime j hj)).continuous.measurable.comp
      (measurable_euler T N γ u (fun k hk ↦ (h.smooth _ (htime k hk.le)).continuous.measurable) j hj)
  have hY (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ euler T N γ u z j) :=
    measurable_euler T N γ u (fun k hk ↦ (h.smooth _ (htime k hk.le)).continuous.measurable) j hj
  have hAm (i : Fin N) : Measurable (fun z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i)) :=
    ((h.smooth _ (htime i i.isLt.le)).continuous_deriv (by norm_num)).measurable.comp (hY i i.isLt.le)
  have hHm (i : Fin N) : Measurable (fun z ↦ deriv (deriv (u (meshTime T N i))) (euler T N γ u z i)) :=
    (h.measurable_second (htime i i.isLt.le)).comp (hY i i.isLt.le)
  have hloc (i : Fin N) (z : Fin (N+1) → ℝ) :
      |u (meshTime T N (i+1)) (euler T N γ u z (i+1))-
        u (meshTime T N i) (euler T N γ u z i)-
        Real.sqrt δ*deriv (u (meshTime T N i)) (euler T N γ u z i)*coordinate N i z-
        (δ/2)*deriv (deriv (u (meshTime T N i))) (euler T N γ u z i)*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N i z)+
        δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [← hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hbint (x : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (u s)) x) volume t (t+δ) := by
      apply (h.second_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hpint (x : ℝ) : IntervalIntegrable (fun s ↦ γ s*(u s x*deriv (u s) x)) volume t (t+δ) := by
      apply (h.product_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hh := gradient_euler_one_step (x := euler T N γ u z i) (z := coordinate N i z)
      hδ hδ1 hG h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub) (h.gamma_nonneg t ht)
      (h.gamma_mono ht htT ht.2) (h.bounded t ht _) (h.smooth t ht)
      (h.second_bound t ht _) (h.third_bound t ht)
      (fun s hs ↦ h.product_bound s (hsub hs))
      (fun s hs y ↦ h.second_lipschitz t ht s (hsub hs) _ y)
      (fun s hs y ↦ h.product_lipschitz t ht s (hsub hs) _ y)
      hbint hpint (h.pde t ht (t+δ) ht')
    dsimp only at hh
    simpa only [hsucc, euler, cubicEnvelope, t, δ, add_assoc, mul_assoc,
      mul_left_comm, mul_comm, div_eq_mul_inv, one_mul] using hh
  have hb := discrete_gradient_residual_L2 (δ := δ) hδ hG h.K_nonneg
    (mul_nonneg (by positivity) h.L_nonneg : 0≤(1/2+γ T)*L)
    (Γ := fun j ↦ γ (meshTime T N j))
    (U := fun j z ↦ u (meshTime T N j) (euler T N γ u z j))
    (A := fun i z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i))
    (H := fun i z ↦ deriv (deriv (u (meshTime T N i))) (euler T N γ u z i))
    (by simpa only [hlast, hzero] using h.gamma_mono ht0 htT hT.le)
    hUm hAm hHm
    (fun i ↦ eulerCoefficient_dependsBefore T i.isLt.le γ u (fun t ↦ deriv (deriv (u t))))
    (fun i z ↦ h.second_bound _ (htime i i.isLt.le) _) hloc
  simpa only [gradientMeshError, hlast, hzero, euler, h.initial,
    sub_zero, δ] using hb

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

lemma gradientMeshError_bound_linear {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    gradientMeshError T N γ u ≤ stepSize T N*gradientErrorConstant T K L γ := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hδ : 0≤ stepSize T N := div_nonneg hT.le hNr.le
  have hδ1 : stepSize T N≤1 := (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hm : (N:ℝ)*stepSize T N=T := by unfold stepSize; field_simp
  exact (gradientMeshError_bound hT hT1 h hN).trans (gaussian_mesh_bound_linear hδ hδ1 hm)

theorem gradientMeshError_tendsto_zero {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) :
    Tendsto (fun N ↦ gradientMeshError T N γ u) atTop (𝓝 0) := by
  have hbound : ∀ᶠ N in atTop,
      gradientMeshError T N γ u≤ stepSize T N*gradientErrorConstant T K L γ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact gradientMeshError_bound_linear hT hT1 h hN
  have hlim : Tendsto (fun N ↦ stepSize T N*gradientErrorConstant T K L γ) atTop (𝓝 0) := by
    simpa only [stepSize, zero_mul] using
      (tendsto_const_div_atTop_nhds_zero_nat T).mul_const (gradientErrorConstant T K L γ)
  exact squeeze_zero' (Eventually.of_forall (fun N ↦ gradientMeshError_nonneg T N γ u)) hbound hlim

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

lemma mesh_terminal_measurable {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    Measurable (meshTerminal T N γ u) :=
  (h.smooth T ⟨hT,le_rfl⟩).continuous.measurable.comp
    (measurable_euler T N γ u (fun _ hj ↦
      (h.smooth _ (mesh_time_mem hT hN hj.le)).continuous.measurable) N le_rfl)

lemma mesh_raw_measurable {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    Measurable (meshRaw T N γ u j) :=
  ((h.smooth _ (mesh_time_mem hT hN hj)).continuous_deriv (by norm_num)).measurable.comp
    (measurable_euler T N γ u (fun k hk ↦
      (h.smooth _ (mesh_time_mem hT hN hk.le)).continuous.measurable) j hj)

lemma mesh_raw_depends (T : ℝ) {N j : ℕ} (hj : j≤N) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) :
    DependsBefore j (meshRaw T N γ u j) :=
  eulerCoefficient_dependsBefore T hj γ u (fun t ↦ deriv (u t))

lemma mesh_raw_memLp {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j≤N) :
    MemLp (meshRaw T N γ u j) 2 (gaussianProduct (Fin (N+1))) := by
  have := gaussianProduct_probability (Fin (N+1))
  apply MemLp.of_bound (mesh_raw_measurable hT h hN hj).aestronglyMeasurable D
  exact Eventually.of_forall (fun z ↦ by
    simpa only [meshRaw, Real.norm_eq_abs] using hD _ (mesh_time_mem hT hN hj) (euler T N γ u z j))

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
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_UniformGridRiemannBound
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

lemma uniform_grid_riemann_bound {f : ℝ → ℝ} {T δ ε : ℝ} {N : ℕ}
    (hδ : 0≤δ) (horizon : (N : ℝ)*δ=T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hmod : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      |s-t|≤δ → |f s-f t|≤ε) :
    |δ*(∑ j ∈ Finset.range N, f ((j : ℝ)*δ))-∫ t in (0 : ℝ)..T, f t| ≤ T*ε := by
  have hT : 0≤T := by rw [←horizon]; positivity
  have hm : ∀ j≤N, (j : ℝ)*δ∈Icc (0 : ℝ) T := by
    intro j hj
    constructor
    · positivity
    · rw [←horizon]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
  have hs : ∀ j<N, Icc ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ)⊆Icc (0 : ℝ) T := by
    intro j hj t ht
    exact ⟨(hm j (by omega)).1.trans ht.1, ht.2.trans (hm (j+1) (by omega)).2⟩
  have hjle : ∀ j : ℕ, (j : ℝ)*δ≤((j+1 : ℕ) : ℝ)*δ := by
    intro j
    push_cast
    nlinarith
  have hint : ∀ j<N, IntervalIntegrable f volume ((j : ℝ)*δ) (((j+1 : ℕ) : ℝ)*δ) := by
    intro j hj
    apply (hf.mono (hs j hj)).intervalIntegrable_of_Icc (hjle j)
  have heq : (∑ j ∈ Finset.range N, ∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t) =
      ∫ t in (0 : ℝ)..T, f t := by
    simpa only [Nat.cast_zero, zero_mul, horizon] using intervalIntegral.sum_integral_adjacent_intervals hint
  have hloc : ∀ j<N, |δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t|≤δ*ε := by
    intro j hj
    have hc : (∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f ((j : ℝ)*δ)-f t) =
        δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint j hj), intervalIntegral.integral_const]
      simp only [Nat.cast_add, Nat.cast_one, smul_eq_mul]
      ring
    rw [←hc]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (j : ℝ)*δ) (b := ((j+1 : ℕ) : ℝ)*δ) (C := ε)
      (f := fun t ↦ f ((j : ℝ)*δ)-f t)
      (fun t ht ↦ by
        rw [uIoc_of_le (hjle j)] at ht
        rw [Real.norm_eq_abs]
        apply hmod _ (hm j (by omega)) t (hs j hj ⟨ht.1.le,ht.2⟩)
        rw [abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
        push_cast at ht
        nlinarith [ht.2])
    have hwidth : (((j+1 : ℕ) : ℝ)*δ)-(j : ℝ)*δ=δ := by push_cast; ring
    simp only [Real.norm_eq_abs, hwidth, abs_of_nonneg hδ] at hb
    simpa only [mul_comm] using hb
  calc
    _ = |∑ j ∈ Finset.range N, (δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t)| := by
      rw [Finset.sum_sub_distrib, ←Finset.mul_sum, heq]
    _ ≤ ∑ j ∈ Finset.range N, |δ*f ((j : ℝ)*δ)-∫ t in ((j : ℝ)*δ)..(((j+1 : ℕ) : ℝ)*δ), f t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, δ*ε := Finset.sum_le_sum (fun j hj ↦ hloc j (Finset.mem_range.mp hj))
    _ = T*ε := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ←mul_assoc, horizon]

lemma uniform_grid_riemann_tendsto {f : ℝ → ℝ} {T : ℝ} (hT : 0<T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    Tendsto (fun N : ℕ ↦ (T/N)*(∑ j ∈ Finset.range N, f ((j : ℝ)*(T/N))))
      atTop (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε/(2*T)) (div_pos hε (by positivity))
  have hδ : Tendsto (fun N : ℕ ↦ T/N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  filter_upwards [hδ.eventually_le_const hθ, eventually_gt_atTop 0] with N hNθ hN
  have horizon : (N : ℝ)*(T/N) = T := by field_simp
  have h := uniform_grid_riemann_bound (div_nonneg hT.le (Nat.cast_nonneg _)) horizon hf
    (fun s hs t ht hst ↦ by
      simpa only [Real.dist_eq] using hmod s hs t ht (by simpa only [Real.dist_eq] using hst.trans hNθ))
  rw [Real.dist_eq]
  apply h.trans_lt
  have : T*(ε/(2*T))=ε/2 := by field_simp
  rw [this]
  exact half_lt_self hε

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

lemma rawIncrement_variance {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H) :
    (∫ z, (rawIncrement H j z)^2 ∂gaussianProduct (Fin (N+1))) =
      ∫ z, (H z)^2 ∂gaussianProduct (Fin (N+1)) := by
  have hind := (hp.independent hj hm).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hi := hind.integral_mul_eq_mul_integral
    (hm.pow_const 2).aestronglyMeasurable ((measurable_coordinate N j).pow_const 2).aestronglyMeasurable
  change (∫ z, (H z)^2 * (coordinate N j z)^2 ∂gaussianProduct (Fin (N+1))) = (∫ z, (H z)^2 ∂gaussianProduct (Fin (N+1))) *
      (∫ z, (coordinate N j z)^2 ∂gaussianProduct (Fin (N+1))) at hi
  simp only [rawIncrement, mul_pow]
  rw [hi, gaussian_second_moment (coordinate_hasLaw N j), mul_one]

lemma rawIncrement_depends {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hp : DependsBefore j H) : DependsBefore (j+1) (rawIncrement H j) := by
  intro z z' hz
  dsimp only [rawIncrement]
  rw [hp z z' (fun i hi ↦ hz i (by omega)), coordinate_eq_apply hj, coordinate_eq_apply hj,
    hz ⟨j,hj⟩ (by simp)]

lemma rawIncrement_past_product {N j : ℕ} {H F : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (fm : Measurable F)
    (hp : DependsBefore j H) (fp : DependsBefore j F) :
    (∫ z, F z * rawIncrement H j z ∂gaussianProduct (Fin (N+1)))=0 := by
  have hi := ((fp.mul hp).independent hj (fm.mul hm)).integral_mul_eq_mul_integral
    (fm.mul hm).aestronglyMeasurable (measurable_coordinate N j).aestronglyMeasurable
  change (∫ z, (F z*H z)*coordinate N j z ∂gaussianProduct (Fin (N+1)))=_ at hi
  simp only [rawIncrement, ←mul_assoc]
  rw [hi, gaussian_mean (coordinate_hasLaw N j), mul_zero]

lemma rawIncrement_pair {N : ℕ} {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (i j : Fin N) (hij : i ≠ j) :
    (∫ z, rawIncrement (H i) i z * rawIncrement (H j) j z
      ∂gaussianProduct (Fin (N+1)))=0 := by
  rcases lt_or_gt_of_ne hij with hij|hij
  · exact rawIncrement_past_product (by omega) (hm j)
      ((hm i).mul (measurable_coordinate N i)) (hp j)
      ((rawIncrement_depends (by omega) (hp i)).mono (by exact Nat.succ_le_of_lt hij))
  · rw [show (fun z ↦ rawIncrement (H i) i z * rawIncrement (H j) j z) =
        (fun z ↦ rawIncrement (H j) j z * rawIncrement (H i) i z) by funext z; ring]
    exact rawIncrement_past_product (by omega) (hm i)
      ((hm j).mul (measurable_coordinate N j)) (hp i)
      ((rawIncrement_depends (by omega) (hp j)).mono (by exact Nat.succ_le_of_lt hij))

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

lemma finiteRaw_isometry {N : ℕ} {δ : ℝ} (hδ : 0≤δ)
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) :
    (∫ z, (finiteRawMartingale δ H z)^2 ∂gaussianProduct (Fin (N+1))) =
      δ * ∑ i : Fin N, ∫ z, (H i z)^2 ∂gaussianProduct (Fin (N+1)) := by
  have hm' (i : Fin N) := (rawIncrement_memLp (by omega) (hm i) (hp i) (hH i)).const_mul (Real.sqrt δ)
  have ho : ∀ i j : Fin N, i≠j →
      (∫ z, (Real.sqrt δ*rawIncrement (H i) i z)*(Real.sqrt δ*rawIncrement (H j) j z)
        ∂gaussianProduct (Fin (N+1)))=0 := by
    intro i j hij
    simp_rw [show ∀ a b : ℝ, (Real.sqrt δ*a)*(Real.sqrt δ*b)=δ*(a*b) by
      intro a b
      rw [show (Real.sqrt δ*a)*(Real.sqrt δ*b)=(Real.sqrt δ)^2*(a*b) by ring, Real.sq_sqrt hδ]]
    rw [integral_const_mul, rawIncrement_pair hm hp i j hij, mul_zero]
  have heq := orthogonal_sum_square hm' ho
  simp only [finiteRawMartingale, ←mul_assoc, rawIncrement] at heq ⊢
  rw [heq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc, mul_pow, Real.sq_sqrt hδ, integral_const_mul]
  congr 1
  simpa only [rawIncrement, mul_pow] using rawIncrement_variance (by omega) (hm i) (hp i)

lemma coupled_mesh_general_moment_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hD0 : 0≤D) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (hLip : ∀ t∈Icc (0 : ℝ) T, ∀ x y, |deriv (u t) x-deriv (u t) y|≤La*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) (j : Fin N) :
    |(∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))-
      (∫ ω, (deriv (u (meshTime T N j)) (X (meshTime T N j) ω))^2 ∂μ)|≤
      (2*D*La)*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) ∧
    |(∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))-
      ∫ ω, deriv (u (meshTime T N j)) (X (meshTime T N j) ω) ∂μ|≤
      La*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let t := meshTime T N j
  let F (ω : Ω) := deriv (u t) (coupledEuler T γ u B N j ω)
  let G (ω : Ω) := deriv (u t) (X t ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht : t∈Icc (0 : ℝ) T := mesh_time_mem hT.le hN j.isLt.le
  have hd : Continuous (deriv (u t)) := (h.smooth t ht).continuous_deriv (by norm_num)
  have hFM : MemLp F 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (coupled_euler_measurable hB hT h N j j.isLt.le).aemeasurable).aestronglyMeasurable D
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, F] using hD t ht _))
  have hGM : MemLp G 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (hXM t ht).aemeasurable).aestronglyMeasurable D
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, G] using hD t ht _))
  have hEM : MemLp E 2 μ := coupled_mesh_error_memLp hB hT h hXM hpaths hN
  have hFG (ω : Ω) : |F ω-G ω|≤La*|E ω| := by
    have he : |coupledEuler T γ u B N j ω-X t ω|≤E ω :=
      le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) j.isLt.le
    calc
      _ ≤ La*|coupledEuler T γ u B N j ω-X t ω| := hLip t ht _ _
      _ ≤ La*(E ω) := mul_le_mul_of_nonneg_left he hLa
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) hLa
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have hmraw := mesh_raw_measurable hT.le h hN j.isLt.le
  have heq1 : (∫ z, meshRaw T N γ u j z ∂gaussianProduct (Fin (N+1)))=∫ ω, F ω ∂μ := by
    rw [←hlaw.integral_comp hmraw.aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshRaw, t, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  have heq2 : (∫ z, (meshRaw T N γ u j z)^2 ∂gaussianProduct (Fin (N+1)))=∫ ω, (F ω)^2 ∂μ := by
    rw [←hlaw.integral_comp (hmraw.pow_const 2).aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshRaw, t, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  constructor
  · rw [heq2]
    exact second_moment_perturbation hFM hGM hEM hD0 hLa
      (Eventually.of_forall (fun ω ↦ ⟨hD t ht _,hD t ht _,hFG ω⟩))
  · rw [heq1]
    exact first_moment_perturbation hFM hGM hEM hLa (Eventually.of_forall hFG)

lemma integral_product_CS {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω*g ω ∂μ| ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g) hp
    (by simpa using hf) (by simpa using hg)
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ←Real.sqrt_eq_rpow] at hh
  exact (abs_integral_le_integral_abs.trans_eq
    (integral_congr_ae (Eventually.of_forall (fun _ ↦ abs_mul _ _)))).trans hh

lemma second_moment_L2_perturbation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} {C : ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hC : (∫ ω, (f ω)^2 ∂μ)+(∫ ω, (g ω)^2 ∂μ)≤C) :
    |(∫ ω, (f ω)^2 ∂μ)-(∫ ω, (g ω)^2 ∂μ)| ≤
      Real.sqrt (∫ ω, (f ω-g ω)^2 ∂μ) * Real.sqrt (2*C) := by
  have heq : (∫ ω, (f ω)^2 ∂μ)-(∫ ω, (g ω)^2 ∂μ)=
      ∫ ω, (f ω-g ω)*(f ω+g ω) ∂μ := by
    rw [←integral_sub hf.integrable_sq hg.integrable_sq]
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ ↦ by ring)
  rw [heq]
  apply (integral_product_CS (hf.sub hg) (hf.add hg)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∫ ω, 2*(f ω)^2+2*(g ω)^2 ∂μ := by
      apply integral_mono (hf.add hg).integrable_sq
        ((hf.integrable_sq.const_mul 2).add (hg.integrable_sq.const_mul 2))
      intro ω
      dsimp only [Pi.add_apply]
      nlinarith [sq_nonneg (f ω-g ω)]
    _ = 2*((∫ ω, (f ω)^2 ∂μ)+(∫ ω, (g ω)^2 ∂μ)) := by
      rw [integral_add (hf.integrable_sq.const_mul 2) (hg.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]
      ring
    _ ≤ 2*C := by linarith

lemma perturbed_grid_riemann_tendsto {f : ℝ → ℝ} {T : ℝ}
    {v : (N : ℕ) → Fin N → ℝ} {r : ℕ → ℝ}
    (hT : 0<T) (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hr0 : Tendsto r atTop (𝓝 0))
    (hv : ∀ᶠ N in atTop, ∀ i : Fin N, |v N i-f ((i : ℕ)*(T/N))| ≤ r N) :
    Tendsto (fun N : ℕ ↦ (T/N)*(∑ i : Fin N, v N i)) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
  have herr : Tendsto (fun N : ℕ ↦ (T/N)*(∑ i : Fin N, v N i)-
      (T/N)*(∑ i : Fin N, f ((i : ℕ)*(T/N)))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦ T*r N)
    · filter_upwards [hv, eventually_gt_atTop 0] with N hNv hN
      have hδ : 0≤T/(N : ℝ) := div_nonneg hT.le (Nat.cast_nonneg _)
      have hmul : (T/(N : ℝ))*(N : ℝ)=T := by field_simp
      rw [Real.norm_eq_abs, ←mul_sub, ←Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hδ]
      calc
        _ ≤ (T/N)*(∑ _ : Fin N, r N) := by
          apply mul_le_mul_of_nonneg_left _ hδ
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ ↦ hNv i))
        _ = T*r N := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ←mul_assoc, hmul]
    · simpa only [mul_zero] using hr0.const_mul T
  have hR : Tendsto (fun N : ℕ ↦ (T/N)*(∑ i : Fin N, f ((i : ℕ)*(T/N)))) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, f t)) := by
    convert uniform_grid_riemann_tendsto hT hf using 1
    all_goals try with_reducible_and_instances rfl
    funext N
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ f ((j : ℝ)*(T/N)))]
  simpa only [sub_add_cancel, zero_add] using herr.add hR

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

lemma mesh_terminal_memLp {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0≤T) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    MemLp (meshTerminal T N γ u) 2 (gaussianProduct (Fin (N+1))) := by
  apply MemLp.of_bound (mesh_terminal_measurable hT h hN).aestronglyMeasurable 1
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs, meshTerminal] using h.bounded T ⟨hT,le_rfl⟩ _)

lemma bounded_second_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {D : ℝ} (hf : MemLp f 2 μ)
    (hD : 0≤D) (hb : ∀ᵐ ω ∂μ, |f ω|≤D) : (∫ ω, (f ω)^2 ∂μ)≤D^2 := by
  calc
    _ ≤ ∫ _ : Ω, D^2 ∂μ := by
      apply integral_mono_ae hf.integrable_sq (integrable_const _)
      filter_upwards [hb] with ω hω
      nlinarith [sq_abs (f ω), abs_nonneg (f ω)]
    _ = _ := by simp

lemma mesh_raw_stochastic_square_bound {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hD0 : 0≤D)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) :
    (∫ z, (finiteRawMartingale (stepSize T N) (fun i : Fin N ↦ meshRaw T N γ u i) z)^2
      ∂gaussianProduct (Fin (N+1))) ≤ T*D^2 := by
  have hδ : 0 ≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg _)
  rw [finiteRaw_isometry hδ (fun i ↦ mesh_raw_measurable hT.le h hN i.isLt.le)
    (fun i ↦ mesh_raw_depends T i.isLt.le γ u)
    (fun i ↦ mesh_raw_memLp hT.le h hD hN i.isLt.le)]
  calc
    _ ≤ stepSize T N * ∑ _ : Fin N, D^2 := by
      apply mul_le_mul_of_nonneg_left _ hδ
      apply Finset.sum_le_sum
      intro i _
      exact bounded_second_moment (mesh_raw_memLp hT.le h hD hN i.isLt.le) hD0
        (Eventually.of_forall (fun z ↦ hD _ (mesh_time_mem hT.le hN i.isLt.le) _))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, stepSize]
      field_simp

lemma mesh_terminal_stochastic_second_moment_error {T K L D : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hD0 : 0≤D)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    {N : ℕ} (hN : 0<N) :
    |(∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))-
      (stepSize T N)*∑ i : Fin N, ∫ z, (meshRaw T N γ u i z)^2 ∂gaussianProduct (Fin (N+1))|≤
      Real.sqrt (gradientMeshError T N γ u) * Real.sqrt (2*(1+T*D^2)) := by
  have hU := mesh_terminal_memLp hT.le h hN
  have hR := finiteRaw_memLp (δ := stepSize T N)
    (fun i : Fin N ↦ mesh_raw_measurable hT.le h hN i.isLt.le)
    (fun i : Fin N ↦ mesh_raw_depends T i.isLt.le γ u)
    (fun i : Fin N ↦ mesh_raw_memLp hT.le h hD hN i.isLt.le)
  have hU2 : (∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))≤1 := by
    simpa only [one_pow] using bounded_second_moment hU (by norm_num : (0 : ℝ)≤1)
      (Eventually.of_forall (fun z ↦ h.bounded T ⟨hT.le,le_rfl⟩ _))
  have hR2 := mesh_raw_stochastic_square_bound hT h hD0 hD hN
  have herr := second_moment_L2_perturbation hU hR (add_le_add hU2 hR2)
  have hδ : 0 ≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg _)
  rw [finiteRaw_isometry hδ (fun i : Fin N ↦ mesh_raw_measurable hT.le h hN i.isLt.le)
    (fun i : Fin N ↦ mesh_raw_depends T i.isLt.le γ u)
    (fun i : Fin N ↦ mesh_raw_memLp hT.le h hD hN i.isLt.le)] at herr
  exact herr

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

lemma terminalTime_mem (n : ℕ) : terminalTime n ∈ Ico (0 : ℝ) 1 := by
  have hn : (1 : ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : (0 : ℝ) < n+1 := by positivity
  simp only [terminalTime]
  constructor
  · have hh : (1 : ℝ)/(n+1) ≤ 1 := (div_le_one hp).mpr hn
    linarith
  · have hh : (0 : ℝ) < 1/(n+1) := by positivity
    linarith

lemma terminalTime_tendsto : Tendsto terminalTime atTop (𝓝[<] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall (fun n ↦ (terminalTime_mem n).2)⟩
  change Tendsto (fun n : ℕ ↦ (1 : ℝ)-1/((n : ℝ)+1)) atTop (𝓝 (1 : ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshBrownian
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

lemma coupled_terminal_second_moment_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L Lu : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : GradientStrip T γ u K L) (hLu : 0≤Lu)
    (huLip : ∀ x y, |u T x-u T y|≤Lu*|x-y|)
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ,
      (∀ t∈Icc (0 : ℝ) T, X t ω=B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0)
    {N : ℕ} (hN : 0<N) :
    |(∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))-
      (∫ ω, (u T (X T ω))^2 ∂μ)| ≤
      (2*Lu)*Real.sqrt (∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let F (ω : Ω) := u T (coupledEuler T γ u B N N ω)
  let G (ω : Ω) := u T (X T ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hd := (h.smooth T ht).continuous
  have hFM : MemLp F 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (coupled_euler_measurable hB hT h N N le_rfl).aemeasurable).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, F] using h.bounded T ht _))
  have hGM : MemLp G 2 μ := MemLp.of_bound
    (hd.measurable.comp_aemeasurable (hXM T ht).aemeasurable).aestronglyMeasurable 1
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs, G] using h.bounded T ht _))
  have hEM : MemLp E 2 μ := coupled_mesh_error_memLp hB hT h hXM hpaths hN
  have hlast : meshTime T N N = T := by dsimp [meshTime, stepSize]; field_simp
  have hFG (ω : Ω) : |F ω-G ω|≤Lu*|E ω| := by
    have he : |coupledEuler T γ u B N N ω-X T ω|≤E ω := by
      change |coupledEuler T γ u B N N ω-X T ω| ≤ initialMax _ N
      have hm := le_initialMax (f := fun k ↦ |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) (le_refl N)
      change |coupledEuler T γ u B N N ω-X (meshTime T N N) ω| ≤ initialMax _ N at hm
      rw [hlast] at hm
      exact hm

    exact (huLip _ _).trans (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) hLu)
  have hlaw := coupledCoordinates_hasLaw hB hT hN
  have heq : (∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))=∫ ω, (F ω)^2 ∂μ := by
    rw [←hlaw.integral_comp ((mesh_terminal_measurable hT.le h hN).pow_const 2).aestronglyMeasurable]
    simp only [Function.comp_apply, F, meshTerminal, coupledEuler, ite_eq_right (Nat.ne_of_gt hN)]
  rw [heq]
  simpa only [mul_one] using second_moment_perturbation hFM hGM hEM (by norm_num : (0 : ℝ)≤1) hLu
    (Eventually.of_forall (fun ω ↦ ⟨h.bounded T ht _, h.bounded T ht _, hFG ω⟩))

theorem diffusion_gradient_isometry
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    {X : ℝ → Ω → ℝ} {T K L D Lu La : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L)
    (hD0 : 0≤D) (hLu : 0≤Lu) (hLa : 0≤La)
    (hD : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (u t) x|≤D)
    (huLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (haLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |deriv (u s) x-deriv (u t) y|≤La*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (X t) μ)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0 : ℝ) T, X t ω = B (Real.toNNReal t) ω+
        ∫ s in (0 : ℝ)..t, γ s*u s (X s ω)) ∧ X 0 ω=0) :
    (∫ ω, (u T (X T ω))^2 ∂μ) =
      ∫ t in (0 : ℝ)..T, ∫ ω, (deriv (u t) (X t ω))^2 ∂μ := by
  let E (N : ℕ) := ∫ ω, (meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ
  have hE : Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence hB hT h hLu huLip hXM hpaths
  have hEs : Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hE
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hmoment : Tendsto (fun N ↦ ∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 (∫ ω, (u T (X T ω))^2 ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_
      (by simpa only [mul_zero] using hEs.const_mul (2*Lu))
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Real.norm_eq_abs]
    exact coupled_terminal_second_moment_bound hB hT h hLu
      (fun x y ↦ by simpa only [sub_self, abs_zero, zero_add] using huLip T ht T ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN
  have hmean := mean_derivative_square_continuous hD0 hLa
    (fun t ht ↦ (h.smooth t ht).continuous_deriv (by norm_num)) hD haLip hXM
    (hpaths.mono (fun _ hω ↦ hω.1))
  have hquadrature : Tendsto (fun N ↦ stepSize T N * ∑ i : Fin N,
      ∫ z, (meshRaw T N γ u i z)^2 ∂gaussianProduct (Fin (N+1))) atTop
      (𝓝 (∫ t in (0 : ℝ)..T, ∫ ω, (deriv (u t) (X t ω))^2 ∂μ)) := by
    apply perturbed_grid_riemann_tendsto (r := fun N ↦ (2*D*La)*Real.sqrt (E N)) hT hmean
      (by simpa only [mul_zero] using hEs.const_mul (2*D*La))
    filter_upwards [eventually_gt_atTop 0] with N hN i
    exact (coupled_mesh_general_moment_bounds hB hT h hD0 hLa hD
      (fun t ht x y ↦ by simpa only [sub_self, abs_zero, zero_add] using haLip t ht t ht x y)
      hXM (hpaths.mono (fun _ hω ↦ hω.2.2)) hN i).1
  have herror : Tendsto (fun N ↦
      (∫ z, (meshTerminal T N γ u z)^2 ∂gaussianProduct (Fin (N+1)))-
      stepSize T N * ∑ i : Fin N, ∫ z, (meshRaw T N γ u i z)^2 ∂gaussianProduct (Fin (N+1)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦
      Real.sqrt (gradientMeshError T N γ u) * Real.sqrt (2*(1+T*D^2)))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      rw [Real.norm_eq_abs]
      exact mesh_terminal_stochastic_second_moment_error hT h hD0 hD hN
    · simpa only [Real.sqrt_zero, zero_mul, Function.comp_def] using
        ((Real.continuous_sqrt.tendsto 0).comp (gradientMeshError_tendsto_zero hT hT1 h)).mul_const
          (Real.sqrt (2*(1+T*D^2)))
  have hlimit := herror.add hquadrature
  simp only [sub_add_cancel, zero_add] at hlimit
  exact tendsto_nhds_unique hmoment hlimit

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
-- module Solutions.OAIQ4_Sk.SKValue_Processes_Feedback
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

lemma coupled_euler_past_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, StronglyMeasurable (B t))
    {T : ℝ} (hT : 0<T) {N : ℕ} (hN : 0<N) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ j<N, Measurable (u (meshTime T N j))) :
    ∀ j ≤ N, StronglyMeasurable[Filtration.natural B hBm (Real.toNNReal (meshTime T N j))]
      (coupledEuler T γ u B N j) := by
  let f := Filtration.natural B hBm
  intro j
  induction j with
  | zero =>
    intro _
    convert (stronglyMeasurable_const : StronglyMeasurable[f (Real.toNNReal (meshTime T N 0))] (fun _ : Ω ↦ (0 : ℝ))) using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    exact coupled_euler_zero T γ u B N ω
  | succ j ih =>
    intro hjN
    have hj : j<N := hjN
    have hδ : 0 ≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
    have ht : Real.toNNReal (meshTime T N j) ≤ Real.toNNReal (meshTime T N (j+1)) := by
      apply Real.toNNReal_mono
      apply mul_le_mul_of_nonneg_right _ hδ
      exact_mod_cast Nat.le_succ j
    have hY := (ih hj.le).mono (f.mono ht)
    have hB0 := (Filtration.stronglyAdapted_natural hBm (Real.toNNReal (meshTime T N j))).mono (f.mono ht)
    have hB1 := Filtration.stronglyAdapted_natural hBm (Real.toNNReal (meshTime T N (j+1)))
    have hU := ((hu j hj).comp hY.measurable).stronglyMeasurable.const_mul
      (stepSize T N*γ (meshTime T N j))
    convert ((hY.add hB1).sub hB0).add hU using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    rw [coupled_euler_step B hT γ u hN hj ω]
    rfl

end SKValue

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

lemma log_two_cosh_bounds (z : ℝ) : |z|≤Real.log (2*Real.cosh z) ∧
    Real.log (2*Real.cosh z)≤|z|+Real.log 2 := by
  have he : 2*Real.cosh z=Real.exp z+Real.exp (-z) := by rw [Real.cosh_eq]; ring
  have h1 : Real.exp |z|≤Real.exp z+Real.exp (-z) := by
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
      linarith [Real.exp_pos (-z)]
    · rw [abs_of_nonpos hz]
      linarith [Real.exp_pos z]
  have h2 : Real.exp z+Real.exp (-z)≤2*Real.exp |z| := by
    have hh1 := Real.exp_le_exp.mpr (le_abs_self z)
    have hh2 := Real.exp_le_exp.mpr (neg_le_abs z)
    linarith
  constructor
  · have hh := Real.log_le_log (Real.exp_pos |z|) h1
    simpa only [←he,Real.log_exp] using hh
  · have hh := Real.log_le_log (add_pos (Real.exp_pos z) (Real.exp_pos (-z))) h2
    rw [Real.log_mul (by norm_num) (Real.exp_pos |z|).ne',Real.log_exp,←he] at hh
    linarith

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

lemma OrderParameter.grid_ae_error_bound (γ : OrderParameter) (n : ℕ) :
    ∀ᵐ t ∂volume, t∈Ioc (0 : ℝ) 1 → |profileCoeff (γ.grid n) t-γ.cutoff t| ≤ γ.cutoff t := by
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t hne ht
  have ht' : t∈Ico (0 : ℝ) 1 := ⟨ht.1.le,lt_of_le_of_ne ht.2 hne⟩
  rw [OrderParameter.cutoff,indicator_of_mem ht',abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (γ.grid_le n ht'))]
  linarith [profileCoeff_nonneg (γ.grid n) t]

lemma OrderParameter.gridError_tendsto (γ : OrderParameter) :
    Tendsto γ.gridError atTop (𝓝 0) := by
  have hl := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := 0) (b := 1) (μ := volume) (l := atTop) (f := fun _ : ℝ ↦ (0 : ℝ))
    (F := fun n t ↦ |profileCoeff (γ.grid n) t-γ.cutoff t|) γ.cutoff
    (Eventually.of_forall (fun n ↦ ((profileCoeff_measurable (γ.grid n)).sub γ.cutoff_measurable).abs.aestronglyMeasurable))
    (Eventually.of_forall (fun n ↦ by
      filter_upwards [γ.grid_ae_error_bound n] with t ht ht'
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht'
      simpa only [Real.norm_eq_abs,abs_abs] using ht ht'))
    γ.cutoff_integrable.intervalIntegrable (by
      filter_upwards [γ.grid_ae_tendsto] with t ht ht'
      have hl := ((ht (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht')).sub_const (γ.cutoff t)).abs
      simpa only [sub_self,abs_zero] using hl)
  change Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, |profileCoeff (γ.grid n) t-γ.cutoff t|) atTop (𝓝 0)
  simpa only [intervalIntegral.integral_zero] using hl

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_StandardGaussian
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -y^2/2) (-x) x := by
    have hh := ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ)
    simpa only [Pi.pow_def,Pi.neg_def,id_eq,pow_one,show (2 : ℕ)-1=1 from rfl,
      Nat.cast_ofNat,mul_one,neg_div,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh
  have hd := h1.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  convert hd using 1 <;> try rfl
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    ring

lemma density_mul_integrable {f : ℝ → ℝ} (hf : Integrable f standardGaussian) :
    Integrable (fun x ↦ gaussianPDFReal 0 1 x*f x) := by
  rw [standardGaussian,gaussianReal_of_var_ne_zero _ (by norm_num)] at hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Eventually.of_forall (fun x ↦ gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mp hf
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hh

lemma standardGaussian_integrable_id : Integrable (fun x : ℝ ↦ x) standardGaussian := by
  have hh := (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (1 : ℝ≥0∞) (by norm_num))
  exact hh.integrable (by norm_num)

lemma gaussian_stein_bounded {f f' : ℝ → ℝ} {C D : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hm : AEStronglyMeasurable f' standardGaussian)
    (hC : ∀ x, |f x|≤C) (hD : ∀ x, |f' x|≤D) :
    (∫ x, x*f x ∂standardGaussian) = ∫ x, f' x ∂standardGaussian := by
  have hfm : Continuous f := continuous_iff_continuousAt.mpr (fun x ↦ (hf x).continuousAt)
  have hfi : Integrable f standardGaussian := Integrable.of_bound hfm.aestronglyMeasurable C
    (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hC x)))
  have hf'i : Integrable f' standardGaussian := Integrable.of_bound hm D
    (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hD x)))
  have hxfi : Integrable (fun x ↦ x*f x) standardGaussian :=
    standardGaussian_integrable_id.mul_bdd hfm.aestronglyMeasurable
      (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hC x)))
  have hi1 : Integrable (fun x ↦ f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert (density_mul_integrable hxfi).neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.neg_apply]
    ring
  have hi2 : Integrable (fun x ↦ f' x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hf'i
  have hi3 : Integrable (fun x ↦ f x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hfi
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 1) (u' := f') (v' := fun x ↦ -x*gaussianPDFReal 0 1 x)
    (fun x _ ↦ hf x) (fun x _ ↦ density_hasDerivAt x) hi1 hi2 hi3
  have hb : (∫ x, f x*(-x*gaussianPDFReal 0 1 x)) =
      -(∫ x, gaussianPDFReal 0 1 x*(x*f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by ring)
  rw [hb] at hibp
  have he : (∫ x, gaussianPDFReal 0 1 x*(x*f x)) =
      ∫ x, gaussianPDFReal 0 1 x*f' x := by
    exact neg_injective hibp |>.trans (by congr 1; funext x; ring)
  simpa only [standardGaussian,integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul] using he

lemma gaussian_coordinate_integrable {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun z : ι → ℝ ↦ z i) (gaussianProduct ι) := by
  exact ((measurePreserving_eval (fun _ : ι ↦ standardGaussian) i).integrable_comp
    standardGaussian_integrable_id.aestronglyMeasurable).mpr standardGaussian_integrable_id

lemma gaussian_pi_stein_bounded {n : ℕ} (i : Fin n) {f f' : (Fin n → ℝ) → ℝ} {C D : ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ z, HasDerivAt (fun x ↦ f (Function.update z i x)) (f' z) (z i))
    (hC : ∀ z, |f z| ≤ C) (hD : ∀ z, |f' z| ≤ D) :
    (∫ z, z i*f z ∂gaussianProduct (Fin n)) = ∫ z, f' z ∂gaussianProduct (Fin n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) i
    have he : MeasurePreserving e.symm (standardGaussian.prod (gaussianProduct (Fin n)))
        (gaussianProduct (Fin (n+1))) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ standardGaussian) i).symm
    have hi : Integrable (fun z : Fin (n+1) → ℝ ↦ z i*f z) (gaussianProduct (Fin (n+1))) :=
      (gaussian_coordinate_integrable i).mul_bdd hf.aestronglyMeasurable
        (Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (hC z)))
    have hi' : Integrable f' (gaussianProduct (Fin (n+1))) :=
      Integrable.of_bound hf'.aestronglyMeasurable D
        (Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (hD z)))
    have hip : Integrable (fun p ↦ e.symm p i * f (e.symm p))
        (standardGaussian.prod (gaussianProduct (Fin n))) := (he.integrable_comp hi.aestronglyMeasurable).mpr hi
    have hi'p : Integrable (fun p ↦ f' (e.symm p))
        (standardGaussian.prod (gaussianProduct (Fin n))) := (he.integrable_comp hi'.aestronglyMeasurable).mpr hi'
    rw [← he.integral_comp' (fun z ↦ z i*f z), ← he.integral_comp' f',
      integral_prod _ hip, integral_prod _ hi'p,
      integral_integral_swap (f := fun x y ↦ e.symm (x,y) i * f (e.symm (x,y))) hip,
      integral_integral_swap (f := fun x y ↦ f' (e.symm (x,y))) hi'p]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_same]
    change (∫ x, x*f (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) ∂standardGaussian) =
      ∫ x, f' (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) ∂standardGaussian
    have hmeas : Measurable (fun x : ℝ ↦ i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) := by
      exact e.symm.measurable.comp (measurable_id.prodMk measurable_const)
    apply gaussian_stein_bounded (f' := fun x ↦ f' (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y))
    · intro x
      simpa only [Fin.update_insertNth,Fin.insertNth_apply_same] using hd (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y)
    · exact (hf'.measurable.comp hmeas).aestronglyMeasurable
    · exact fun x ↦ hC _
    · exact fun x ↦ hD _

lemma partition_pos {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) : 0 < partition x := by
  exact Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty

lemma gibbsWeight_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    0 ≤ gibbsWeight x i := le_of_lt (div_pos (Real.exp_pos _) (partition_pos x))

lemma sum_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∑ i, gibbsWeight x i = 1 := by
  simp only [gibbsWeight,← Finset.sum_div]
  change partition x / partition x = 1
  exact div_self (ne_of_gt (partition_pos x))

lemma gibbsWeight_le_one {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    gibbsWeight x i ≤ 1 := by
  calc
    _ ≤ ∑ j, gibbsWeight x j := Finset.single_le_sum (fun j _ ↦ gibbsWeight_nonneg x j) (Finset.mem_univ i)
    _ = 1 := sum_gibbsWeight x

lemma continuous_partition {ι : Type*} [Fintype ι] : Continuous (@partition ι _) := by
  unfold partition
  fun_prop

lemma continuous_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι] (i : ι) :
    Continuous (fun x : ι → ℝ ↦ gibbsWeight x i) := by
  exact (Real.continuous_exp.comp (continuous_apply i)).div continuous_partition (fun x ↦ ne_of_gt (partition_pos x))

lemma hasDerivAt_partition {ι : Type*} [Fintype ι] {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) :
    HasDerivAt (fun s ↦ partition (x s)) (∑ i, Real.exp (x t i)*v i) t := by
  simpa only [partition,Finset.sum_apply] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (h i).exp))

lemma hasDerivAt_logPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) :
    HasDerivAt (fun s ↦ logPartition (x s)) (∑ i, gibbsWeight (x t) i*v i) t := by
  convert (hasDerivAt_partition h).log (ne_of_gt (partition_pos _)) using 1 <;> try rfl
  simp only [gibbsWeight,Finset.sum_div,mul_div_assoc]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma hasDerivAt_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) (i : ι) :
    HasDerivAt (fun s ↦ gibbsWeight (x s) i)
      (gibbsWeight (x t) i*(v i-∑ j, gibbsWeight (x t) j*v j)) t := by
  convert (h i).exp.div (hasDerivAt_partition h) (ne_of_gt (partition_pos _)) using 1 <;> try rfl
  simp only [gibbsWeight]
  rw [show (∑ j, Real.exp (x t j)/partition (x t)*v j) =
      (∑ j, Real.exp (x t j)*v j)/partition (x t) by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring]
  field_simp [ne_of_gt (partition_pos (x t))]

lemma abs_gibbsMean_le {ι : Type*} [Fintype ι] [Nonempty ι] (x v : ι → ℝ) {C : ℝ}
    (hC : ∀ i, |v i| ≤ C) : |∑ i, gibbsWeight x i*v i| ≤ C := by
  calc
    _ ≤ ∑ i, |gibbsWeight x i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, gibbsWeight x i*|v i| := by simp only [abs_mul,abs_of_nonneg (gibbsWeight_nonneg _ _)]
    _ ≤ ∑ i, gibbsWeight x i*C := Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hC i) (gibbsWeight_nonneg _ _))
    _ = C := by rw [← Finset.sum_mul,sum_gibbsWeight,one_mul]

lemma continuous_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) :
    Continuous (linearProcess c) := by
  unfold linearProcess
  fun_prop

lemma hasDerivAt_linearProcess_update {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : ι → κ → ℝ) (z : κ → ℝ) (i : ι) (k : κ) :
    HasDerivAt (fun x ↦ linearProcess c (Function.update z k x) i) (c i k) (z k) := by
  have h : ∀ j, HasDerivAt (fun x ↦ c i j * Function.update z k x j)
      (if j=k then c i k else 0) (z k) := by
    intro j
    by_cases hj : j=k
    · subst j
      simpa only [Function.update_self,ite_true,mul_one,id_eq] using (hasDerivAt_id (z k)).const_mul (c i k)
    · simpa only [Function.update_of_ne hj,ite_eq_right hj] using hasDerivAt_const (z k) (c i j*z j)
  simpa only [linearProcess,Finset.sum_apply,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    using HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ h j)

lemma continuous_linear_gibbsWeight {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) : Continuous (fun z ↦ gibbsWeight (linearProcess c z) i) :=
  (continuous_gibbsWeight i).comp (continuous_linearProcess c)

lemma integrable_linear_gibbsWeight {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) : Integrable (fun z ↦ gibbsWeight (linearProcess c z) i) (gaussianProduct κ) := by
  apply Integrable.of_bound (continuous_linear_gibbsWeight c i).aestronglyMeasurable 1
  exact Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _)

lemma coordinate_gibbsWeight_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) (k : κ) :
    Integrable (fun z ↦ z k*gibbsWeight (linearProcess c z) i) (gaussianProduct κ) := by
  apply (gaussian_coordinate_integrable k).mul_bdd (continuous_linear_gibbsWeight c i).aestronglyMeasurable
  exact Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _)

lemma gaussian_coordinate_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    (∫ z, z k*gibbsWeight (linearProcess c z) i ∂gaussianProduct (Fin n)) =
    ∫ z, gibbsWeight (linearProcess c z) i *
      (c i k - ∑ j, gibbsWeight (linearProcess c z) j*c j k) ∂gaussianProduct (Fin n) := by
  apply gaussian_pi_stein_bounded k (C := 1) (D := 2*∑ j, |c j k|)
  · exact continuous_linear_gibbsWeight c i
  · apply Continuous.mul (continuous_linear_gibbsWeight c i)
    apply continuous_const.sub
    exact continuous_finsetSum _ (fun j _ ↦ (continuous_linear_gibbsWeight c j).mul continuous_const)
  · intro z
    simpa only [Function.update_eq_self] using
      hasDerivAt_gibbsWeight (fun j ↦ hasDerivAt_linearProcess_update c z j k) i
  · intro z
    rw [abs_of_nonneg (gibbsWeight_nonneg _ _)]
    exact gibbsWeight_le_one _ _
  · intro z
    have hsum : ∀ j, |c j k| ≤ ∑ l, |c l k| := fun j ↦
      Finset.single_le_sum (f := fun l ↦ |c l k|) (fun l _ ↦ abs_nonneg _) (Finset.mem_univ j)
    calc
      _ = gibbsWeight (linearProcess c z) i * |c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k| := by
        rw [abs_mul,abs_of_nonneg (gibbsWeight_nonneg _ _)]
      _ ≤ |c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k| :=
        mul_le_of_le_one_left (abs_nonneg _) (gibbsWeight_le_one _ _)
      _ ≤ |c i k| + |∑ j, gibbsWeight (linearProcess c z) j*c j k| := abs_sub _ _
      _ ≤ (∑ j, |c j k|) + (∑ j, |c j k|) := add_le_add (hsum i) (abs_gibbsMean_le _ _ hsum)
      _ = _ := by ring

lemma le_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    x i ≤ logPartition x := by
  apply (Real.le_log_iff_exp_le (partition_pos x)).mpr
  exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i)

lemma logPartition_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) {C : ℝ}
    (h : ∀ i, x i ≤ C) : logPartition x ≤ Real.log (Fintype.card ι) + C := by
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    logPartition x ≤ Real.log ((Fintype.card ι : ℝ)*Real.exp C) := by
      apply Real.log_le_log (partition_pos x)
      calc
        partition x ≤ ∑ _ : ι, Real.exp C := Finset.sum_le_sum (fun i _ ↦ Real.exp_le_exp.mpr (h i))
        _ = _ := by simp
    _ = _ := by rw [Real.log_mul (ne_of_gt hc) (Real.exp_ne_zero _),Real.log_exp]

lemma abs_logPartition_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    |logPartition x| ≤ |Real.log (Fintype.card ι)| + ∑ i, |x i| := by
  have hsum : ∀ i, |x i| ≤ ∑ j, |x j| := fun i ↦
    Finset.single_le_sum (f := fun j ↦ |x j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
  have hu := logPartition_le x (fun i ↦ (le_abs_self _).trans (hsum i))
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hl := le_logPartition x i
  have hx := neg_abs_le (x i)
  have hxi := hsum i
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log (Fintype.card ι)),abs_nonneg (Real.log (Fintype.card ι))]

lemma continuous_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (@logPartition ι _) :=
  continuous_partition.log (fun x ↦ ne_of_gt (partition_pos x))

lemma linearProcess_integrable {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    Integrable (fun z ↦ linearProcess c z i) (gaussianProduct κ) :=
  integrable_finsetSum _ (fun k _ ↦ (gaussian_coordinate_integrable k).const_mul (c i k))

lemma logPartition_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) : Integrable (fun z ↦ logPartition (linearProcess c z)) (gaussianProduct κ) := by
  have hb := (integrable_const (|Real.log (Fintype.card ι)| : ℝ)).add
    (integrable_finsetSum Finset.univ (fun i _ ↦ (linearProcess_integrable c i).abs))
  apply hb.mono' ((continuous_logPartition.comp (continuous_linearProcess c)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_def,Pi.add_apply] using abs_logPartition_le (linearProcess c z))

lemma gibbsWeight_mul_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) {f : (κ → ℝ) → ℝ} (hi : Integrable f (gaussianProduct κ)) :
    Integrable (fun z ↦ gibbsWeight (linearProcess c z) i*f z) (gaussianProduct κ) := by
  simpa only [mul_comm] using hi.mul_bdd (continuous_linear_gibbsWeight c i).aestronglyMeasurable
    (Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _))

lemma gaussian_linear_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c d : ι → Fin n → ℝ) (i : ι) :
    (∫ z, gibbsWeight (linearProcess c z) i * linearProcess d z i ∂gaussianProduct (Fin n)) =
    ∫ z, gibbsWeight (linearProcess c z) i *
      ((∑ k, d i k*c i k) - ∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k))
        ∂gaussianProduct (Fin n) := by
  have hid : ∀ k, Integrable (fun z ↦ d i k * (z k*gibbsWeight (linearProcess c z) i))
      (gaussianProduct (Fin n)) := fun k ↦ (coordinate_gibbsWeight_integrable c i k).const_mul _
  have hic : ∀ k, Integrable (fun z ↦ d i k * (gibbsWeight (linearProcess c z) i *
      (c i k - ∑ j, gibbsWeight (linearProcess c z) j*c j k))) (gaussianProduct (Fin n)) := by
    intro k
    apply Integrable.const_mul
    apply gibbsWeight_mul_integrable
    exact (integrable_const _).sub (integrable_finsetSum Finset.univ
      (fun j _ ↦ (integrable_linear_gibbsWeight c j).mul_const _))
  calc
    _ = ∫ z, ∑ k, d i k*(z k*gibbsWeight (linearProcess c z) i) ∂gaussianProduct (Fin n) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z ↦ by simp only [linearProcess,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring)
    _ = ∑ k, d i k * (∫ z, z k*gibbsWeight (linearProcess c z) i ∂gaussianProduct (Fin n)) := by
      rw [integral_finsetSum Finset.univ (fun k _ ↦ hid k)]
      simp only [integral_const_mul]
    _ = ∑ k, d i k * (∫ z, gibbsWeight (linearProcess c z) i *
        (c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k) ∂gaussianProduct (Fin n)) := by
      simp only [gaussian_coordinate_gibbsWeight]
    _ = ∫ z, ∑ k, d i k * (gibbsWeight (linearProcess c z) i *
        (c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k)) ∂gaussianProduct (Fin n) := by
      rw [integral_finsetSum Finset.univ (fun k _ ↦ hic k)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl; intro k _; ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _; ring

lemma weighted_covariance_pairs {ι : Type*} [Fintype ι] (p : ι → ℝ) (D : ι → ι → ℝ)
    (hp : ∑ i, p i = 1) :
    ∑ i, p i*(D i i-∑ j, p j*D i j) =
    (1/2 : ℝ)*∑ i, ∑ j, p i*p j*(D i i+D j j-D i j-D j i) := by
  have h1 : (∑ i, ∑ j, p i*p j*D i i) = ∑ i, p i*D i i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = p i*D i i*∑ j, p j := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ = _ := by rw [hp,mul_one]
  have h2 : (∑ i, ∑ j, p i*p j*D j j) = ∑ j, p j*D j j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (∑ i, p i)*(p j*D j j) := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := by rw [hp,one_mul]
  have h3 : (∑ i, ∑ j, p i*p j*D j i) = ∑ i, ∑ j, p i*p j*D i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  have hl : (∑ i, p i*(D i i-∑ j, p j*D i j)) =
      (∑ i, p i*D i i) - ∑ i, ∑ j, p i*p j*D i j := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
  have hr : (∑ i, ∑ j, p i*p j*(D i i+D j j-D i j-D j i)) =
      2*(∑ i, p i*D i i)-2*(∑ i, ∑ j, p i*p j*D i j) := by
    simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [h1,h2,h3]
    ring
  rw [hl,hr]
  ring

end SKValueG
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RotatedCoefficients
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma gaussian_gibbs_derivative_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c d : ι → Fin n → ℝ)
    (h : ∀ i j, 0 ≤ ∑ k, (d i k-d j k)*(c i k-c j k)) :
    0 ≤ ∫ z, ∑ i, gibbsWeight (linearProcess c z) i*linearProcess d z i ∂gaussianProduct (Fin n) := by
  have hi : ∀ i, Integrable (fun z ↦ gibbsWeight (linearProcess c z) i*linearProcess d z i)
      (gaussianProduct (Fin n)) := fun i ↦ gibbsWeight_mul_integrable c i (linearProcess_integrable d i)
  have hi' : ∀ i, Integrable (fun z ↦ gibbsWeight (linearProcess c z) i *
      ((∑ k, d i k*c i k)-∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k)))
      (gaussianProduct (Fin n)) := by
    intro i
    apply gibbsWeight_mul_integrable
    exact (integrable_const _).sub (integrable_finsetSum _ (fun j _ ↦ (integrable_linear_gibbsWeight c j).mul_const _))
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [gaussian_linear_gibbsWeight]
  rw [← integral_finsetSum _ (fun i _ ↦ hi' i)]
  apply integral_nonneg
  intro z
  change (0 : ℝ) ≤ ∑ i, gibbsWeight (linearProcess c z) i *
    ((∑ k, d i k*c i k)-∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k))
  rw [weighted_covariance_pairs _ (fun i j ↦ ∑ k, d i k*c j k) (sum_gibbsWeight (linearProcess c z))]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (gibbsWeight_nonneg _ _) (gibbsWeight_nonneg _ _))
  have he : (∑ k, d i k*c i k)+(∑ k, d j k*c j k)-
      (∑ k, d i k*c j k)-(∑ k, d j k*c i k) = ∑ k, (d i k-d j k)*(c i k-c j k) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact h i j

lemma hasDerivAt_rotatedProcess {ι κ : Type*} [Fintype κ] (a b : ι → κ → ℝ)
    (t : ℝ) (z : κ → ℝ) (i : ι) :
    HasDerivAt (fun s ↦ linearProcess (rotatedCoefficients a b s) z i)
      (linearProcess (rotationVelocity a b t) z i) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
    (((Real.hasDerivAt_cos t).mul_const (a i k)).add ((Real.hasDerivAt_sin t).mul_const (b i k))).mul_const (z k))

lemma abs_rotationVelocity_le {ι κ : Type*} (a b : ι → κ → ℝ) (t : ℝ) (i : ι) (k : κ) :
    |rotationVelocity a b t i k| ≤ |a i k|+|b i k| := by
  calc
    _ ≤ |-Real.sin t*a i k| + |Real.cos t*b i k| := abs_add_le _ _
    _ = |Real.sin t| *|a i k| + |Real.cos t| *|b i k| := by rw [abs_mul,abs_neg,abs_mul]
    _ ≤ 1*|a i k| + 1*|b i k| := add_le_add
      (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (abs_nonneg _))
    _ = _ := by ring

lemma rotation_derivative_bound {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (a b : ι → κ → ℝ) (t : ℝ) (z : κ → ℝ) :
    |∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
        linearProcess (rotationVelocity a b t) z i| ≤
      ∑ i, ∑ k, (|a i k|+|b i k|)*|z k| := by
  apply abs_gibbsMean_le
  intro i
  calc
    _ ≤ ∑ k, |rotationVelocity a b t i k*z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (|a i k|+|b i k|)*|z k| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_rotationVelocity_le _ _ _ _ _) (abs_nonneg _)
    _ ≤ _ := Finset.single_le_sum (f := fun j ↦ ∑ k, (|a j k|+|b j k|)*|z k|) (fun j _ ↦ Finset.sum_nonneg (fun k _ ↦ mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))) (Finset.mem_univ i)

lemma hasDerivAt_expected_rotated_logPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ z, logPartition (linearProcess (rotatedCoefficients a b s) z) ∂gaussianProduct (Fin n))
      (∫ z, ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
        linearProcess (rotationVelocity a b t) z i ∂gaussianProduct (Fin n)) t := by
  have hb : Integrable (fun z : Fin n → ℝ ↦ ∑ i, ∑ k, (|a i k|+|b i k|)*|z k|)
      (gaussianProduct (Fin n)) :=
    integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun k _ ↦
      (gaussian_coordinate_integrable k).abs.const_mul _))
  have hmc : Continuous (fun z : Fin n → ℝ ↦ ∑ i,
      gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
      linearProcess (rotationVelocity a b t) z i) := by
    apply continuous_finsetSum
    intro i _
    apply (continuous_linear_gibbsWeight _ _).mul
    exact (continuous_apply i).comp (continuous_linearProcess _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) (μ := gaussianProduct (Fin n))
    (F := fun s z ↦ logPartition (linearProcess (rotatedCoefficients a b s) z))
    (F' := fun s z ↦ ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b s) z) i *
      linearProcess (rotationVelocity a b s) z i)
    (bound := fun z ↦ ∑ i, ∑ k, (|a i k|+|b i k|)*|z k|)
    (Filter.univ_mem)
    (Eventually.of_forall (fun s ↦ (continuous_logPartition.comp (continuous_linearProcess _)).aestronglyMeasurable))
    (logPartition_integrable _) hmc.aestronglyMeasurable
    (Eventually.of_forall (fun z s _ ↦ by simpa only [Real.norm_eq_abs] using rotation_derivative_bound a b s z)) hb
    (Eventually.of_forall (fun z s _ ↦ hasDerivAt_logPartition (hasDerivAt_rotatedProcess a b s z)))).2

lemma rotation_pair_covariance {ι κ : Type*} [Fintype κ] (a b : ι → κ → ℝ) (t : ℝ) (i j : ι) :
    (∑ k, (rotationVelocity a b t i k-rotationVelocity a b t j k)*
      (rotatedCoefficients a b t i k-rotatedCoefficients a b t j k)) =
    Real.sin t*Real.cos t*((∑ k, (b i k-b j k)^2)-(∑ k, (a i k-a j k)^2)) +
      ((Real.cos t)^2-(Real.sin t)^2)*∑ k, (a i k-a j k)*(b i k-b j k) := by
  simp only [rotationVelocity,rotatedCoefficients,← Finset.sum_sub_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma expected_logPartition_le_of_pair_distances {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
    ∫ z, logPartition (linearProcess b z) ∂gaussianProduct (Fin n) := by
  let F := fun t ↦ ∫ z, logPartition (linearProcess (rotatedCoefficients a b t) z) ∂gaussianProduct (Fin n)
  have hd : ∀ t, HasDerivAt F (∫ z, ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
      linearProcess (rotationVelocity a b t) z i ∂gaussianProduct (Fin n)) t :=
    hasDerivAt_expected_rotated_logPartition a b
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t ↦ (hd t).continuousAt)
  have hm : MonotoneOn F (Icc (0 : ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc.continuousOn
      (fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (Real.pi/2) := interior_subset ht
    rw [(hd t).deriv]
    apply gaussian_gibbs_derivative_nonneg
    intro i j
    rw [rotation_pair_covariance,horth,mul_zero,add_zero]
    exact mul_nonneg (mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 (ht'.2.trans (by linarith [Real.pi_pos])))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht'.1],ht'.2⟩)) (sub_nonneg.mpr (hdist i j))
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hh := hm ⟨le_rfl,hπ⟩ ⟨hπ,le_rfl⟩ hπ
  have ha0 : rotatedCoefficients a b 0 = a := by funext i k; simp [rotatedCoefficients]
  have hb0 : rotatedCoefficients a b (Real.pi/2) = b := by funext i k; simp [rotatedCoefficients]
  simpa only [F,ha0,hb0] using hh

lemma le_finiteMaximum {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : x i ≤ finiteMaximum x :=
  le_csSup (Set.finite_range x).bddAbove (Set.mem_range_self i)

lemma exists_finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∃ i, x i = finiteMaximum x := (Set.range_nonempty x).csSup_mem (Set.finite_range x)

lemma continuous_finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (@finiteMaximum ι) := by
  have he (x : ι → ℝ) : finiteMaximum x = Finset.univ.sup' Finset.univ_nonempty x := by
    rw [Finset.sup'_eq_csSup_image]
    simp only [Finset.coe_univ,Set.image_univ,finiteMaximum]
  simp_rw [funext he]
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ ↦ continuous_apply i)

lemma abs_finiteMaximum_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    |finiteMaximum x| ≤ ∑ i, |x i| := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  rw [← hi]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x j)) (Finset.mem_univ i)

lemma finiteMaximum_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) : Integrable (fun z ↦ finiteMaximum (linearProcess c z)) (gaussianProduct κ) := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ (linearProcess_integrable c i).abs)).mono'
    ((continuous_finiteMaximum.comp (continuous_linearProcess c)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_def] using abs_finiteMaximum_le (linearProcess c z))

lemma scaled_max_le_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    (β : ℝ) : β*finiteMaximum x ≤ logPartition (fun i ↦ β*x i) := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  rw [← hi]
  exact le_logPartition (fun i ↦ β*x i) i

lemma logPartition_le_scaled_max {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    {β : ℝ} (hβ : 0 ≤ β) : logPartition (fun i ↦ β*x i) ≤ β*finiteMaximum x+Real.log (Fintype.card ι) := by
  exact (logPartition_le _ (fun i ↦ mul_le_mul_of_nonneg_left (le_finiteMaximum x i) hβ)).trans_eq (add_comm _ _)

lemma linearProcess_scaled {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (β : ℝ) (z : κ → ℝ) :
    linearProcess (fun i k ↦ β*c i k) z = fun i ↦ β*linearProcess c z i := by
  funext i
  simp only [linearProcess,Finset.mul_sum,mul_assoc]

lemma expected_max_le_of_pair_distances_orthogonal {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n) := by
  have hb (β : ℝ) (hβ : 0 ≤ β) :
      β*(∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
      β*(∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n)) + Real.log (Fintype.card ι) := by
    have hiA := logPartition_integrable (fun i k ↦ β*a i k)
    have hiB := logPartition_integrable (fun i k ↦ β*b i k)
    have hcomp := expected_logPartition_le_of_pair_distances
      (fun i k ↦ β*a i k) (fun i k ↦ β*b i k)
      (fun i j ↦ by
        calc
          (∑ k, (β*a i k-β*a j k)*(β*b i k-β*b j k)) =
              β^2*(∑ k, (a i k-a j k)*(b i k-b j k)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
          _ = 0 := by rw [horth,mul_zero])
      (fun i j ↦ by
        have he (c : ι → Fin n → ℝ) : (∑ k, (β*c i k-β*c j k)^2) = β^2*∑ k, (c i k-c j k)^2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        rw [he,he]
        exact mul_le_mul_of_nonneg_left (hdist i j) (sq_nonneg β))
    calc
      _ = ∫ z, β*finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n) := by rw [integral_const_mul]
      _ ≤ ∫ z, logPartition (linearProcess (fun i k ↦ β*a i k) z) ∂gaussianProduct (Fin n) := by
        apply integral_mono ((finiteMaximum_integrable a).const_mul _) hiA
        intro z
        change β*finiteMaximum (linearProcess a z) ≤ logPartition (linearProcess (fun i k ↦ β*a i k) z)
        rw [linearProcess_scaled]
        exact scaled_max_le_logPartition _ _
      _ ≤ _ := hcomp
      _ ≤ ∫ z, β*finiteMaximum (linearProcess b z)+Real.log (Fintype.card ι) ∂gaussianProduct (Fin n) := by
        apply integral_mono hiB (((finiteMaximum_integrable b).const_mul _).add (integrable_const _))
        intro z
        change logPartition (linearProcess (fun i k ↦ β*b i k) z) ≤ β*finiteMaximum (linearProcess b z)+Real.log (Fintype.card ι)
        rw [linearProcess_scaled]
        exact logPartition_le_scaled_max _ hβ
      _ = _ := by rw [integral_add ((finiteMaximum_integrable b).const_mul _) (integrable_const _),integral_const_mul,integral_const]; simp
  by_contra hh
  have hΔ : 0 < (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) -
      (∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n)) := sub_pos.mpr (lt_of_not_ge hh)
  let Δ := (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct (Fin n)) -
      (∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct (Fin n))
  let β := (|Real.log (Fintype.card ι)|+1)/Δ
  have hβ : 0 < β := div_pos (by positivity) hΔ
  have hh' := hb β hβ.le
  have he : β*Δ = |Real.log (Fintype.card ι)|+1 := div_mul_cancel₀ _ hΔ.ne'
  have hlog := le_abs_self (Real.log (Fintype.card ι))
  dsimp [Δ] at he
  nlinarith

lemma gaussian_integral_reindex {κ ν : Type*} [Fintype κ] [Fintype ν] (e : κ ≃ ν)
    (f : (κ → ℝ) → ℝ) :
    (∫ z : ν → ℝ, f (fun k ↦ z (e k)) ∂gaussianProduct ν) = ∫ z, f z ∂gaussianProduct κ := by
  have he := measurePreserving_piCongrLeft (α := fun _ : κ ↦ ℝ)
    (fun _ : κ ↦ standardGaussian) e.symm
  have hf (z : ν → ℝ) : (MeasurableEquiv.piCongrLeft (π := fun _ : κ ↦ ℝ) e.symm) z = fun k ↦ z (e k) := by
    funext k
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simpa only [gaussianProduct,hf] using he.integral_comp' f

lemma linearProcess_reindex {ι κ ν : Type*} [Fintype κ] [Fintype ν]
    (c : ι → κ → ℝ) (e : κ ≃ ν) (z : ν → ℝ) :
    linearProcess c (fun k ↦ z (e k)) = linearProcess (fun i l ↦ c i (e.symm l)) z := by
  funext i
  simpa only [linearProcess, Equiv.symm_apply_apply] using e.sum_comp (fun l ↦ c i (e.symm l)*z l)

lemma expected_max_reindex {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (c : ι → κ → ℝ) (e : κ ≃ ν) :
    (∫ z, finiteMaximum (linearProcess (fun i l ↦ c i (e.symm l)) z) ∂gaussianProduct ν) =
    ∫ z, finiteMaximum (linearProcess c z) ∂gaussianProduct κ := by
  simpa only [linearProcess_reindex] using gaussian_integral_reindex e (fun z ↦ finiteMaximum (linearProcess c z))

lemma expected_max_le_of_pair_distances_orthogonal_fintype {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ι → κ → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct κ) ≤
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct κ := by
  let e := Fintype.equivFin κ
  have hh := expected_max_le_of_pair_distances_orthogonal
    (fun i k ↦ a i (e.symm k)) (fun i k ↦ b i (e.symm k))
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)*(b i k-b j k))]
      exact horth i j)
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)^2), e.symm.sum_comp (fun k ↦ (b i k-b j k)^2)]
      exact hdist i j)
  simpa only [expected_max_reindex] using hh

lemma expected_max_embedLeft {ι κ ν : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) :
    (∫ z, finiteMaximum (linearProcess (embedLeft (ν := ν) a) z) ∂gaussianProduct (κ ⊕ ν)) =
    ∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct κ := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, finiteMaximum (linearProcess (embedLeft a) z) ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ finiteMaximum (linearProcess (embedLeft a) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedLeft a) ((MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ ν ↦ ℝ)).symm p) =
      linearProcess a p.1 := by
    funext i
    simp [linearProcess,embedLeft,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_fst (μ := gaussianProduct κ) (ν := gaussianProduct ν) (fun z ↦ finiteMaximum (linearProcess a z))

lemma expected_max_embedRight {ι κ ν : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (b : ι → ν → ℝ) :
    (∫ z, finiteMaximum (linearProcess (embedRight (κ := κ) b) z) ∂gaussianProduct (κ ⊕ ν)) =
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct ν := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, finiteMaximum (linearProcess (embedRight b) z) ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ finiteMaximum (linearProcess (embedRight b) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedRight b) ((MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ ν ↦ ℝ)).symm p) =
      linearProcess b p.2 := by
    funext i
    simp [linearProcess,embedRight,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_snd (μ := gaussianProduct κ) (ν := gaussianProduct ν) (fun z ↦ finiteMaximum (linearProcess b z))

lemma expected_max_le_of_pair_distances {ι κ ν : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) (b : ι → ν → ℝ)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (linearProcess a z) ∂gaussianProduct κ) ≤
    ∫ z, finiteMaximum (linearProcess b z) ∂gaussianProduct ν := by
  have h := expected_max_le_of_pair_distances_orthogonal_fintype
    (embedLeft (ν := ν) a) (embedRight (κ := κ) b)
    (fun i j ↦ by simp [embedLeft,embedRight,Fintype.sum_sum_type])
    (fun i j ↦ by simpa only [Fintype.sum_sum_type,embedLeft,embedRight,
      Sum.elim_inl,Sum.elim_inr,sub_self,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_add,add_zero] using hdist i j)
  simpa only [expected_max_embedLeft,expected_max_embedRight] using h

lemma spin_sq (b : Bool) : spin b ^ 2 = 1 := by cases b <;> norm_num [spin]

lemma linearProcess_hamCoeff (n : ℕ) (J : (Fin n × Fin n) → ℝ) :
    linearProcess (hamCoeff n) J = hamiltonian n J := by
  funext σ
  simp only [linearProcess,hamCoeff,hamiltonian,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma groundStateSequence_eq (n : ℕ) : groundStateSequence n = (n : ℝ)⁻¹ * expectedMaximum n := by
  simp only [groundStateSequence,expectedMaximum,linearProcess_hamCoeff,finiteMaximum]

lemma twice_upper_sum {ι : Type*} [Fintype ι] [LinearOrder ι] (f : ι → ι → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    2*(∑ i, ∑ j, if i < j then f i j else 0) = ∑ i, ∑ j, f i j := by
  have hs : (∑ i, ∑ j, if j < i then f i j else 0) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have hsplit (i j : ι) : f i j = (if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_ge h.le]
    · subst j; simp [hdiag]
    · simp [h,not_lt_of_ge h.le]
  conv_rhs => arg 2; ext i; arg 2; ext j; rw [hsplit i j]
  simp only [Finset.sum_add_distrib,hs]
  ring

lemma spin_pair_difference {dimension : ℕ} (σ τ : Fin dimension → Bool) (i j : Fin dimension) :
    (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 =
      2-2*(spin (σ i)*spin (τ i))*(spin (σ j)*spin (τ j)) := by
  have h1 := spin_sq (σ i)
  have h2 := spin_sq (σ j)
  have h3 := spin_sq (τ i)
  have h4 := spin_sq (τ j)
  calc
    _ = (spin (σ i))^2*(spin (σ j))^2+(spin (τ i))^2*(spin (τ j))^2 -
      2*(spin (σ i)*spin (τ i))*(spin (σ j)*spin (τ j)) := by ring
    _ = _ := by rw [h1,h2,h3,h4]; ring

end SKValueG
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_BlockCoeff
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma hamCoeff_distance {n : ℕ} (hn : 0 < n) (σ τ : Fin n → Bool) :
    (∑ k, (hamCoeff n σ k-hamCoeff n τ k)^2) =
    (n : ℝ) - (∑ i, spin (σ i)*spin (τ i))^2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt := Real.sq_sqrt hn'.le
  have hn0 := ne_of_gt hn'
  have hs0 := Real.sqrt_ne_zero'.mpr hn'
  have hu := twice_upper_sum (fun i j ↦ (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2)
    (fun i j ↦ by ring) (fun i ↦ by rw [← sq,← sq,spin_sq,spin_sq]; norm_num)
  have he : (∑ i, ∑ j, (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2) =
      2*(n : ℝ)^2 - 2*(∑ i, spin (σ i)*spin (τ i))^2 := by
    simp_rw [spin_pair_difference,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum,← Finset.sum_mul]
    ring
  have hc : (∑ k, (hamCoeff n σ k-hamCoeff n τ k)^2) =
      (Real.sqrt (n : ℝ))⁻¹^2 *
      ∑ i, ∑ j, if i < j then (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 else 0 := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum,hamCoeff]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hc,inv_pow,hsqrt]
  rw [he] at hu
  have ht : (∑ i, ∑ j, if i < j then (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 else 0) =
      (n : ℝ)^2 - (∑ i, spin (σ i)*spin (τ i))^2 := by linarith
  rw [ht]
  field_simp

lemma weighted_square_div_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    (x+y)^2/(a+b) ≤ x^2/a+y^2/b := by
  have hab : 0 < a+b := add_pos ha hb
  have he : x^2/a+y^2/b = (b*x^2+a*y^2)/(a*b) := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ hab (mul_pos ha hb)).2
  nlinarith [sq_nonneg (b*x-a*y)]

lemma blockCoeff_distance_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (σ τ : Fin (n+m) → Bool) :
    (∑ k, (blockCoeff n m σ k-blockCoeff n m τ k)^2) ≤
      ∑ k, (hamCoeff (n+m) σ k-hamCoeff (n+m) τ k)^2 := by
  simp only [Fintype.sum_sum_type,blockCoeff,Sum.elim_inl,Sum.elim_inr]
  rw [hamCoeff_distance hn,hamCoeff_distance hm,hamCoeff_distance (by omega)]
  rw [Fin.sum_univ_add,Nat.cast_add]
  have hh := weighted_square_div_le (by exact_mod_cast hn : (0 : ℝ) < n)
    (by exact_mod_cast hm : (0 : ℝ) < m)
    (∑ i : Fin n, spin (σ (Fin.castAdd m i))*spin (τ (Fin.castAdd m i)))
    (∑ i : Fin m, spin (σ (Fin.natAdd n i))*spin (τ (Fin.natAdd n i)))
  linarith

lemma finiteMaximum_append_sum {n m : ℕ} (f : (Fin n → Bool) → ℝ)
    (g : (Fin m → Bool) → ℝ) :
    finiteMaximum (fun σ : Fin (n+m) → Bool ↦
      f (fun i ↦ σ (Fin.castAdd m i))+g (fun i ↦ σ (Fin.natAdd n i))) =
    finiteMaximum f + finiteMaximum g := by
  apply le_antisymm
  · obtain ⟨σ,hσ⟩ := exists_finiteMaximum (fun σ : Fin (n+m) → Bool ↦
      f (fun i ↦ σ (Fin.castAdd m i))+g (fun i ↦ σ (Fin.natAdd n i)))
    rw [← hσ]
    exact add_le_add (le_finiteMaximum _ _) (le_finiteMaximum _ _)
  · obtain ⟨σ,hσ⟩ := exists_finiteMaximum f
    obtain ⟨τ,hτ⟩ := exists_finiteMaximum g
    have hh := le_finiteMaximum (fun η : Fin (n+m) → Bool ↦
      f (fun i ↦ η (Fin.castAdd m i))+g (fun i ↦ η (Fin.natAdd n i))) (Fin.append σ τ)
    simpa only [Fin.append_left,Fin.append_right,hσ,hτ] using hh

lemma expected_max_block (n m : ℕ) :
    (∫ J, finiteMaximum (linearProcess (blockCoeff n m) J)
      ∂gaussianProduct ((Fin n × Fin n) ⊕ (Fin m × Fin m))) =
    expectedMaximum n + expectedMaximum m := by
  have he := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin n × Fin n) ⊕ (Fin m × Fin m) ↦ standardGaussian)
  change (∫ J, finiteMaximum (linearProcess (blockCoeff n m) J)
    ∂Measure.pi (fun _ : (Fin n × Fin n) ⊕ (Fin m × Fin m) ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun J ↦ finiteMaximum (linearProcess (blockCoeff n m) J))]
  have hlin (p : ((Fin n × Fin n) → ℝ) × ((Fin m × Fin m) → ℝ)) :
      linearProcess (blockCoeff n m)
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin n × Fin n) ⊕ (Fin m × Fin m) ↦ ℝ)).symm p) =
      (fun σ ↦ linearProcess (hamCoeff n) p.1 (fun i ↦ σ (Fin.castAdd m i))+
        linearProcess (hamCoeff m) p.2 (fun i ↦ σ (Fin.natAdd n i))) := by
    funext σ
    simp [linearProcess,blockCoeff,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin,finiteMaximum_append_sum]
  change (∫ p, finiteMaximum (linearProcess (hamCoeff n) p.1)+
    finiteMaximum (linearProcess (hamCoeff m) p.2)
      ∂(gaussianProduct (Fin n × Fin n)).prod (gaussianProduct (Fin m × Fin m))) = _
  rw [integral_add ((finiteMaximum_integrable (hamCoeff n)).comp_fst _)
    ((finiteMaximum_integrable (hamCoeff m)).comp_snd _),
    integral_fun_fst (fun J ↦ finiteMaximum (linearProcess (hamCoeff n) J)),
    integral_fun_snd (fun J ↦ finiteMaximum (linearProcess (hamCoeff m) J))]
  simp [expectedMaximum]

lemma expectedMaximum_zero : expectedMaximum 0 = 0 := by
  have hh (J : (Fin 0 × Fin 0) → ℝ) : linearProcess (hamCoeff 0) J = fun _ ↦ 0 := by
    funext σ
    simp [linearProcess]
  simp [expectedMaximum,hh,finiteMaximum]

lemma expectedMaximum_superadditive (n m : ℕ) : expectedMaximum n + expectedMaximum m ≤ expectedMaximum (n+m) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [expectedMaximum_zero]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [expectedMaximum_zero]
  exact (expected_max_block n m).symm.le.trans
    (expected_max_le_of_pair_distances (blockCoeff n m) (hamCoeff (n+m)) (blockCoeff_distance_le hn hm))

lemma integrable_exp_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    Integrable (fun z ↦ Real.exp (linearProcess c z i)) (gaussianProduct κ) := by
  simpa only [gaussianProduct,standardGaussian,linearProcess,Real.exp_sum] using
    Integrable.fintype_prod (fun k : κ ↦ integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (c i k))

lemma integral_exp_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    (∫ z, Real.exp (linearProcess c z i) ∂gaussianProduct κ) = Real.exp ((∑ k, (c i k)^2)/2) := by
  simp only [gaussianProduct,linearProcess,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun k x ↦ Real.exp (c i k*x))]
  have hg (r : ℝ) : (∫ x, Real.exp (r*x) ∂standardGaussian) = Real.exp (r^2/2) := by
    simpa [mgf,standardGaussian] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) r
  simp_rw [hg]
  rw [← Real.exp_sum,Finset.sum_div]

lemma integral_logPartition_upper {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) :
    (∫ z, logPartition (linearProcess c z) ∂gaussianProduct κ) ≤
      Real.log (∑ i, Real.exp ((∑ k, (c i k)^2)/2)) := by
  let Z := fun z ↦ ∑ i, Real.exp (linearProcess c z i)
  let E := ∑ i, Real.exp ((∑ k, (c i k)^2)/2)
  have hZ : Integrable Z (gaussianProduct κ) := integrable_finsetSum _ (fun i _ ↦ integrable_exp_linearProcess c i)
  have hE : (∫ z, Z z ∂gaussianProduct κ) = E := by
    rw [integral_finsetSum _ (fun i _ ↦ integrable_exp_linearProcess c i)]
    simp only [integral_exp_linearProcess,E]
  have hEp : 0 < E := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hZp (z) : 0 < Z z := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hlog (z) : logPartition (linearProcess c z) ≤ Z z/E-1+Real.log E := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (hZp z) hEp)
    rw [Real.log_div (hZp z).ne' hEp.ne'] at hh
    exact sub_le_iff_le_add.mp hh
  have hh := integral_mono (logPartition_integrable c)
    (((hZ.div_const E).sub (integrable_const 1)).add (integrable_const (Real.log E))) hlog
  change (∫ z, logPartition (linearProcess c z) ∂gaussianProduct κ) ≤
    (∫ z, (Z z/E-1)+Real.log E ∂gaussianProduct κ) at hh
  rw [integral_add (f := fun z ↦ Z z/E-1) (g := fun _ ↦ Real.log E)
    ((hZ.div_const E).sub (integrable_const 1)) (integrable_const _),
    integral_sub (f := fun z ↦ Z z/E) (g := fun _ ↦ 1) (hZ.div_const E) (integrable_const 1),
    integral_div,hE] at hh
  simpa only [div_self hEp.ne',integral_const,probReal_univ,one_smul,sub_self,zero_add] using hh

lemma upper_triangle_count_bound (n : ℕ) :
    2*(∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) ≤ (n : ℝ)^2 := by
  have h := twice_upper_sum (fun i j : Fin n ↦ if i=j then (0 : ℝ) else 1)
    (fun i j ↦ by simp only [eq_comm]) (fun i ↦ by simp)
  have he : (∑ i : Fin n, ∑ j : Fin n, if i < j then (if i=j then (0 : ℝ) else 1) else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp [hij,ne_of_lt hij]
    · simp [hij]
  rw [he] at h
  rw [h]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> norm_num
    _ = _ := by simp; ring

lemma hamCoeff_variance_bound (n : ℕ) (σ : Fin n → Bool) :
    (∑ k, (hamCoeff n σ k)^2) ≤ (n : ℝ)/2 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (∑ k, (hamCoeff n σ k)^2) = (n : ℝ)⁻¹ *
      ∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0 := by
    simp only [hamCoeff,Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rw [mul_pow,mul_pow,spin_sq,spin_sq,inv_pow,Real.sq_sqrt hn'.le]
      ring
    · ring
  rw [he,← div_eq_inv_mul]
  apply (div_le_iff₀ hn').2
  have hh := upper_triangle_count_bound n
  nlinarith

lemma expectedMaximum_upper (n : ℕ) :
    expectedMaximum n ≤ (n : ℝ)*(Real.log 2+1/4) := by
  have hmax (J) : finiteMaximum (linearProcess (hamCoeff n) J) ≤
      logPartition (linearProcess (hamCoeff n) J) := by
    obtain ⟨σ,hσ⟩ := exists_finiteMaximum (linearProcess (hamCoeff n) J)
    rw [← hσ]
    exact le_logPartition _ _
  have hsum : (∑ σ : Fin n → Bool, Real.exp ((∑ k, (hamCoeff n σ k)^2)/2)) ≤
      (2 : ℝ)^n * Real.exp ((n : ℝ)/4) := by
    calc
      _ ≤ ∑ σ : Fin n → Bool, Real.exp ((n : ℝ)/4) := by
        apply Finset.sum_le_sum
        intro σ _
        apply Real.exp_le_exp.mpr
        have hh := hamCoeff_variance_bound n σ
        linarith
      _ = _ := by simp
  have hsumpos : (0 : ℝ) < ∑ σ : Fin n → Bool, Real.exp ((∑ k, (hamCoeff n σ k)^2)/2) :=
    Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty
  calc
    expectedMaximum n ≤ ∫ J, logPartition (linearProcess (hamCoeff n) J) ∂gaussianProduct (Fin n × Fin n) :=
      integral_mono (finiteMaximum_integrable (hamCoeff n)) (logPartition_integrable (hamCoeff n)) hmax
    _ ≤ Real.log (∑ σ : Fin n → Bool, Real.exp ((∑ k, (hamCoeff n σ k)^2)/2)) :=
      integral_logPartition_upper (hamCoeff n)
    _ ≤ Real.log ((2 : ℝ)^n*Real.exp ((n : ℝ)/4)) := Real.log_le_log hsumpos hsum
    _ = _ := by rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (Real.exp_ne_zero _),Real.log_pow,Real.log_exp]; ring

theorem groundStateSequence_tendsto :
    Tendsto groundStateSequence atTop (𝓝 groundStateValue) := by
  let u : ℕ → ℝ := fun n ↦ -expectedMaximum n
  have hu : Subadditive u := by
    intro n m
    dsimp [u]
    linarith [expectedMaximum_superadditive n m]
  have hC : 0 ≤ Real.log 2+1/4 := by positivity
  have hb : BddBelow (range (fun n : ℕ ↦ u n/n)) := by
    refine ⟨-(Real.log 2+1/4), ?_⟩
    rintro y ⟨n,rfl⟩
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [Nat.cast_zero,div_zero]
      linarith
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hh : expectedMaximum n/n ≤ Real.log 2+1/4 := by
      apply (div_le_iff₀ hn').2
      simpa only [mul_comm] using expectedMaximum_upper n
    dsimp [u]
    rw [neg_div]
    linarith
  apply tendsto_nhds_limUnder
  refine ⟨-hu.lim, ?_⟩
  have hh := (hu.tendsto_lim hb).neg
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp [groundStateSequence_eq,u,div_eq_mul_inv,mul_comm]

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_Volterra
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter Function
open scoped Topology NNReal Nat
namespace SKValue
namespace VolterraData
variable {T:ℝ} {hT:0≤T} (D:VolterraData T hT)
lemma next_apply (Y:C(Icc (0:ℝ) T,ℝ)) (t:Icc (0:ℝ) T):
    D.next Y t=∫s in (0:ℝ)..(t:ℝ),D.field s (Y (projIcc 0 T hT s)) :=rfl
lemma integ_to (Y:C(Icc (0:ℝ) T,ℝ)) (t:Icc (0:ℝ) T):
    IntervalIntegrable (fun s ↦ D.field s (Y (projIcc 0 T hT s))) volume 0 t := by
  apply (D.integ Y).mono_set
  rw [uIcc_of_le t.2.1,uIcc_of_le hT]
  exact Icc_subset_Icc le_rfl t.2.2
lemma iterate_bound (Y Z:C(Icc (0:ℝ) T,ℝ)) (n:ℕ) (t:Icc (0:ℝ) T):
    dist ((D.next)^[n] Y t) ((D.next)^[n] Z t)≤
      (D.lip*|((t:ℝ)-0)|)^n/n.factorial*dist Y Z := by
  induction n generalizing t with
  | zero=>simpa using ContinuousMap.dist_apply_le_dist (f:=Y) (g:=Z) t
  | succ n hn=>
    rw [iterate_succ_apply',iterate_succ_apply',dist_eq_norm,next_apply,next_apply,
      ←intervalIntegral.integral_sub (D.integ_to _ t) (D.integ_to _ t)]
    calc
      _≤∫s in uIoc (0:ℝ) (t:ℝ),(D.lip:ℝ)^(n+1)*|s-0|^n/n.factorial*dist Y Z := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply norm_integral_le_of_norm_le ((by fun_prop:Continuous (fun s:ℝ ↦
          (D.lip:ℝ)^(n+1)*|s-0|^n/n.factorial*dist Y Z)).integrableOn_uIoc)
        filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
        rw [uIoc_of_le t.2.1] at hs
        have hsT:s∈Icc (0:ℝ) T:=⟨hs.1.le,hs.2.trans t.2.2⟩
        rw [←dist_eq_norm]
        have hp:=D.bound s hsT ((D.next)^[n] Y (projIcc 0 T hT s)) ((D.next)^[n] Z (projIcc 0 T hT s))
        have hh:=hn (⟨s,hsT⟩:Icc (0:ℝ) T)
        have he:projIcc 0 T hT s=(⟨s,hsT⟩:Icc (0:ℝ) T):=projIcc_of_mem hT hsT
        rw [he] at hp ⊢
        apply hp.trans
        calc
          _≤(D.lip:ℝ)*((D.lip*|s-0|)^n/n.factorial*dist Y Z):=mul_le_mul_of_nonneg_left hh D.lip.coe_nonneg
          _=_:=by rw [mul_pow,pow_succ];ring
      _≤_:=by
        apply le_of_abs_le
        rw [←intervalIntegral.abs_intervalIntegral_eq,intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div,intervalIntegral.integral_const_mul,abs_mul,abs_div,
          abs_mul,intervalIntegral.abs_intervalIntegral_eq,integral_pow_abs_sub_uIoc,abs_div,
          abs_pow,abs_pow,abs_dist,NNReal.abs_eq,abs_abs,mul_div,div_div,←abs_mul,
          ←Nat.cast_succ,←Nat.cast_mul,←Nat.factorial_succ,Nat.abs_cast,←mul_pow]
lemma exists_fixedPoint:∃Y:C(Icc (0:ℝ) T,ℝ),D.next Y=Y := by
  obtain ⟨n,hn⟩:= (FloorSemiring.tendsto_pow_div_factorial_atTop ((D.lip:ℝ)*T)).eventually
    (gt_mem_nhds zero_lt_one) |>.exists
  have hn0:0≤((D.lip:ℝ)*T)^n/n.factorial:=by positivity
  have hc:ContractingWith ⟨((D.lip:ℝ)*T)^n/n.factorial,hn0⟩ (D.next)^[n] := by
    refine ⟨hn,LipschitzWith.of_dist_le_mul (fun Y Z ↦ ?_)⟩
    rw [ContinuousMap.dist_le]
    · intro t
      apply (D.iterate_bound Y Z n t).trans
      simp only [sub_zero,abs_of_nonneg t.2.1]
      change (D.lip*↑t)^n/n.factorial*dist Y Z ≤ ((D.lip:ℝ)*T)^n/n.factorial*dist Y Z
      gcongr
      · exact mul_nonneg D.lip.coe_nonneg t.2.1
      · exact t.2.2
    · positivity
  exact ⟨_,hc.isFixedPt_fixedPoint_iterate⟩
end VolterraData
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
lemma exists_local_diffusion_path (W:BrownianSpace) (γ:OrderParameter) {T:ℝ}
    (hT:T∈Ico (0:ℝ) 1) (b:ℝ → ℝ) (hb:ContinuousOn b (Icc (0:ℝ) T)):
    ∃X:ℝ → ℝ,ContinuousOn X (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (X s)) volume 0 T ∧
      ∀t∈Icc (0:ℝ) T,X t=b t+∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (X s) := by
  obtain ⟨K,L,Lu,hLu,hG,hu⟩:=(sourceStripRegularity W γ).core T hT
  have hg0:0≤γ.coeff T:=γ.nonneg T hT
  have hi:IntervalIntegrable γ.coeff volume 0 T:=γ.intervalIntegrable.mono_set (by
    rw [uIcc_of_le hT.1,uIcc_of_le (by norm_num:(0:ℝ)≤1)];exact Icc_subset_Icc le_rfl hT.2.le)
  have hj:=derivative_joint_continuous hLu hu
  let D:VolterraData T hT.1:={
    field:=fun t y ↦ γ.coeff t*gradient W γ t (b t+y)
    lip:=⟨γ.coeff T*Lu,mul_nonneg hg0 hLu⟩
    bound:=by
      intro t ht x y
      have hg:0≤γ.coeff t:=γ.nonneg t ⟨ht.1,ht.2.trans_lt hT.2⟩
      have hgt:γ.coeff t≤γ.coeff T:=γ.monotone ⟨ht.1,ht.2.trans_lt hT.2⟩ hT ht.2
      simp only [Real.dist_eq,←mul_sub,abs_mul,abs_of_nonneg hg]
      have hh:=hu t ht t ht (b t+x) (b t+y)
      simp only [sub_self,abs_zero,zero_add,add_sub_add_left_eq_sub] at hh
      change _≤(γ.coeff T*Lu)*|x-y|
      calc
        _≤γ.coeff t*(Lu*|x-y|):=mul_le_mul_of_nonneg_left hh hg
        _≤γ.coeff T*(Lu*|x-y|):=mul_le_mul_of_nonneg_right hgt (by positivity)
        _=_:=by ring
    integ:=by
      intro Y
      apply hi.mul_continuousOn
      rw [uIcc_of_le hT.1]
      apply hj.comp (continuousOn_id.prodMk (hb.add ((Y.continuous.comp continuous_projIcc).continuousOn)))
      exact fun t ht ↦ ht }
  obtain ⟨Y,hY⟩:=D.exists_fixedPoint
  let X:=fun t ↦ b t+Y (projIcc 0 T hT.1 t)
  have hXcont:ContinuousOn X (Icc (0:ℝ) T):=hb.add ((Y.continuous.comp continuous_projIcc).continuousOn)
  refine ⟨X,hXcont,D.integ Y,?_⟩
  intro t ht
  have he:=congrArg (fun f:C(Icc (0:ℝ) T,ℝ) ↦ f ⟨t,ht⟩) hY
  change (∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (X s))=Y ⟨t,ht⟩ at he
  dsimp only [X]
  rw [projIcc_of_mem hT.1 ht,he]
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_EulerLimitProcess
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
lemma eulerLimitProcess_zero (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω):eulerLimitProcess W γ 0 z=0 :=by
  simp [eulerLimitProcess]
lemma eulerLimitProcess_measurable (W:BrownianSpace) (γ:OrderParameter) (t:ℝ):
    StronglyMeasurable[W.filtration t.toNNReal] (eulerLimitProcess W γ t) := by
  by_cases ht:0<t ∧ t<1
  · change StronglyMeasurable[W.filtration t.toNNReal] (fun z ↦ if 0<t ∧ t<1 then limsup (fun N:ℕ ↦ coupledEuler t γ.coeff (gradient W γ) W.B N N z) atTop else 0)
    simp only [ite_eq_left ht]
    apply Measurable.stronglyMeasurable
    apply Measurable.limsup
    intro N
    by_cases hN:N=0
    · subst N
      exact measurable_const
    have hN':0<N:=Nat.pos_of_ne_zero hN
    have hh:=coupled_euler_past_measurable W.measurable ht.1 hN' γ.coeff (gradient W γ)
      (fun j hj ↦ ((phi_evolution W γ ⟨ht.1.le,ht.2⟩).slices _ (mesh_time_mem ht.1.le hN' hj.le)).jets.smooth.continuous.measurable) N le_rfl
    have he:meshTime t N N=t:=by dsimp [meshTime,stepSize];field_simp
    rw [he] at hh
    exact hh.measurable
  · change StronglyMeasurable[W.filtration t.toNNReal] (fun z ↦ if 0<t ∧ t<1 then limsup (fun N:ℕ ↦ coupledEuler t γ.coeff (gradient W γ) W.B N N z) atTop else 0)
    simp only [ite_eq_right ht]
    exact stronglyMeasurable_const
lemma eulerLimitProcess_eq_path (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω)
    {T:ℝ} (hT:T∈Ico (0:ℝ) 1) {X:ℝ → ℝ}
    (hc:ContinuousOn X (Icc (0:ℝ) T))
    (hi:IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (X s)) volume 0 T)
    (he:∀t∈Icc (0:ℝ) T,X t=W.B t.toNNReal z+∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (X s))
    (h0:X 0=0) {t:ℝ} (ht:t∈Icc (0:ℝ) T):eulerLimitProcess W γ t z=X t := by
  rcases ht.1.eq_or_lt with htz|htz
  · subst t
    rw [eulerLimitProcess_zero,h0]
  have ht1:t<1:=ht.2.trans_lt hT.2
  obtain ⟨K,L,Lu,hLu,hG,hu⟩:=(sourceStripRegularity W γ).core t ⟨htz.le,ht1⟩
  have hsub:Icc (0:ℝ) t⊆Icc (0:ℝ) T:=Icc_subset_Icc le_rfl ht.2
  have hi':IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (X s)) volume 0 t:=hi.mono_set (by
    rw [uIcc_of_le htz.le,uIcc_of_le hT.1];exact hsub)
  have hv:=driven_euler_uniform_convergence
    (Y:=fun N j ↦ coupledEuler t γ.coeff (gradient W γ) W.B N j z) htz.le hLu
    (γ.monotone.mono (fun s hs ↦ ⟨hs.1,hs.2.trans_lt ht1⟩))
    (γ.nonneg 0 (by norm_num)) (fun s hs x ↦ gradient_bound W γ ⟨hs.1,hs.2.trans ht1.le⟩ x)
    hu (hc.mono hsub) hi' (fun s hs ↦ he s (hsub hs)) h0
    (fun N ↦ coupled_euler_zero t γ.coeff (gradient W γ) W.B N z)
    (fun N hN j hj ↦ coupled_euler_step W.B htz γ.coeff (gradient W γ) hN hj z)
  have hl:Tendsto (fun N:ℕ ↦ coupledEuler t γ.coeff (gradient W γ) W.B N N z) atTop (𝓝 (X t)) :=by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩:=eventually_atTop.mp (hv ε hε)
    refine ⟨max N 1,?_⟩
    intro n hn
    have hnpos:0<n:= lt_of_lt_of_le (by norm_num:(0:ℕ)<1) ((le_max_right N 1).trans hn)
    have hh:=hN n ((le_max_left N 1).trans hn) n le_rfl
    have hnt:(n:ℝ)*(t/n)=t:=by field_simp
    simpa only [hnt,Real.dist_eq] using hh
  simpa only [eulerLimitProcess,ite_eq_left (show 0<t ∧ t<1 from ⟨htz,ht1⟩)] using hl.limsup_eq
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
lemma eulerLimitProcess_local_path (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω)
    (hb:Continuous (fun t:ℝ ↦ W.B t.toNNReal z)) (h0:W.B 0 z=0)
    {T:ℝ} (hT:T∈Ico (0:ℝ) 1):
    ContinuousOn (fun t ↦ eulerLimitProcess W γ t z) (Icc (0:ℝ) T) ∧
    IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (eulerLimitProcess W γ s z)) volume 0 T ∧
    ∀t∈Icc (0:ℝ) T,eulerLimitProcess W γ t z=W.B t.toNNReal z+
      ∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (eulerLimitProcess W γ s z) :=by
  obtain ⟨X,hc,hi,he⟩:=exists_local_diffusion_path W γ hT _ hb.continuousOn
  have hz:X 0=0:=by simpa only [Real.toNNReal_zero,h0,intervalIntegral.integral_same,add_zero] using he 0 ⟨le_rfl,hT.1⟩
  have heq (t:ℝ) (ht:t∈Icc (0:ℝ) T):eulerLimitProcess W γ t z=X t:=
    eulerLimitProcess_eq_path W γ z hT hc hi he hz ht
  refine ⟨hc.congr heq,hi.congr (fun s hs ↦ ?_),?_⟩
  · rw [uIoc_of_le hT.1] at hs
    rw [heq s ⟨hs.1.le,hs.2⟩]
  intro t ht
  rw [heq t ht,he t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  dsimp only
  rw [heq s ⟨hs.1,hs.2.trans ht.2⟩]
lemma continuousOn_preterminal_of_strips {f:ℝ → ℝ}
    (h:∀T∈Ico (0:ℝ) 1,ContinuousOn f (Icc (0:ℝ) T)):
    ContinuousOn f (Ico (0:ℝ) 1) :=by
  intro t ht
  obtain ⟨T,htT,hT⟩:=exists_between ht.2
  apply (h T ⟨ht.1.trans htT.le,hT⟩ t ⟨ht.1,htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩
lemma eulerLimitProcess_drift_integrable (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω)
    (hb:Continuous (fun t:ℝ ↦ W.B t.toNNReal z)) (h0:W.B 0 z=0):
    IntervalIntegrable (fun s ↦ γ.coeff s*gradient W γ s (eulerLimitProcess W γ s z)) volume 0 1 :=by
  have hu:ContinuousOn (fun s ↦ gradient W γ s (eulerLimitProcess W γ s z)) (Ico (0:ℝ) 1):=by
    apply continuousOn_preterminal_of_strips
    intro T hT
    obtain ⟨K,L,Lu,hLu,hG,hLip⟩:=(sourceStripRegularity W γ).core T hT
    have hj:ContinuousOn (fun p:ℝ×ℝ ↦ gradient W γ p.1 p.2) {p | p.1∈Icc (0:ℝ) T}:=
      derivative_joint_continuous hLu hLip
    have hp:ContinuousOn (fun s ↦ (s,eulerLimitProcess W γ s z)) (Icc (0:ℝ) T):=
      continuousOn_id.prodMk (eulerLimitProcess_local_path W γ z hb h0 hT).1
    exact ContinuousOn.comp (g:=fun p:ℝ×ℝ ↦ gradient W γ p.1 p.2)
      (f:=fun s ↦ (s,eulerLimitProcess W γ s z)) hj hp (fun s hs ↦ hs)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num:(0:ℝ)≤1)).mpr
  have hm:AEStronglyMeasurable (fun s ↦ gradient W γ s (eulerLimitProcess W γ s z)) (volume.restrict (Ioc (0:ℝ) 1)) :=by
    rw [←Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (hu.mono Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo
  apply γ.integrable.mul_bdd hm (c:=(1:ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simpa only [Real.norm_eq_abs] using gradient_bound W γ ⟨hs.1.le,hs.2⟩ (eulerLimitProcess W γ s z)
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_DiffusionExistence
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
lemma terminalEulerProcess_measurable (W:BrownianSpace) (γ:OrderParameter):
    StronglyMeasurable[W.filtration 1] (terminalEulerProcess W γ) :=by
  apply Measurable.stronglyMeasurable
  apply Measurable.limsup
  intro n
  apply ((eulerLimitProcess_measurable W γ (terminalTime n)).mono ?_).measurable
  apply W.filtration.mono
  exact Real.toNNReal_le_iff_le_coe.mpr (terminalTime_mem n).2.le
lemma diffusionProcess_measurable (W:BrownianSpace) (γ:OrderParameter) {t:ℝ}:
    StronglyMeasurable[W.filtration t.toNNReal] (diffusionProcess W γ t) :=by
  change StronglyMeasurable[W.filtration t.toNNReal] (fun z ↦ if t<1 then eulerLimitProcess W γ t z else terminalEulerProcess W γ z)
  by_cases ht:t<1
  · simp only [ite_eq_left ht]
    exact eulerLimitProcess_measurable W γ t
  · simp only [ite_eq_right ht]
    apply (terminalEulerProcess_measurable W γ).mono (W.filtration.mono ?_)
    exact (Real.le_toNNReal_iff_coe_le (zero_le_one.trans (not_lt.mp ht))).mpr (not_lt.mp ht)
lemma diffusionProcess_adapted (W:BrownianSpace) (γ:OrderParameter):
    Adapted W.filtration (fun t z ↦ diffusionProcess W γ (min (t:ℝ) 1) z) :=by
  intro t
  apply ((diffusionProcess_measurable W γ (t:=min (t:ℝ) 1)).mono ?_).measurable
  apply W.filtration.mono
  exact Real.toNNReal_le_iff_le_coe.mpr (min_le_left _ _)
lemma diffusionProcess_path (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω)
    (hb:Continuous (fun t:ℝ ↦ W.B t.toNNReal z)) (h0:W.B 0 z=0):
    ContinuousOn (fun t ↦ diffusionProcess W γ t z) (Icc (0:ℝ) 1) ∧
    ∀t∈Icc (0:ℝ) 1,diffusionProcess W γ t z=W.B t.toNNReal z+
      ∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (diffusionProcess W γ s z) :=by
  let f:=fun s ↦ γ.coeff s*gradient W γ s (eulerLimitProcess W γ s z)
  let F:=fun t ↦ W.B t.toNNReal z+∫s in (0:ℝ)..t,f s
  have hi:IntervalIntegrable f volume 0 1:=eulerLimitProcess_drift_integrable W γ z hb h0
  have hc:ContinuousOn F (Icc (0:ℝ) 1):=by
    apply hb.continuousOn.add
    simpa only [uIcc_of_le (by norm_num:(0:ℝ)≤1)] using
      intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have he:∀t∈Ico (0:ℝ) 1,eulerLimitProcess W γ t z=F t:=by
    intro t ht
    exact (eulerLimitProcess_local_path W γ z hb h0 ht).2.2 t ⟨ht.1,le_rfl⟩
  have hl:Tendsto (fun n ↦ eulerLimitProcess W γ (terminalTime n) z) atTop (𝓝 (F 1)):=by
    have htime:Tendsto terminalTime atTop (𝓝[Icc (0:ℝ) 1] (1:ℝ)):=
      tendsto_nhdsWithin_iff.mpr ⟨(tendsto_nhdsWithin_iff.mp terminalTime_tendsto).1,
        Eventually.of_forall (fun n ↦ ⟨(terminalTime_mem n).1,(terminalTime_mem n).2.le⟩)⟩
    apply ((hc 1 ⟨by norm_num,le_rfl⟩).tendsto.comp htime).congr
    intro n
    exact (he _ (terminalTime_mem n)).symm
  have hU:terminalEulerProcess W γ z=F 1:=hl.limsup_eq
  have hEq (t:ℝ) (ht:t∈Icc (0:ℝ) 1):diffusionProcess W γ t z=F t:=by
    by_cases ht1:t<1
    · simpa only [diffusionProcess,ite_eq_left ht1] using he t ⟨ht.1,ht1⟩
    · have ht':t=1:=le_antisymm ht.2 (not_lt.mp ht1)
      subst t
      simpa only [diffusionProcess,lt_self_iff_false,ite_false] using hU
  refine ⟨hc.congr hEq,?_⟩
  intro t ht
  rw [hEq t ht]
  change W.B t.toNNReal z+(∫s in (0:ℝ)..t,f s)=_
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le ht.1
  intro s hs
  simp only [f,diffusionProcess,ite_eq_left (hs.2.trans_le ht.2)]
theorem diffusionProcess_isDiffusion (W:BrownianSpace) (γ:OrderParameter):IsDiffusion W γ (diffusionProcess W γ) :=by
  refine ⟨diffusionProcess_adapted W γ,?_⟩
  filter_upwards [W.brownian.cont,W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with z hz h0
  exact diffusionProcess_path W γ z (hz.comp (by fun_prop:Continuous (fun t:ℝ ↦ t.toNNReal))) h0
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_WeakGuerra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma logCoshTerminal_ge_abs {M : ℝ} (hM : 0<M) (x : ℝ) :
    |x|≤logCoshTerminal M x := by
  have hh := (log_two_cosh_bounds (M*x)).1
  rw [abs_mul,abs_of_pos hM] at hh
  exact (le_div_iff₀ hM).mpr (by simpa only [mul_comm] using hh)

lemma OrderParameter.weighted_cutoff_integral (γ : OrderParameter) :
    (∫ t in (0 : ℝ)..1,t*γ.cutoff t)=∫ t in (0 : ℝ)..1,t*γ.coeff t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t hne ht
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)] at ht
  have ht' : t∈Ico (0 : ℝ) 1 := ⟨ht.1.le,lt_of_le_of_ne ht.2 hne⟩
  simp only [OrderParameter.cutoff,indicator_of_mem ht']

lemma OrderParameter.weighted_grid_error (γ : OrderParameter) (j : ℕ) :
    |(∫ t in (0 : ℝ)..1,t*profileCoeff (γ.grid j) t)-(∫ t in (0 : ℝ)..1,t*γ.cutoff t)|≤γ.gridError j := by
  have hi : IntervalIntegrable (profileCoeff (γ.grid j)) volume 0 1 :=
    γ.grid_time j ▸ profileCoeff_integrable (γ.grid j)
  have hj : IntervalIntegrable γ.cutoff volume 0 1 := γ.cutoff_integrable.intervalIntegrable
  have hiw := hi.continuousOn_mul (continuous_id : Continuous (fun t : ℝ ↦ t)).continuousOn
  have hjw := hj.continuousOn_mul (continuous_id : Continuous (fun t : ℝ ↦ t)).continuousOn
  simp only [id_eq] at hiw hjw
  rw [←intervalIntegral.integral_sub hiw hjw]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1,|t*profileCoeff (γ.grid j) t-t*γ.cutoff t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1,|profileCoeff (γ.grid j) t-γ.cutoff t| := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hiw.sub hjw).abs (hi.sub hj).abs
      intro t ht
      rw [←mul_sub,abs_mul,abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (abs_nonneg _) ht.2
    _ = γ.gridError j := rfl

lemma OrderParameter.weighted_grid_tendsto (γ : OrderParameter) :
    Tendsto (fun j ↦ ∫ t in (0 : ℝ)..1,t*profileCoeff (γ.grid j) t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1,t*γ.coeff t)) := by
  rw [←γ.weighted_cutoff_integral]
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ ↦ abs_nonneg _) γ.weighted_grid_error γ.gridError_tendsto

theorem expectedMaximum_le_parisi (W : BrownianSpace) (γ : OrderParameter) {n : ℕ} (hn : 0<n) :
    SKValueG.expectedMaximum n≤(n : ℝ)*parisi W γ := by
  have ht := (smoothApprox_tendsto W γ).tendsto_at ((⟨0,by norm_num⟩ : Ico (0 : ℝ) 1),0)
  have hp := γ.weighted_grid_tendsto
  have hf : Tendsto (fun j ↦ (n : ℝ)*(smoothApprox γ j 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*profileCoeff (γ.grid j) t))) atTop (𝓝 ((n : ℝ)*parisi W γ)) := by
    simpa only [parisi] using tendsto_const_nhds.mul (ht.sub (tendsto_const_nhds.mul hp))
  apply ge_of_tendsto hf
  exact Eventually.of_forall (fun j ↦ SKValueG.weak_profile_guerra_upper W hn
    (logCoshTerminal_smoothTerminal (by positivity : (0 : ℝ)<j+1))
    (logCoshTerminal_ge_abs (by positivity)) (γ.grid_mono j) (γ.grid_time j))

theorem groundStateValue_le_parisi (W : BrownianSpace) (γ : OrderParameter) :
    groundStateValue≤parisi W γ := by
  have he : SKValueG.groundStateSequence=groundStateSequence := rfl
  have hev : SKValueG.groundStateValue=groundStateValue := rfl
  have ht := SKValueG.groundStateSequence_tendsto
  rw [he,hev] at ht
  apply le_of_tendsto ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change SKValueG.groundStateSequence n≤_
  rw [SKValueG.groundStateSequence_eq]
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_left (expectedMaximum_le_parisi W γ hn) (inv_nonneg.mpr hn'.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hn'.ne',one_mul] using hh

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_GradientSquareIntegral
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

lemma IsDiffusion.gradient_square_integral {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    (∫ ω, (gradient W γ T (X T ω))^2 ∂W.μ)=
      ∫ t in (0 : ℝ)..T, ∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
  exact diffusion_gradient_isometry W.brownian.toIsPreBrownianReal hT hT1.le hG
    hD hLu hLa hDb hu ha
    (fun t ht ↦ (hX.measurable ⟨ht.1,ht.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x))

lemma IsDiffusion.curvature_square_mean_continuous {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ) :
    ContinuousOn (fun t ↦ ∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ) (Ico (0 : ℝ) 1) := by
  intro t ht
  obtain ⟨T,htT,hT1⟩ := exists_between ht.2
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨ht.1.trans htT.le,hT1⟩
  have hc := mean_derivative_square_continuous hD hLa
    (fun s hs ↦ (hG.smooth s hs).continuous_deriv (by norm_num)) hDb ha
    (fun s hs ↦ (hX.measurable ⟨hs.1,hs.2.trans hT1.le⟩).aestronglyMeasurable)
    (hX.2.mono (fun _ hω ↦ hω.1.mono (Icc_subset_Icc le_rfl hT1.le)))
  apply (hc t ⟨ht.1,htT.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs hsT
  exact ⟨hs.1,hsT.le⟩

lemma continuous_eq_one_of_primitive {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ico (0 : ℝ) 1))
    (hi : ∀ t∈Ioo (0 : ℝ) 1, (∫ s in (0 : ℝ)..t, f s)=t) :
    ∀ t∈Ico (0 : ℝ) 1, f t=1 := by
  have hint (t : ℝ) (ht : t∈Ioo (0 : ℝ) 1) : f t=1 := by
    have hf : IntervalIntegrable f volume 0 t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1.le]
      exact hc.mono (fun s hs ↦ ⟨hs.1,hs.2.trans_lt ht.2⟩)
    have hs : Ico (0 : ℝ) 1∈𝓝 t := Ico_mem_nhds ht.1 ht.2
    have hd := intervalIntegral.integral_hasDerivAt_right hf
      ⟨Ico (0 : ℝ) 1,hs,hc.aestronglyMeasurable measurableSet_Ico⟩
      ((hc t ⟨ht.1.le,ht.2⟩).continuousAt hs)
    have he : (fun t ↦ ∫ s in (0 : ℝ)..t, f s)=ᶠ[𝓝 t] (id : ℝ → ℝ) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hi s hs
    exact hd.unique ((hasDerivAt_id t).congr_of_eventuallyEq he)
  intro t ht
  obtain h0|h0 := ht.1.eq_or_lt
  · subst t
    have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
      apply (hc 0 (by norm_num)).mono_left
      apply le_inf nhdsWithin_le_nhds
      apply le_principal_iff.mpr
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))] with s hs hs1
      exact ⟨hs.le,hs1⟩
    apply tendsto_nhds_unique hlim
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))] with s hs hs1
    exact (hint s ⟨hs,hs1⟩).symm
  · exact hint t ⟨h0,ht.2⟩

lemma IsDiffusion.curvature_unit_moment_of_contact {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (hreg : SourceStripRegularity W γ)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    ∀ t∈Ico (0 : ℝ) 1, (∫ ω, (curvature W γ t (X t ω))^2 ∂W.μ)=1 := by
  apply continuous_eq_one_of_primitive (hX.curvature_square_mean_continuous hreg)
  intro t ht
  rw [←hX.gradient_square_integral hreg ht.1 ht.2,hmom t ⟨ht.1.le,ht.2⟩]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_ContactAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma normalizer_pos_iff (W : BrownianSpace) (γ : OrderParameter) (T : ℝ) (N j : ℕ) :
    0<normalizer W γ T N j ↔
    0<∫ z,(rawCoefficient W γ T N j z)^2 ∂gaussianProduct (Fin (N+1)) := by
  unfold normalizer
  rw [inv_pos, Real.sqrt_pos]

lemma IsDiffusion.strip_value_le_groundState {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ)=t)
    {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    (∫ t in (0 : ℝ)..T,∫ ω,curvature W γ t (X t ω) ∂W.μ)≤groundStateValue := by
  have hreg := sourceStripRegularity W γ
  have hamom := hX.curvature_unit_moment_of_contact hreg hmom
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
  obtain ⟨hp,hl⟩ := hX.finite_gaussian_fixed_strip hT hT1 hG hD hLu hLa hDb hu ha
    (fun t ht ↦ hamom t ⟨ht.1,ht.2.trans_lt hT1⟩)
  apply le_of_tendsto hl
  filter_upwards [hp,eventually_gt_atTop (0 : ℕ)] with N hNpos hN
  exact shiftedCoefficientSum_le_groundState W γ hT.le hT1 hN
    (fun j hj ↦ (normalizer_pos_iff W γ T N j).mp (hNpos j hj))

theorem IsDiffusion.groundState_eq_parisi_of_contact {W : BrownianSpace}
    {γ : OrderParameter} {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    groundStateValue=parisi W γ := by
  have hreg := sourceStripRegularity W γ
  obtain ⟨U,hmart,hU,hU2,hP,hB,hA,hi,hl⟩ :=
    hX.parisi_value_assembly hreg hmom (hX.curvature_unit_moment_of_contact hreg hmom)
  refine le_antisymm (groundStateValue_le_parisi W γ) ?_
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
    (Ioi_mem_nhds (by norm_num : (0 : ℝ)<1))] with T hT1 hT
  exact hX.strip_value_le_groundState hmom hT hT1

theorem IsDiffusion.scalar_value_of_contact {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ)=t) :
    ScalarValueConclusion W γ X := by
  have hreg := sourceStripRegularity W γ
  obtain ⟨U,hmart,hU,hU2,hP,hB,hA,hi,hl⟩ :=
    hX.parisi_value_assembly hreg hmom (hX.curvature_unit_moment_of_contact hreg hmom)
  refine ⟨SKValueG.groundStateSequence_tendsto,U,hmart,hU,hU2,?_,?_,?_,hi⟩
  · exact (hX.groundState_eq_parisi_of_contact hmom).trans hP
  · exact (hX.groundState_eq_parisi_of_contact hmom).trans hB
  · exact (hX.groundState_eq_parisi_of_contact hmom).trans hA

theorem IsDiffusion.finite_gaussian_of_contact {W : BrownianSpace}
    {γ : OrderParameter} {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X)
    (hmom : ∀ t∈Ico (0 : ℝ) 1, (∫ ω,(gradient W γ t (X t ω))^2 ∂W.μ)=t)
    {T : ℝ} (hT : 0<T) (hT1 : T<1) : FiniteGaussianConclusion W γ X T := by
  have hreg := sourceStripRegularity W γ
  have hamom := hX.curvature_unit_moment_of_contact hreg hmom
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := hreg T ⟨hT.le,hT1⟩
  obtain ⟨hp,hl⟩ := hX.finite_gaussian_fixed_strip hT hT1 hG hD hLu hLa hDb hu ha
    (fun t ht ↦ hamom t ⟨ht.1,ht.2.trans_lt hT1⟩)
  obtain ⟨U,hmart,hU,hU2,hP,hB,hA,hi,hend⟩ := hX.parisi_value_assembly hreg hmom hamom
  refine ⟨hp,hl,?_⟩
  rwa [hX.groundState_eq_parisi_of_contact hmom]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_MainConclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue

theorem scalar_value_target (W:BrownianSpace) (γ:OrderParameter) (X:ℝ → W.Ω → ℝ)
    (hmin:IsMinimizer W γ) (hX:IsDiffusion W γ X):ScalarValueConclusion W γ X :=
  hX.scalar_value_of_contact (hmin.gradient_moment_contact hX)

theorem finite_gaussian_target (W:BrownianSpace) (γ:OrderParameter) (X:ℝ → W.Ω → ℝ)
    (T:ℝ) (hT:0<T) (hT1:T<1) (hmin:IsMinimizer W γ) (hX:IsDiffusion W γ X):
    FiniteGaussianConclusion W γ X T :=
  hX.finite_gaussian_of_contact (hmin.gradient_moment_contact hX) hT hT1
lemma IsMinimizer.ground_state_parisi_of_diffusion {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hmin:IsMinimizer W γ) (hX:IsDiffusion W γ X):groundStateValue=parisi W γ :=
  hX.groundState_eq_parisi_of_contact (hmin.gradient_moment_contact hX)

theorem ground_state_parisi_target (W:BrownianSpace) (γ:OrderParameter)
    (hmin:IsMinimizer W γ):groundStateValue=parisi W γ :=
  hmin.ground_state_parisi_of_diffusion (diffusionProcess_isDiffusion W γ)
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKValue

theorem value_consequences_oai :
    (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ),
      IsMinimizer W γ → IsDiffusion W γ X → ScalarValueConclusion W γ X) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter) (X : ℝ → W.Ω → ℝ) (T : ℝ),
      0 < T → T < 1 → IsMinimizer W γ → IsDiffusion W γ X →
      FiniteGaussianConclusion W γ X T) ∧
    (∀ (W : BrownianSpace) (γ : OrderParameter),
      IsMinimizer W γ → groundStateValue = parisi W γ) := by
  exact ⟨scalar_value_target, finite_gaussian_target, ground_state_parisi_target⟩

end SKValue

end OAI
end

theorem solution : type_of% @OAI.SKValue.value_consequences_oai := @OAI.SKValue.value_consequences_oai
