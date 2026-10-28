-- Prove2me | solution 1 for OAI.SKValue.IsDiffusion.momentExpr_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:54:24.865431+00:00
-- url     : https://prove2.me/submissions/b7e357fc-5701-424d-85ef-0b027f41b96c

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_phi_evolution
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

lemma BoundedSmoothFamily.iteratedDeriv {T : ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (n : ℕ) :
    BoundedSmoothFamily T (fun t ↦ iteratedDeriv n (F t)) := by
  induction n with
  | zero => exact h
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

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
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ForcedGenerator
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue

lemma ForcedTest.euler_one_step {T K L t δ x z:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) (ht:0 ≤ t) (hδ:0 ≤ δ) (hδ1:δ ≤ 1) (htδ:t+δ ≤ T) :
    let d:=Real.sqrt δ*z+δ*γ t*u t x
    |V (t+δ) (x+d)-V t x-δ*forcedSource γ u V b p t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2:ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) z+δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d:=Real.sqrt δ*z+δ*γ t*u t x
  have htT:t ≤ T := (le_add_of_nonneg_right hδ).trans htδ
  have hT:0 ≤ T := ht.trans htT
  have hsub:Icc t (t+δ) ⊆ Icc (0:ℝ) T := Icc_subset_Icc ht htδ
  have htm:t∈Icc (0:ℝ) T := ⟨ht,htT⟩
  have hem:t+δ∈Icc (0:ℝ) T := ⟨by linarith,htδ⟩
  have hTm:T∈Icc (0:ℝ) T := ⟨hT,le_rfl⟩
  have hbint (y:ℝ):IntervalIntegrable (fun s ↦ b s y) volume t (t+δ) :=
    (h.b_integrable y).mono_set (by rw [uIcc_of_le (by linarith:t ≤ t+δ),uIcc_of_le hT];exact hsub)
  have hpint (y:ℝ):IntervalIntegrable (fun s ↦ γ s*p s y) volume t (t+δ) :=
    (h.p_integrable y).mono_set (by rw [uIcc_of_le (by linarith:t ≤ t+δ),uIcc_of_le hT];exact hsub)
  have hgen:=gradient_generator_quadrature (b:=b) (p:=p) (y:=x+d)
    hδ (h.gamma_nonneg T hTm) h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub)
    (h.gamma_nonneg t htm) (h.gamma_mono htm hTm htT)
    (fun s hs ↦ h.p_bound s (hsub hs) _) (fun s hs ↦ h.b_lipschitz t htm s (hsub hs) x _)
    (fun s hs ↦ h.p_lipschitz t htm s (hsub hs) x _) (hbint _) (hpint _)
  have htime:|(V (t+δ) (x+d)-V t x+u t x-δ*forcedSource γ u V b p t x)-
      (V t (x+d)-V t x+u t x)+δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*u t x*deriv (V t) x)| ≤
      δ*(((1/2:ℝ)+γ T)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq:(V (t+δ) (x+d)-V t x+u t x-δ*forcedSource γ u V b p t x)-
        (V t (x+d)-V t x+u t x)+δ*((1/2:ℝ)*deriv (deriv (V t)) x+γ t*u t x*deriv (V t) x)=
        (V (t+δ) (x+d)-V t (x+d))-δ*((1/2:ℝ)*b t x+γ t*p t x) := by
      unfold forcedSource;ring
    rw [heq,h.pde t htm (t+δ) hem]
    simpa only [add_sub_cancel_left] using hgen
  have hspace:|(V t (x+d)-V t x+u t x)-u t x-deriv (V t) x*d-
      (1/2:ℝ)*deriv (deriv (V t)) x*d^2| ≤ K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound (h.smooth t htm) h.K_nonneg (h.third_bound t htm) x d
  have hh:=euler_cubic_remainder hδ hδ1 (h.gamma_nonneg T hTm) h.K_nonneg
    (mul_nonneg (by linarith [h.gamma_nonneg T hTm] : 0 ≤ 1/2+γ T) h.L_nonneg)
    (by rw [abs_of_nonneg (h.gamma_nonneg t htm)];exact h.gamma_mono htm hTm htT)
    (h.drift_bound t htm x) (h.second_bound t htm x) hspace htime
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  dsimp only [d,cubicEnvelope]
  ring
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma mean_observable_continuous {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsFiniteMeasure μ] {X:ℝ → Ω → ℝ} {T C:ℝ} {Q:ℝ → ℝ → ℝ}
    (hc:ContinuousOn (fun p:ℝ×ℝ ↦ Q p.1 p.2) (Icc (0:ℝ) T ×ˢ univ))
    (hb:∀ t∈Icc (0:ℝ) T,∀ x,|Q t x|≤C)
    (hXM:∀ t∈Icc (0:ℝ) T,AEStronglyMeasurable (X t) μ)
    (hXC:∀ᵐ z ∂μ,ContinuousOn (fun t ↦ X t z) (Icc (0:ℝ) T)) :
    ContinuousOn (fun t ↦ ∫ z,Q t (X t z) ∂μ) (Icc (0:ℝ) T) := by
  have hqc (t) (ht:t∈Icc (0:ℝ) T):Continuous (Q t) := by
    have hh : ContinuousOn (Q t) univ := hc.comp (continuousOn_const.prodMk continuousOn_id) (fun x _ ↦ ⟨ht,mem_univ x⟩)
    simpa only [continuousOn_univ] using hh
  apply continuousOn_of_dominated (bound:=fun _ ↦ C)
  · intro t ht
    exact ((hqc t ht).measurable.comp_aemeasurable (hXM t ht).aemeasurable).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hb t ht (X t z))
  · exact integrable_const _
  · filter_upwards [hXC] with z hz
    exact hc.comp (continuousOn_id.prodMk hz) (fun t ht ↦ ⟨ht,mem_univ _⟩)

lemma IsDiffusion.weightedObservable_tendsto {W:BrownianSpace} {γ:OrderParameter}
    {X:ℝ → W.Ω → ℝ} (hX:IsDiffusion W γ X) {T C:ℝ} (hT:0<T) (hT1:T<1)
    {η:ℝ → ℝ} (hη:MonotoneOn η (Icc (0:ℝ) T)) (hη0:0≤η 0)
    {Q:ℝ → ℝ → ℝ} (hC:0≤C) {D:ℝ≥0}
    (hc:ContinuousOn (fun p:ℝ×ℝ ↦ Q p.1 p.2) (Icc (0:ℝ) T ×ˢ univ))
    (hb:∀ t∈Icc (0:ℝ) T,∀ x,|Q t x|≤C)
    (hl:∀ t∈Icc (0:ℝ) T,LipschitzWith D (Q t)) :
    Tendsto (fun N ↦ stepSize T N*∑ j:Fin N,η (meshTime T N j)*
      (∫ z,Q (meshTime T N j) (euler T N γ.coeff (gradient W γ) z j) ∂gaussianProduct (Fin (N+1)))) atTop
      (𝓝 (∫ t in (0:ℝ)..T,η t*(∫ z,Q t (X t z) ∂W.μ))) := by
  obtain ⟨Kv,Lv,K,L,D',Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := sourceStripRegularity W γ T ⟨hT.le,hT1⟩
  let E (N:ℕ) := ∫ z,(meshMaxError T X (coupledEuler T γ.coeff (gradient W γ) W.B) N z)^2 ∂W.μ
  let f (t:ℝ) := ∫ z,Q t (X t z) ∂W.μ
  have hXM (t:ℝ) (ht:t∈Icc (0:ℝ) T):MemLp (X t) 2 W.μ := hX.memLp ⟨ht.1,ht.2.trans hT1.le⟩ (by norm_num)
  have hpaths := hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x)
  have hEl:Tendsto E atTop (𝓝 0) := coupled_euler_L2_convergence W.brownian.toIsPreBrownianReal
    hT hG hLu hu (fun t ht ↦ (hXM t ht).aestronglyMeasurable) hpaths
  have hEs:Tendsto (fun N ↦ Real.sqrt (E N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hEl
  have hf:ContinuousOn f (Icc (0:ℝ) T) := mean_observable_continuous hc hb
    (fun t ht ↦ (hXM t ht).aestronglyMeasurable) (hpaths.mono (fun _ hz ↦ hz.1))
  have hfB (t:ℝ) (ht:t∈Icc (0:ℝ) T):|f t|≤C := by
    simpa only [f,Real.norm_eq_abs,probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ:=W.μ) (C:=C) (f:=fun z ↦ Q t (X t z))
        (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hb t ht (X t z))))
  apply perturbed_monotone_weighted_grid_tendsto (r:=fun N ↦ (D:ℝ)*Real.sqrt (E N)) hT hC hη hη0 hf hfB
    (by simpa only [mul_zero] using hEs.const_mul (D:ℝ))
  filter_upwards [eventually_gt_atTop 0] with N hN j
  exact coupled_lipschitz_expectation_bound W.brownian.toIsPreBrownianReal hT hG hXM
    (hpaths.mono (fun _ hz ↦ hz.2.2)) hN j.isLt.le (hl _ (mesh_time_mem hT.le hN j.isLt.le))
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_PolynomialObservable
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace SKValue
lemma BoundedJoint.const (T c:ℝ):BoundedJoint T (fun _ _ ↦ c) := by
  refine ⟨⟨|c|,abs_nonneg c,fun _ _ _ ↦ le_rfl⟩,⟨0,le_rfl,?_⟩⟩
  intros;simp
lemma BoundedJoint.add {T:ℝ} {F G:ℝ → ℝ → ℝ} (hF:BoundedJoint T F) (hG:BoundedJoint T G):
    BoundedJoint T (fun t x ↦ F t x+G t x) := by
  obtain ⟨A,hA,hFA⟩:=hF.bounded;obtain ⟨B,hB,hGB⟩:=hG.bounded
  obtain ⟨L,hL,hFL⟩:=hF.joint;obtain ⟨M,hM,hGM⟩:=hG.joint
  refine ⟨⟨A+B,add_nonneg hA hB,fun t ht x ↦ (abs_add_le _ _).trans (add_le_add (hFA t ht x) (hGB t ht x))⟩,
    ⟨L+M,add_nonneg hL hM,?_⟩⟩
  intro t ht s hs x y
  calc
    _ = |(F s y-F t x)+(G s y-G t x)| := by congr 1;ring
    _ ≤ |F s y-F t x|+|G s y-G t x| := abs_add_le _ _
    _ ≤ L*(|s-t|+|y-x|)+M*(|s-t|+|y-x|) := add_le_add (hFL t ht s hs x y) (hGM t ht s hs x y)
    _ = _ := by ring
lemma BoundedJoint.mul {T:ℝ} {F G:ℝ → ℝ → ℝ} (hF:BoundedJoint T F) (hG:BoundedJoint T G):
    BoundedJoint T (fun t x ↦ F t x*G t x) := by
  obtain ⟨A,hA,hFA⟩:=hF.bounded;obtain ⟨B,hB,hGB⟩:=hG.bounded
  obtain ⟨L,hL,hFL⟩:=hF.joint;obtain ⟨M,hM,hGM⟩:=hG.joint
  refine ⟨⟨A*B,mul_nonneg hA hB,?_⟩,⟨L*B+A*M,by positivity,?_⟩⟩
  · intro t ht x;rw [abs_mul];exact mul_le_mul (hFA t ht x) (hGB t ht x) (abs_nonneg _) hA
  · intro t ht s hs x y
    calc
      _ = |(F s y-F t x)*G s y+F t x*(G s y-G t x)| := by congr 1;ring
      _ ≤ |(F s y-F t x)*G s y|+|F t x*(G s y-G t x)| := abs_add_le _ _
      _ ≤ L*(|s-t|+|y-x|)*B+A*(M*(|s-t|+|y-x|)) := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul (hFL t ht s hs x y) (hGB s hs y) (abs_nonneg _) (by positivity))
          (mul_le_mul (hFA t ht x) (hGM t ht s hs x y) (abs_nonneg _) hA)
      _ = _ := by ring
lemma BoundedJoint.continuous {T:ℝ} {F:ℝ → ℝ → ℝ} (hF:BoundedJoint T F):
    ContinuousOn (fun p:ℝ×ℝ ↦ F p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  obtain ⟨L,hL,hl⟩:=hF.joint
  have hh:LipschitzOnWith ⟨2*L,by positivity⟩ (fun p:ℝ×ℝ ↦ F p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    simp only [Real.dist_eq,Prod.dist_eq]
    have hb:=hl q.1 hq.1 p.1 hp.1 q.2 p.2
    change |F p.1 p.2-F q.1 q.2|≤(2*L)*max |p.1-q.1| |p.2-q.2|
    nlinarith [le_max_left |p.1-q.1| |p.2-q.2|,le_max_right |p.1-q.1| |p.2-q.2|]
  exact hh.continuousOn
lemma BoundedJoint.spatial {T:ℝ} {F:ℝ → ℝ → ℝ} (hF:BoundedJoint T F):
    ∃ L:ℝ≥0,∀ t∈Icc (0:ℝ) T,LipschitzWith L (F t) := by
  obtain ⟨L,hL,hl⟩:=hF.joint
  refine ⟨Real.toNNReal L,fun t ht ↦ ?_⟩
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [Real.coe_toNNReal _ hL,Real.dist_eq,sub_self,abs_zero,zero_add] using hl t ht t ht y x
lemma SmoothEvolution.polyJet_joint {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr):BoundedJoint T (polyJet V e) := by
  induction e with
  | const c => exact BoundedJoint.const T c
  | coord n =>
    obtain ⟨L,hL,hl⟩:=h.jet_joint n
    exact ⟨h.bound n,⟨L,hL,fun t ht s hs x y ↦ hl s hs t ht x y⟩⟩
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf
lemma SmoothEvolution.polyJet_smooth {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr) {t:ℝ} (ht:t∈Icc (0:ℝ) T):
    ContDiff ℝ ∞ (polyJet V e t) := by
  induction e with
  | const c => exact contDiff_const
  | coord n => exact ((h.slices t ht).jets.iteratedDeriv n).smooth
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf
lemma SmoothEvolution.polyJet_hasDeriv {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (x:ℝ):
    HasDerivAt (polyJet V e t) (polyJet V e.spatial t x) x := by
  apply JetExpr.hasDerivAt_eval
  intro n
  simpa only [JetExpr.eval,iteratedDeriv_succ] using
    (((h.slices t ht).jets.iteratedDeriv n).smooth.differentiable (by norm_num) x).hasDerivAt
lemma SmoothEvolution.polyJet_iterated {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (n:ℕ):
    iteratedDeriv n (polyJet V e t)=polyJet V (e.spatialIter n) t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (h.polyJet_hasDeriv _ ht x).deriv
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma BoundedSmoothFamily.at_continuous {T:ℝ} {F:ℝ → ℝ → ℝ}
    (h:BoundedSmoothFamily T F) (x:ℝ) : ContinuousOn (fun t ↦ F t x) (Icc (0:ℝ) T) := by
  have hh := (h.joint 0).comp (continuousOn_id.prodMk continuousOn_const) (fun t ht ↦ ⟨ht,mem_univ x⟩)
  simpa only [iteratedDeriv_zero,Function.comp_def,id_eq] using hh

lemma BoundedSmoothFamily.weightedFamilyIntegral_hasDerivAt {T a b : ℝ} {γ : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (h : BoundedSmoothFamily T F) (hi : IntervalIntegrable γ volume a b)
    (ha : 0≤a) (hab : a≤b) (hb : b≤T) (x : ℝ) :
    HasDerivAt (weightedFamilyIntegral a b γ F) (weightedFamilyIntegral a b γ (fun t ↦ _root_.deriv (F t)) x) x := by
  have hfi (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*F s u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.at_continuous u).mono (Icc_subset_Icc ha hb)
  have hf'i (u : ℝ) : IntervalIntegrable (fun s ↦ γ s*_root_.deriv (F s) u) volume a b := by
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hab] using (h.deriv.at_continuous u).mono (Icc_subset_Icc ha hb)
  obtain ⟨C,hC,hbd⟩ := h.bound 1
  simp only [iteratedDeriv_one] at hbd
  have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u s ↦ γ s*F s u)
    (F' := fun u s ↦ γ s*_root_.deriv (F s) u)
    (s := univ) (bound := fun s ↦ |γ s| * C) (μ := volume.restrict (Ioc a b))
    univ_mem (Eventually.of_forall (fun u ↦ ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi u)).aestronglyMeasurable))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hfi x))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hf'i x)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (hbd s ⟨ha.trans hs.1.le,hs.2.trans hb⟩ u) (abs_nonneg _))
    (hi'.abs.mul_const C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      intro u _
      have hfs := h.slices s ⟨ha.trans hs.1.le,hs.2.trans hb⟩
      exact ((hfs.smooth.differentiable (by norm_num)) u).hasDerivAt.const_mul (γ s))
  change HasDerivAt (fun u ↦ ∫ s in a..b, γ s*F s u)
    (∫ s in a..b, γ s*_root_.deriv (F s) x) x
  simpa only [intervalIntegral.integral_of_le hab] using hd.2

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HigherPDE
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace SKValue
lemma SmoothEvolution.jet_pde_ordered {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    {a b:ℝ} (ha:0≤a) (hab:a≤b) (hb:b≤T) (n:ℕ) (x:ℝ) :
    iteratedDeriv n (deriv (V b)) x-iteratedDeriv n (deriv (V a)) x=
      -(1/2:ℝ)*(weightedFamilyIntegral a b (fun _ ↦ 1)
        (fun t ↦ iteratedDeriv (n+2) (deriv (V t))) x)-
      weightedFamilyIntegral a b γ
        (fun t ↦ iteratedDeriv n (fun y ↦ deriv (V t) y*deriv (deriv (V t)) y)) x := by
  have haT:a∈Icc (0:ℝ) T := ⟨ha,hab.trans hb⟩
  have hbT:b∈Icc (0:ℝ) T := ⟨ha.trans hab,hb⟩
  have hfg:=h.gradient_family
  have hG:=hfg.mul hfg.deriv
  have hiab:IntervalIntegrable γ volume a b := hi.mono_set (by
    rw [uIcc_of_le hab,uIcc_of_le (ha.trans haT.2)]
    exact Icc_subset_Icc ha hb)
  induction n generalizing x with
  | zero =>
    have hh:=h.gradient_pde a haT b hbT x
    have hci:IntervalIntegrable (fun t ↦ deriv (deriv (deriv (V t))) x) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact (hfg.deriv.deriv.at_continuous x).mono (Icc_subset_Icc ha hb)
    have hpi:IntervalIntegrable (fun t ↦ γ t*(deriv (V t) x*deriv (deriv (V t)) x)) volume a b :=
      hiab.mul_continuousOn (by rw [uIcc_of_le hab];exact (hG.at_continuous x).mono (Icc_subset_Icc ha hb))
    rw [intervalIntegral.integral_add (hci.const_mul _) hpi,intervalIntegral.integral_const_mul] at hh
    simpa only [Nat.zero_add,weightedFamilyIntegral,iteratedDeriv_zero,
      show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,one_mul,neg_add_rev,
      neg_mul,sub_eq_add_neg,add_comm] using hh
  | succ n ih =>
    have hleft:=(((hfg.slices b hbT).iteratedDeriv n).smooth.differentiable (by norm_num) x).hasDerivAt.sub
      (((hfg.slices a haT).iteratedDeriv n).smooth.differentiable (by norm_num) x).hasDerivAt
    have hright:=((hfg.iteratedDeriv (n+2)).weightedFamilyIntegral_hasDerivAt
      (intervalIntegrable_const (c:=(1:ℝ))) ha hab hb x).const_mul (-(1/2:ℝ))
    have hright:=hright.sub ((hG.iteratedDeriv n).weightedFamilyIntegral_hasDerivAt hiab ha hab hb x)
    have hEq:(fun y ↦ iteratedDeriv n (deriv (V b)) y-iteratedDeriv n (deriv (V a)) y)=
      (fun y ↦ -(1/2:ℝ)*weightedFamilyIntegral a b (fun _ ↦ 1)
        (fun t ↦ iteratedDeriv (n+2) (deriv (V t))) y-
          weightedFamilyIntegral a b γ (fun t ↦ iteratedDeriv n
            (fun q ↦ deriv (V t) q*deriv (deriv (V t)) q)) y) := funext ih
    have he:=hleft.unique (hright.congr_of_eventuallyEq (Eventually.of_forall ih))
    simpa only [iteratedDeriv_succ,Nat.add_assoc] using he
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma SmoothEvolution.jet_time_hasDerivAt {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    {t:ℝ} (ht:t∈Ioo (0:ℝ) T) (hγ:ContinuousAt γ t) (n:ℕ) (x:ℝ):
    HasDerivAt (fun s ↦ iteratedDeriv n (deriv (V s)) x)
      (-(1/2:ℝ)*iteratedDeriv (n+2) (deriv (V t)) x-
        γ t*iteratedDeriv n (fun y ↦ deriv (V t) y*deriv (deriv (V t)) y) x) t := by
  let A:=fun s ↦ iteratedDeriv (n+2) (deriv (V s)) x
  let B:=fun s ↦ iteratedDeriv n (fun y ↦ deriv (V s) y*deriv (deriv (V s)) y) x
  have hA:ContinuousOn A (Icc (0:ℝ) T) := h.continuous_jet (n+2) x
  have hB:ContinuousOn B (Icc (0:ℝ) T) :=
    ((h.gradient_family.mul h.gradient_family.deriv).iteratedDeriv n).at_continuous x
  have hT:0≤T:=ht.1.le.trans ht.2.le
  have hiA:IntervalIntegrable A volume 0 T := by
    apply ContinuousOn.intervalIntegrable;simpa only [uIcc_of_le hT] using hA
  have hiB:IntervalIntegrable (fun s ↦ γ s*B s) volume 0 T :=
    hi.mul_continuousOn (by simpa only [uIcc_of_le hT] using hB)
  have htT:t∈Icc (0:ℝ) T:=⟨ht.1.le,ht.2.le⟩
  have hn:=Icc_mem_nhds ht.1 ht.2
  have hsub:uIcc (0:ℝ) t⊆uIcc (0:ℝ) T:=by
    rw [uIcc_of_le ht.1.le,uIcc_of_le hT];exact Icc_subset_Icc le_rfl ht.2.le
  have hAi:IntegrableOn A (Icc (0:ℝ) T) volume := by
    simpa only [uIcc_of_le hT] using (intervalIntegrable_iff').mp hiA
  have hBi:IntegrableOn (fun s ↦ γ s*B s) (Icc (0:ℝ) T) volume := by
    simpa only [uIcc_of_le hT] using (intervalIntegrable_iff').mp hiB
  have hdA:=intervalIntegral.integral_hasDerivAt_right (hiA.mono_set hsub)
    ⟨Icc (0:ℝ) T,hn,hAi.aestronglyMeasurable⟩ ((hA t htT).continuousAt hn)
  have hdB:=intervalIntegral.integral_hasDerivAt_right (hiB.mono_set hsub)
    ⟨Icc (0:ℝ) T,hn,hBi.aestronglyMeasurable⟩ (hγ.mul ((hB t htT).continuousAt hn))
  have hd:=((hasDerivAt_const t (iteratedDeriv n (deriv (V 0)) x)).add
    (hdA.const_mul (-(1/2:ℝ)))).sub hdB
  simp only [zero_add] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with s hs
  have he:=h.jet_pde_ordered hi (a:=0) (by norm_num) hs.1 hs.2 n x
  dsimp only [weightedFamilyIntegral] at he
  simp only [one_mul] at he
  change iteratedDeriv n (deriv (V s)) x=
    iteratedDeriv n (deriv (V 0)) x+(-(1/2:ℝ))*(∫ r in (0:ℝ)..s,A r)-∫ r in (0:ℝ)..s,γ r*B r
  dsimp only [A,B]
  linarith
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma SmoothEvolution.polyJet_time_hasDerivAt {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    {t:ℝ} (ht:t∈Ioo (0:ℝ) T) (hγ:ContinuousAt γ t) (e:JetExpr) (x:ℝ):
    HasDerivAt (fun s ↦ polyJet V e s x)
      ((1/2:ℝ)*polyJet V e.timeB t x+γ t*polyJet V e.timeP t x) t := by
  induction e with
  | const c => simpa only [polyJet,JetExpr.timeB,JetExpr.timeP,JetExpr.D,JetExpr.eval,mul_zero,add_zero] using hasDerivAt_const t c
  | coord n =>
    have hd:=h.jet_time_hasDerivAt hi ht hγ n x
    have he:=congrFun (h.polyJet_iterated (JetExpr.mul (.coord 0) (.coord 1)) ⟨ht.1.le,ht.2.le⟩ n) x
    have hf:polyJet V (JetExpr.mul (.coord 0) (.coord 1)) t=
        fun y ↦ deriv (V t) y*deriv (deriv (V t)) y := by
      funext y;simp only [polyJet,JetExpr.eval,iteratedDeriv_zero,iteratedDeriv_one]
    rw [hf] at he
    change _=JetExpr.eval (fun i ↦ iteratedDeriv i (deriv (V t)) x) _ at he
    simp only [polyJet,JetExpr.timeB,JetExpr.timeP,JetExpr.D,JetExpr.eval]
    rw [←he]
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    ring
  | add e f he hf =>
    convert he.add hf using 1 <;> (try (ext s; rfl))
    simp only [polyJet,JetExpr.timeB,JetExpr.timeP,JetExpr.D,JetExpr.eval]
    ring
  | mul e f he hf =>
    convert he.mul hf using 1 <;> (try (ext s; rfl))
    simp only [polyJet,JetExpr.timeB,JetExpr.timeP,JetExpr.D,JetExpr.eval]
    ring
lemma SmoothEvolution.polyJet_pde_ordered {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    (hm:MonotoneOn γ (Icc (0:ℝ) T)) {a b:ℝ} (ha:0≤a) (hab:a≤b) (hb:b≤T)
    (e:JetExpr) (x:ℝ):
    polyJet V e b x-polyJet V e a x=∫ s in a..b,
      ((1/2:ℝ)*polyJet V e.timeB s x+γ s*polyJet V e.timeP s x) := by
  obtain ⟨L,hL,hl⟩:=(h.polyJet_joint e).joint
  have hLip:LipschitzOnWith (Real.toNNReal L) (fun s ↦ polyJet V e s x) (uIcc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [uIcc_of_le hab] at hs ht
    simpa only [Real.coe_toNNReal _ hL,Real.dist_eq,sub_self,abs_zero,add_zero] using
      hl t ⟨ha.trans ht.1,ht.2.trans hb⟩ s ⟨ha.trans hs.1,hs.2.trans hb⟩ x x
  rw [←hLip.absolutelyContinuousOnInterval.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [monotoneOn_ae_continuousAt_interior hm,(Set.countable_singleton b).ae_notMem volume] with s hs hsb hsi
  rw [uIoc_of_le hab] at hsi
  have hst:s<T := (lt_of_le_of_ne hsi.2 (by simpa only [mem_singleton_iff] using hsb)).trans_le hb
  exact (h.polyJet_time_hasDerivAt hi ⟨ha.trans_lt hsi.1,hst⟩ (hs ⟨ha.trans_lt hsi.1,hst⟩) e x).deriv
lemma SmoothEvolution.polyJet_pde {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hi:IntervalIntegrable γ volume 0 T)
    (hm:MonotoneOn γ (Icc (0:ℝ) T)) {a b:ℝ} (ha:a∈Icc (0:ℝ) T) (hb:b∈Icc (0:ℝ) T)
    (e:JetExpr) (x:ℝ):
    polyJet V e b x-polyJet V e a x=∫ s in a..b,
      ((1/2:ℝ)*polyJet V e.timeB s x+γ s*polyJet V e.timeP s x) := by
  rcases le_total a b with hab|hab
  · exact h.polyJet_pde_ordered hi hm ha.1 hab hb.2 e x
  · rw [intervalIntegral.integral_symm]
    rw [←h.polyJet_pde_ordered hi hm hb.1 hab ha.2 e x]
    ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_PolynomialForced
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators ContDiff
namespace SKValue
lemma BoundedJoint.at_continuous {T:ℝ} {F:ℝ → ℝ → ℝ} (h:BoundedJoint T F) (x:ℝ):
    ContinuousOn (fun t ↦ F t x) (Icc (0:ℝ) T) :=
  h.continuous.comp (continuousOn_id.prodMk continuousOn_const)
    ((mapsTo_id _).prodMk (mapsTo_univ (fun _ ↦ x) _))
lemma BoundedJoint.slice {T:ℝ} {F:ℝ → ℝ → ℝ} (h:BoundedJoint T F) {t:ℝ}
    (ht:t∈Icc (0:ℝ) T):Continuous (F t) := by
  obtain ⟨L,hl⟩:=h.spatial
  exact (hl t ht).continuous
lemma SmoothEvolution.polynomial_forced {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (hT:0≤T) (hi:IntervalIntegrable γ volume 0 T)
    (hm:MonotoneOn γ (Icc (0:ℝ) T)) (hn:∀t∈Icc (0:ℝ) T,0≤γ t)
    (hu:∀t∈Icc (0:ℝ) T,∀x,|deriv (V t) x|≤1) (e:JetExpr):
    ∃ K L:ℝ,ForcedTest T γ (fun t ↦ deriv (V t)) (polyJet V e)
      (polyJet V e.timeB) (polyJet V e.timeP) K L := by
  obtain ⟨A,hA,ha⟩:=(h.polyJet_joint e).bounded
  obtain ⟨B,hB,hb⟩:=(h.polyJet_joint (e.spatialIter 1)).bounded
  obtain ⟨C,hC,hc⟩:=(h.polyJet_joint (e.spatialIter 2)).bounded
  obtain ⟨D,hD,hd⟩:=(h.polyJet_joint (e.spatialIter 3)).bounded
  obtain ⟨E,hE,he⟩:=(h.polyJet_joint e.timeB).bounded
  obtain ⟨F,hF,hf⟩:=(h.polyJet_joint e.timeP).bounded
  obtain ⟨L,hL,hl⟩:=(h.polyJet_joint e.timeB).joint
  obtain ⟨M,hM,hm'⟩:=(h.polyJet_joint e.timeP).joint
  refine ⟨A+B+C+D+E+F,L+M,⟨by positivity,by positivity,hn,hm,?_,hu,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro t ht;exact ((h.slices t ht).jets.smooth.continuous).measurable
  · intro t ht;exact (h.polyJet_smooth e ht).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  · intro t ht x;linarith [ha t ht x]
  · intro t ht x
    have hh:=hb t ht x
    rw [←h.polyJet_iterated e ht 1,iteratedDeriv_one] at hh
    linarith
  · intro t ht x
    have hh:=hc t ht x
    rw [←h.polyJet_iterated e ht 2] at hh
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hh
    linarith
  · intro t ht x
    have hh:=hd t ht x
    rw [←h.polyJet_iterated e ht 3] at hh
    linarith
  · intro t ht;exact ((h.polyJet_joint e.timeB).slice ht).measurable
  · intro t ht;exact ((h.polyJet_joint e.timeP).slice ht).measurable
  · intro t ht x;linarith [he t ht x]
  · intro t ht x;linarith [hf t ht x]
  · intro t ht s hs x y
    exact (hl t ht s hs x y).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM) (by positivity))
  · intro t ht s hs x y
    exact (hm' t ht s hs x y).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL) (by positivity))
  · intro y
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using (h.polyJet_joint e.timeB).at_continuous y
  · intro y
    apply hi.mul_continuousOn
    simpa only [uIcc_of_le hT] using (h.polyJet_joint e.timeP).at_continuous y
  · intro a ha b hb x;exact h.polyJet_pde hi hm ha hb e x
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_Forced
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma ForcedTest.source_measurable {T K L:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) {t:ℝ} (ht:t∈Icc (0:ℝ) T) :
    Measurable (forcedSource γ u V b p t) := by
  have h1:=((h.smooth t ht).continuous_deriv (by norm_num)).measurable
  have h2:Measurable (fun x ↦ deriv (deriv (V t)) x) := by
    have hh:=((h.smooth t ht).continuous_iteratedDeriv 2 (by norm_num)).measurable
    simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hh
  exact ((h.b_measurable t ht).add h2).const_mul (1/2:ℝ) |>.add
    (((h.p_measurable t ht).add ((h.drift_measurable t ht).mul h1)).const_mul (γ t))
lemma ForcedTest.source_bound {T K L:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (x:ℝ) :
    |forcedSource γ u V b p t x| ≤ (1+2*γ T)*K := by
  have hb:|b t x+deriv (deriv (V t)) x| ≤ K+K :=
    (abs_add_le _ _).trans (add_le_add (h.b_bound t ht x) (h.second_bound t ht x))
  have hp:|p t x+u t x*deriv (V t) x| ≤ K+K := by
    apply (abs_add_le _ _).trans
    apply add_le_add (h.p_bound t ht x)
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (h.drift_bound t ht x) (h.first_bound t ht x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  unfold forcedSource
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (h.gamma_nonneg t ht)]
  norm_num only [abs_div,abs_one,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hγ:=h.gamma_mono ht ⟨ht.1.trans ht.2,le_rfl⟩ ht.2
  have hK:=h.K_nonneg
  have hmul:=mul_le_mul hp hγ (h.gamma_nonneg t ht) (by linarith : (0:ℝ) ≤ K+K)
  nlinarith
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

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_ForcedExpectation
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal
namespace SKValue
lemma ForcedTest.expectation_step {T K L t δ:ℝ} {γ:ℝ → ℝ} {u V b₀ p₀:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b₀ p₀ K L) (ht:0≤t) (hδ:0≤δ) (hδ1:δ≤1) (htδ:t+δ≤T)
    {N j:ℕ} (hj:j<N+1) {Y:(Fin (N+1) → ℝ) → ℝ}
    (hYm:Measurable Y) (hYp:DependsBefore j Y) :
    let μ := gaussianProduct (Fin (N+1))
    let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*γ t*u t (Y z)
    |(∫ z,V (t+δ) (Y' z) ∂μ)-(∫ z,V t (Y z) ∂μ)-δ*(∫ z,forcedSource γ u V b₀ p₀ t (Y z) ∂μ)|≤
      δ*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+δ*K*(γ (t+δ)-γ t) := by
  let μ := gaussianProduct (Fin (N+1))
  let p := fun z ↦ deriv (V t) (Y z)
  let a := fun z ↦ deriv (deriv (V t)) (Y z)
  let Y' := fun z ↦ Y z+Real.sqrt δ*coordinate N j z+δ*γ t*u t (Y z)
  let P := fun z ↦ Real.sqrt δ*rawIncrement p j z
  let Q := fun z ↦ (δ/2)*(a z*((coordinate N j z)^2-1))
  let S := fun z ↦ forcedSource γ u V b₀ p₀ t (Y z)
  let D := fun z ↦ V (t+δ) (Y' z)-V t (Y z)-δ*S z
  let R := fun z ↦ D z-P z-Q z
  let E := fun z ↦ δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N j z)+δ*K*(γ (t+δ)-γ t)
  have htT:t≤T := (le_add_of_nonneg_right hδ).trans htδ
  have htm:t∈Icc (0:ℝ) T := ⟨ht,htT⟩
  have hem:t+δ∈Icc (0:ℝ) T := ⟨by linarith,htδ⟩
  have hpm:Measurable p := ((h.smooth t htm).continuous_deriv (by norm_num)).measurable.comp hYm
  have ham:Measurable a := by
    have hh := (h.smooth t htm).continuous_iteratedDeriv 2 (by norm_num)
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ] at hh
    exact hh.measurable.comp hYm
  have hpM:MemLp p 2 μ := MemLp.of_bound hpm.aestronglyMeasurable K
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.first_bound t htm (Y z)))
  have haM:MemLp a 2 μ := MemLp.of_bound ham.aestronglyMeasurable K
    (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.second_bound t htm (Y z)))
  have hpp:DependsBefore j p := fun z z' hz ↦ by dsimp only [p];rw [hYp z z' hz]
  have hap:DependsBefore j a := fun z z' hz ↦ by dsimp only [a];rw [hYp z z' hz]
  have hPi:Integrable P μ := (((rawIncrement_memLp hj hpm hpp hpM).const_mul _).integrable (by norm_num))
  have hQi:Integrable Q μ := (((predictableCenteredSquare_memLp ham (fun z ↦ h.second_bound t htm (Y z))).const_mul _).integrable (by norm_num))
  have hP0:(∫ z,P z ∂μ)=0 := by
    dsimp only [P]
    rw [integral_const_mul,rawIncrement_mean hj hpm hpp,mul_zero]
  have hQ0:(∫ z,Q z ∂μ)=0 := by
    dsimp only [Q]
    rw [integral_const_mul,predictableCenteredSquare_mean hj ham hap,mul_zero]
  have hY'm:Measurable Y' := (hYm.add ((measurable_coordinate N j).const_mul _)).add
    (((h.drift_measurable t htm).comp hYm).const_mul _)
  have hcur:Integrable (fun z ↦ V t (Y z)) μ :=
    (MemLp.of_bound ((h.smooth t htm).continuous.measurable.comp hYm).aestronglyMeasurable K
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.bound t htm (Y z))) :
        MemLp (fun z ↦ V t (Y z)) 2 μ).integrable (by norm_num)
  have hnext:Integrable (fun z ↦ V (t+δ) (Y' z)) μ :=
    (MemLp.of_bound ((h.smooth (t+δ) hem).continuous.measurable.comp hY'm).aestronglyMeasurable K
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.bound (t+δ) hem (Y' z))) :
        MemLp (fun z ↦ V (t+δ) (Y' z)) 2 μ).integrable (by norm_num)
  have hSi:Integrable S μ :=
    (MemLp.of_bound ((h.source_measurable htm).comp hYm).aestronglyMeasurable ((1+2*γ T)*K)
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using h.source_bound htm (Y z))) :
        MemLp S 2 μ).integrable (by norm_num)
  have hDi:Integrable D μ := (hnext.sub hcur).sub (hSi.const_mul δ)
  have hRi:Integrable R μ := (hDi.sub hPi).sub hQi
  have hEi0 := (cubicEnvelope_memLp_two (coordinate_hasLaw N j)
    (h.gamma_nonneg T ⟨ht.trans htT,le_rfl⟩) K ((1/2+γ T)*L)).integrable (by norm_num)
  have hEi:Integrable E μ := (hEi0.const_mul _).add (integrable_const _)
  have hRE (z) : |R z|≤E z := by
    have hh := h.euler_one_step ht hδ hδ1 htδ (x:=Y z) (z:=coordinate N j z)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [R,D,P,Q,p,a,Y',S,E,rawIncrement]
    congr 1
    ring_nf
  have hRmean:(∫ z,R z ∂μ)=(∫ z,V (t+δ) (Y' z) ∂μ)-(∫ z,V t (Y z) ∂μ)-δ*(∫ z,S z ∂μ) := by
    have hs := integral_sub (hDi.sub hPi) hQi
    change (∫ z,D z-P z-Q z ∂μ)=(∫ z,D z-P z ∂μ)-(∫ z,Q z ∂μ) at hs
    have hs1 := integral_sub hDi hPi
    change (∫ z,D z-P z ∂μ)=(∫ z,D z ∂μ)-(∫ z,P z ∂μ) at hs1
    change (∫ z,D z-P z-Q z ∂μ)=_
    rw [hs,hs1,hP0,hQ0,sub_zero,sub_zero]
    have hs2 := integral_sub (hnext.sub hcur) (hSi.const_mul δ)
    change (∫ z,V (t+δ) (Y' z)-V t (Y z)-δ*S z ∂μ)=
      (∫ z,V (t+δ) (Y' z)-V t (Y z) ∂μ)-(∫ z,δ*S z ∂μ) at hs2
    dsimp only [D]
    rw [hs2,integral_sub hnext hcur,integral_const_mul]
  have hEmean:(∫ z,E z ∂μ)=
      δ*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+δ*K*(γ (t+δ)-γ t) := by
    dsimp only [E]
    rw [integral_add (hEi0.const_mul _) (integrable_const _),integral_const_mul]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    have he:(∫ z,cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N j z) ∂μ)=
        cubicEnvelopeMean (γ T) K ((1/2+γ T)*L) := by
      simpa only [Function.comp_def,cubicEnvelopeMean,standardGaussian] using
        (coordinate_hasLaw N j).integral_comp (measurable_cubicEnvelope (γ T) K ((1/2+γ T)*L)).aestronglyMeasurable
    rw [he]
  change |(∫ z,V (t+δ) (Y' z) ∂μ)-(∫ z,V t (Y z) ∂μ)-δ*(∫ z,forcedSource γ u V b₀ p₀ t (Y z) ∂μ)|≤_
  rw [←hRmean,←hEmean]
  exact abs_integral_le_integral_abs.trans (integral_mono hRi.norm hEi hRE)
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal
namespace SKValue
lemma ForcedTest.mesh_expectation {T K L:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) (hT:0<T) (hT1:T≤1) {N:ℕ} (hN:0<N) :
    |(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1)))-V 0 0-stepSize T N*∑ j∈Finset.range N,
      (∫ z,forcedSource γ u V b p (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))|≤
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
        stepSize T N*K*(γ T-γ 0) := by
  let δ := stepSize T N
  let A := fun j ↦ ∫ z,V (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1))
  let S := fun j ↦ ∫ z,forcedSource γ u V b p (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1))
  have hNr:0<(N:ℝ) := by exact_mod_cast hN
  have hδ:0≤δ := div_nonneg hT.le hNr.le
  have hδ1:δ≤1 := by
    apply (div_le_iff₀ hNr).mpr
    have hn:(1:ℝ)≤N := by exact_mod_cast hN
    simpa only [one_mul] using hT1.trans hn
  have htime (j:ℕ) (hj:j≤N) := mesh_time_mem hT.le hN hj
  have hs (j:ℕ) : meshTime T N j+δ=meshTime T N (j+1) := by dsimp [meshTime];push_cast;ring
  have hlast:meshTime T N N=T := by dsimp [meshTime,stepSize];field_simp
  have hzero:meshTime T N 0=0 := by simp [meshTime]
  have hum (j:ℕ) (hj:j<N) : Measurable (u (meshTime T N j)) := h.drift_measurable _ (htime j hj.le)
  have hstep (j:ℕ) (hj:j<N) : |A (j+1)-A j+(-δ*S j)|≤
      δ*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
        δ*K*(γ (meshTime T N (j+1))-γ (meshTime T N j))+0*((0:ℝ)-0) := by
    have hYp:DependsBefore j (fun z ↦ euler T N γ u z j) :=
      eulerCoefficient_dependsBefore T hj.le γ u (fun _ y ↦ y)
    have he := h.expectation_step (htime j hj.le).1 hδ hδ1
      (by rw [hs];exact (htime (j+1) (by omega)).2) (by omega:j<N+1)
      (measurable_euler T N γ u hum j hj.le) hYp
    dsimp only at he
    rw [hs] at he
    simpa only [A,S,euler,δ,mul_assoc,add_zero,sub_self,mul_zero,sub_eq_add_neg,neg_mul] using he
  have hh := abs_telescope_source (A:=A) (b:=fun j ↦ -δ*S j) (Γ:=fun j ↦ γ (meshTime T N j))
    (Δ:=fun _ ↦ 0) (e:=0) hstep
  have hA0:A 0=V 0 0 := by simp [A,meshTime,euler]
  rw [hA0,show A N=(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1))) by
    dsimp only [A];rw [hlast],hlast,hzero] at hh
  have hNd:(N:ℝ)*δ=T := by dsimp [δ,stepSize];field_simp
  simpa only [neg_mul,Finset.sum_neg_distrib,←Finset.mul_sum,sub_self,mul_zero,add_zero,←mul_assoc,hNd,←sub_eq_add_neg,S] using hh

lemma ForcedTest.terminal_lipschitz {T K L:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) (hT:0≤T) (x y:ℝ) : |V T x-V T y|≤K*|x-y| := by
  have hd := (h.smooth T ⟨hT,le_rfl⟩).differentiable (by norm_num)
  have hb:∀ z,‖deriv (V T) z‖≤K := fun z ↦ by simpa only [Real.norm_eq_abs] using h.first_bound T ⟨hT,le_rfl⟩ z
  have hl : LipschitzWith ⟨K,h.K_nonneg⟩ (V T) := by
    apply lipschitzWith_of_nnnorm_deriv_le hd
    intro z
    exact_mod_cast hb z
  have hh := hl.dist_le_mul x y
  change |V T x-V T y|≤K*|x-y| at hh
  exact hh

lemma ForcedTest.coupled_terminal_error {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hB:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {T K L K' L':ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (hT:0<T) (hu:GradientStrip T γ u K L) (h:ForcedTest T γ u V b p K' L')
    (hXM:∀ t∈Icc (0:ℝ) T,AEStronglyMeasurable (X t) μ)
    (hpaths:∀ᵐ ω ∂μ,(∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+
      ∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0) {N:ℕ} (hN:0<N) :
    |(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1)))-
      (∫ ω,V T (X T ω) ∂μ)|≤K'*Real.sqrt (∫ ω,(meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ) := by
  let F := fun ω ↦ V T (coupledEuler T γ u B N N ω)
  let G := fun ω ↦ V T (X T ω)
  let E := meshMaxError T X (coupledEuler T γ u B) N
  have ht:T∈Icc (0:ℝ) T := ⟨hT.le,le_rfl⟩
  have hm:Continuous (V T) := (h.smooth T ht).continuous
  have hFM:MemLp F 2 μ := MemLp.of_bound
    (hm.measurable.comp_aemeasurable (coupled_euler_measurable hB hT hu N N le_rfl).aemeasurable).aestronglyMeasurable K'
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs,F] using h.bound T ht _))
  have hGM:MemLp G 2 μ := MemLp.of_bound
    (hm.measurable.comp_aemeasurable (hXM T ht).aemeasurable).aestronglyMeasurable K'
      (Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs,G] using h.bound T ht _))
  have hEM:MemLp E 2 μ := coupled_mesh_error_memLp hB hT hu hXM hpaths hN
  have hlast:meshTime T N N=T := by dsimp [meshTime,stepSize];field_simp
  have hFG (ω:Ω) : |F ω-G ω|≤K'*|E ω| := by
    have he:|coupledEuler T γ u B N N ω-X T ω|≤E ω := by
      have hh := le_initialMax (f:=fun k ↦
        |coupledEuler T γ u B N k ω-X (meshTime T N k) ω|) (le_refl N)
      change |coupledEuler T γ u B N N ω-X (meshTime T N N) ω|≤E ω at hh
      rwa [hlast] at hh
    exact (h.terminal_lipschitz hT.le _ _).trans
      (mul_le_mul_of_nonneg_left (he.trans (le_abs_self _)) h.K_nonneg)
  have heq:(∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1)))=(∫ ω,F ω ∂μ) := by
    have heum := measurable_euler T N γ u (fun j hj ↦ (hu.smooth _ (mesh_time_mem hT.le hN hj.le)).continuous.measurable) N le_rfl
    have hh := (coupledCoordinates_hasLaw hB hT hN).integral_comp (hm.measurable.comp heum).aestronglyMeasurable
    simpa only [Function.comp_apply,F,coupledEuler,ite_eq_right (Nat.ne_of_gt hN)] using hh.symm
  rw [heq]
  exact first_moment_perturbation hFM hGM hEM h.K_nonneg (Eventually.of_forall hFG)
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_ForcedDiffusion
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma ForcedTest.diffusion_generator_of_source_limit {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hB:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {T K L K' L' Lu:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (hT:0<T) (hT1:T≤1) (hu:GradientStrip T γ u K L) (h:ForcedTest T γ u V b p K' L')
    (hLu:0≤Lu) (hLip:∀ s∈Icc (0:ℝ) T,∀ t∈Icc (0:ℝ) T,∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM:∀ t∈Icc (0:ℝ) T,AEStronglyMeasurable (X t) μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      (∀ t∈Icc (0:ℝ) T,X t ω=B t.toNNReal ω+∫ s in (0:ℝ)..t,γ s*u s (X s ω)) ∧ X 0 ω=0)
    {I:ℝ} (hsource:Tendsto (fun N ↦ stepSize T N*∑ j∈Finset.range N,
      (∫ z,forcedSource γ u V b p (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1))))
        atTop (𝓝 I)) :
    (∫ ω,V T (X T ω) ∂μ)=V 0 0+I := by
  let S := fun N ↦ stepSize T N*∑ j∈Finset.range N,
      (∫ z,forcedSource γ u V b p (meshTime T N j) (euler T N γ u z j) ∂gaussianProduct (Fin (N+1)))
  let A := fun N ↦ ∫ z,V T (euler T N γ u z N) ∂gaussianProduct (Fin (N+1))
  let E := fun N ↦ T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K' ((1/2+γ T)*L')+
    stepSize T N*K'*(γ T-γ 0)
  let F := fun N ↦ K'*Real.sqrt (∫ ω,(meshMaxError T X (coupledEuler T γ u B) N ω)^2 ∂μ)
  have hδ:Tendsto (fun N:ℕ ↦ stepSize T N) atTop (𝓝 (0:ℝ)) := tendsto_const_div_atTop_nhds_zero_nat T
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hδ
  have hE:Tendsto E atTop (𝓝 0) := by
    simpa only [E,Function.comp_def,Real.sqrt_zero,mul_zero,zero_mul,add_zero] using
      (((hsqrt.const_mul T).mul_const (cubicEnvelopeMean (γ T) K' ((1/2+γ T)*L'))).add
        ((hδ.mul_const K').mul_const (γ T-γ 0)))
  have hF:Tendsto F atTop (𝓝 0) := by
    simpa only [F,Function.comp_def,Real.sqrt_zero,mul_zero] using
      (((Real.continuous_sqrt.tendsto 0).comp
        (coupled_euler_L2_convergence hB hT hu hLu hLip hXM hpaths)).const_mul K')
  have hbound:∀ᶠ N in atTop,|(∫ ω,V T (X T ω) ∂μ)-V 0 0-S N|≤E N+F N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have he := h.mesh_expectation hT hT1 hN
    have hf := h.coupled_terminal_error hB hT hu hXM
      (by filter_upwards [hpaths] with ω hω using hω.2.2) hN
    have ht := abs_sub_le ((∫ ω,V T (X T ω) ∂μ)-V 0 0-S N) (A N-V 0 0-S N) 0
    change |A N-V 0 0-S N|≤E N at he
    change |A N-(∫ ω,V T (X T ω) ∂μ)|≤F N at hf
    have hf' : |(∫ ω,V T (X T ω) ∂μ)-A N|≤F N := by
      rw [abs_sub_comm];exact hf
    have hid:((∫ ω,V T (X T ω) ∂μ)-V 0 0-S N)-(A N-V 0 0-S N)=
      (∫ ω,V T (X T ω) ∂μ)-A N := by ring
    rw [hid,sub_zero,sub_zero] at ht
    linarith
  have hleft:Tendsto (fun N ↦ |(∫ ω,V T (X T ω) ∂μ)-V 0 0-S N|) atTop
      (𝓝 |(∫ ω,V T (X T ω) ∂μ)-V 0 0-I|) := (tendsto_const_nhds.sub hsource).abs
  have hz := le_of_tendsto_of_tendsto hleft (hE.add hF) hbound
  have habs:|(∫ ω,V T (X T ω) ∂μ)-V 0 0-I|=0 := le_antisymm (by simpa using hz) (abs_nonneg _)
  have he := abs_eq_zero.mp habs
  linarith
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_PolynomialGenerator
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma SmoothEvolution.polyJet_source {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (x:ℝ):
    forcedSource γ (fun t ↦ deriv (V t)) (polyJet V e) (polyJet V e.timeB) (polyJet V e.timeP) t x=
      polyJet V e.sourceA t x+γ t*polyJet V e.sourceP t x := by
  have hd:deriv (polyJet V e t)=polyJet V e.spatial t := funext (fun y ↦ (h.polyJet_hasDeriv e ht y).deriv)
  have hdd:=h.polyJet_iterated e ht 2
  simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hdd
  unfold forcedSource
  rw [hdd,hd]
  simp only [polyJet,JetExpr.sourceA,JetExpr.sourceP,JetExpr.eval,iteratedDeriv_zero]

lemma IsDiffusion.polyJet_generator {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {T:ℝ} (hT:0<T) (hT1:T<1) (e:JetExpr):
    (∫ z,polyJet (phi W γ) e T (X T z) ∂W.μ)=polyJet (phi W γ) e 0 0+
      ∫ t in (0:ℝ)..T, ((∫ z,polyJet (phi W γ) e.sourceA t (X t z) ∂W.μ)+
        γ.coeff t*(∫ z,polyJet (phi W γ) e.sourceP t (X t z) ∂W.μ)) := by
  have h:=phi_evolution W γ ⟨hT.le,hT1⟩
  have hm:MonotoneOn γ.coeff (Icc (0:ℝ) T):=γ.monotone.mono (fun _ ht ↦ ⟨ht.1,ht.2.trans_lt hT1⟩)
  have hi:IntervalIntegrable γ.coeff volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT.le] using hm
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩:=sourceStripRegularity W γ T ⟨hT.le,hT1⟩
  obtain ⟨K',L',hf⟩:=h.polynomial_forced hT.le hi hm (fun t ht ↦ γ.nonneg _ ⟨ht.1,ht.2.trans_lt hT1⟩)
    hG.bounded e
  have hjA:=h.polyJet_joint e.sourceA
  have hjP:=h.polyJet_joint e.sourceP
  obtain ⟨A,hA,hAb⟩:=hjA.bounded
  obtain ⟨P,hP,hPb⟩:=hjP.bounded
  obtain ⟨D1,hD1⟩:=hjA.spatial
  obtain ⟨D2,hD2⟩:=hjP.spatial
  have hlimA:=hX.weightedObservable_tendsto hT hT1 (η:=fun _ ↦ (1:ℝ)) (fun _ _ _ _ _ ↦ le_rfl)
    (by norm_num) hA hjA.continuous hAb hD1
  have hlimP:=hX.weightedObservable_tendsto hT hT1 hm (γ.nonneg _ (by constructor <;> norm_num))
    hP hjP.continuous hPb hD2
  simp only [one_mul] at hlimA
  have hXM (t:ℝ) (ht:t∈Icc (0:ℝ) T):AEStronglyMeasurable (X t) W.μ :=
    (hX.memLp (p:=2) ⟨ht.1,ht.2.trans hT1.le⟩ (by norm_num)).aestronglyMeasurable
  have hpaths:=hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x)
  have hAi:IntervalIntegrable (fun t ↦ ∫ z,polyJet (phi W γ) e.sourceA t (X t z) ∂W.μ) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT.le]
    exact mean_observable_continuous hjA.continuous hAb hXM (hpaths.mono (fun _ hz ↦ hz.1))
  have hPi:IntervalIntegrable (fun t ↦ γ.coeff t*(∫ z,polyJet (phi W γ) e.sourceP t (X t z) ∂W.μ)) volume 0 T := by
    apply hi.mul_continuousOn
    rw [uIcc_of_le hT.le]
    exact mean_observable_continuous hjP.continuous hPb hXM (hpaths.mono (fun _ hz ↦ hz.1))
  apply hf.diffusion_generator_of_source_limit W.brownian.toIsPreBrownianReal hT hT1.le hG hLu hu hXM hpaths
  rw [intervalIntegral.integral_add hAi hPi]
  apply (hlimA.add hlimP).congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [←mul_add,←Finset.sum_add_distrib]
  rw [←Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have ht:=mesh_time_mem hT.le hN j.isLt.le
  have hIA:Integrable (fun z ↦ polyJet (phi W γ) e.sourceA (meshTime T N j) (euler T N γ.coeff (gradient W γ) z j))
      (gaussianProduct (Fin (N+1))) := by
    apply Integrable.of_bound
    · exact ((hjA.slice ht).measurable.comp (measurable_euler T N γ.coeff (gradient W γ) (fun i hi ↦ (hG.smooth _ (mesh_time_mem hT.le hN hi.le)).continuous.measurable) j j.isLt.le)).aestronglyMeasurable
    · exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hAb _ ht _)
  have hIP:Integrable (fun z ↦ polyJet (phi W γ) e.sourceP (meshTime T N j) (euler T N γ.coeff (gradient W γ) z j))
      (gaussianProduct (Fin (N+1))) := by
    apply Integrable.of_bound
    · exact ((hjP.slice ht).measurable.comp (measurable_euler T N γ.coeff (gradient W γ) (fun i hi ↦ (hG.smooth _ (mesh_time_mem hT.le hN hi.le)).continuous.measurable) j j.isLt.le)).aestronglyMeasurable
    · exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hPb _ ht _)
  rw [←integral_const_mul,←integral_add hIA (hIP.const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z ↦ (h.polyJet_source e ht _).symm)
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_PolynomialMoment
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma IsDiffusion.jetMoment_continuous {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {T:ℝ} (hT:T∈Ico (0:ℝ) 1) (e:JetExpr):
    ContinuousOn (jetMoment W γ X e) (Icc (0:ℝ) T) := by
  have hj:=(phi_evolution W γ hT).polyJet_joint e
  obtain ⟨C,hC,hb⟩:=hj.bounded
  apply mean_observable_continuous hj.continuous hb
  · intro t ht;exact (hX.memLp (p:=2) ⟨ht.1,ht.2.trans hT.2.le⟩ (by norm_num)).aestronglyMeasurable
  · obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩:=sourceStripRegularity W γ T hT
    exact (hX.strip_paths hT.1 hT.2 hLu (fun t ht s hs x y ↦ hu s hs t ht y x)).mono (fun _ hz ↦ hz.1)
lemma IsDiffusion.jetMoment_hasDerivAt {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hγ:ContinuousAt γ.coeff t)
    (e:JetExpr):HasDerivAt (jetMoment W γ X e)
      (jetMoment W γ X e.sourceA t+γ.coeff t*jetMoment W γ X e.sourceP t) t := by
  obtain ⟨S,htS,hS⟩:=exists_between ht.2
  have hS0:0≤S:=ht.1.le.trans htS.le
  have hSt:S∈Ico (0:ℝ) 1:=⟨hS0,hS⟩
  let F:=fun r ↦ jetMoment W γ X e.sourceA r+γ.coeff r*jetMoment W γ X e.sourceP r
  have hcA:=hX.jetMoment_continuous hSt e.sourceA
  have hcP:=hX.jetMoment_continuous hSt e.sourceP
  have hmono:MonotoneOn γ.coeff (uIcc (0:ℝ) S) := by
    rw [uIcc_of_le hS0];exact γ.monotone.mono (fun _ hr ↦ ⟨hr.1,hr.2.trans_lt hS⟩)
  have hi:IntervalIntegrable F volume 0 S := by
    apply IntervalIntegrable.add
    · exact ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hS0] using hcA)
    · exact hmono.intervalIntegrable.mul_continuousOn (by simpa only [uIcc_of_le hS0] using hcP)
  have hn:Icc (0:ℝ) S∈𝓝 t:=Icc_mem_nhds ht.1 htS
  have hc:ContinuousAt F t := (hcA.continuousAt hn).add (hγ.mul (hcP.continuousAt hn))
  have hsub:uIcc (0:ℝ) t⊆uIcc (0:ℝ) S:=by
    rw [uIcc_of_le ht.1.le,uIcc_of_le hS0];exact Icc_subset_Icc le_rfl htS.le
  have hIi:IntegrableOn F (Icc (0:ℝ) S) volume := by
    simpa only [uIcc_of_le hS0] using (intervalIntegrable_iff').mp hi
  have hd:=((intervalIntegral.integral_hasDerivAt_right (hi.mono_set hsub)
    ⟨Icc (0:ℝ) S,hn,hIi.aestronglyMeasurable⟩ hc).const_add (polyJet (phi W γ) e 0 0))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 htS] with s hs
  exact hX.polyJet_generator hs.1 (hs.2.trans hS) e
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
namespace JetExpr
lemma momentExpr_sourceA (R:ℕ → ℝ):eval R momentExpr.sourceA=eval R curvatureExpr := by
  norm_num [momentExpr,curvatureExpr,square,sourceA,timeB,spatialIter,spatial,D,eval];ring
lemma momentExpr_sourceP (R:ℕ → ℝ):eval R momentExpr.sourceP=0 := by
  norm_num [momentExpr,square,sourceP,timeP,spatialIter,spatial,D,eval];ring
end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_CurvatureMoment
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma IsDiffusion.polyJet_integrable {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ico (0:ℝ) 1) (e:JetExpr):
    Integrable (fun z ↦ polyJet (phi W γ) e t (X t z)) W.μ := by
  have hj:=(phi_evolution W γ ht).polyJet_joint e
  obtain ⟨C,hC,hb⟩:=hj.bounded
  apply Integrable.of_bound
  · exact ((hj.slice ⟨ht.1,le_rfl⟩).measurable.comp (hX.measurable ⟨ht.1,ht.2.le⟩)).aestronglyMeasurable
  · exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hb t ⟨ht.1,le_rfl⟩ (X t z))
lemma IsDiffusion.jetMoment_hasDerivAt_integral {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hc:ContinuousAt γ.coeff t) (e:JetExpr):
    HasDerivAt (jetMoment W γ X e) (∫ z,polyJet (phi W γ) e.sourceA t (X t z)+
      γ.coeff t*polyJet (phi W γ) e.sourceP t (X t z) ∂W.μ) t := by
  rw [integral_add (hX.polyJet_integrable ⟨ht.1.le,ht.2⟩ _) ((hX.polyJet_integrable ⟨ht.1.le,ht.2⟩ _).const_mul _),integral_const_mul]
  exact hX.jetMoment_hasDerivAt ht hc e
lemma IsDiffusion.momentExpr_hasDerivAt_oai {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hc:ContinuousAt γ.coeff t):
    HasDerivAt (jetMoment W γ X JetExpr.momentExpr) (jetMoment W γ X JetExpr.curvatureExpr t) t := by
  have hd:=hX.jetMoment_hasDerivAt_integral ht hc JetExpr.momentExpr
  simpa only [polyJet,JetExpr.momentExpr_sourceA,JetExpr.momentExpr_sourceP,mul_zero,add_zero,jetMoment] using hd
end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsDiffusion.momentExpr_hasDerivAt_oai := @OAI.SKValue.IsDiffusion.momentExpr_hasDerivAt_oai
