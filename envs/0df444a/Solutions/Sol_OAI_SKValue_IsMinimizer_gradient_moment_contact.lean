-- Prove2me | solution 1 for OAI.SKValue.IsMinimizer.gradient_moment_contact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:00:54.208814+00:00
-- url     : https://prove2.me/submissions/e52a02fc-619b-4b9c-a3c8-575af232bb9c

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_IsDiffusion_contactPotential_continuous
import Theorems.Thm_OAI_SKValue_IsDiffusion_contactPotential_hasDerivAt
import Theorems.Thm_OAI_SKValue_IsDiffusion_curvatureExpr_hasDerivAt
import Theorems.Thm_OAI_SKValue_IsDiffusion_curvatureSlope_hasDerivAt
import Theorems.Thm_OAI_SKValue_IsDiffusion_gradientMoment_continuous
import Theorems.Thm_OAI_SKValue_IsDiffusion_momentExpr_hasDerivAt
import Theorems.Thm_OAI_SKValue_IsDiffusion_moment_convexOn_zero_closed
import Theorems.Thm_OAI_SKValue_IsDiffusion_splitResponse_tendsto
import Theorems.Thm_OAI_SKValue_IsMinimizer_coeff_constant_of_contactPositive
import Theorems.Thm_OAI_SKValue_IsMinimizer_contactPotential_nonneg
import Theorems.Thm_OAI_SKValue_IsMinimizer_contact_origin_of_positive
import Theorems.Thm_OAI_SKValue_IsMinimizer_moment_eq_at_contact
import Theorems.Thm_OAI_SKValue_phi_evolution
import Theorems.Thm_OAI_SKValue_smoothApprox_tendsto
import Theorems.Thm_OAI_SKValue_sourceStripRegularity
import Theorems.Thm_OAI_SKValue_split_profile_coercivity
import Theorems.Thm_OAI_SKValue_split_spatialJet_limit

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

lemma profileCoeff_integrable (l : HeatProfile) :
    IntervalIntegrable (profileCoeff l) volume 0 (profileTime l) := by
  induction l with
  | nil => exact intervalIntegrable_const
  | cons p l ih =>
    exact patchTime_intervalIntegrable p.1.coe_nonneg (profileTime_nonneg l) intervalIntegrable_const ih

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

lemma patchTime_end {E : Type*} {a b : ℝ} (hb : 0≤b) {f g : ℝ → E} (hfg : f a=g 0) :
    patchTime a f g (a+b)=g b := by
  rcases hb.eq_or_lt with rfl | hb
  · simpa only [add_zero,patchTime_left f g le_rfl] using hfg
  · rw [patchTime_right f g (lt_add_of_pos_right a hb)]
    congr 1
    ring

lemma profileValue_terminal (ψ : ℝ → ℝ) (l : HeatProfile) :
    profileValue ψ l (profileTime l)=ψ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change patchTime _ _ _ ((p.1 : ℝ)+profileTime l)=ψ
    rw [patchTime_end (profileTime_nonneg l)]
    · exact ih
    · funext x
      simp only [sub_self,coleHopf_zero]

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

lemma logCoshTerminal_even (M x : ℝ) : logCoshTerminal M (-x)=logCoshTerminal M x := by
  simp only [logCoshTerminal,mul_neg,Real.cosh_neg]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_EvenEvolution
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

lemma profileValue_even {ψ : ℝ → ℝ} (hψ : ∀ x, ψ (-x)=ψ x)
    (l : HeatProfile) (t x : ℝ) : profileValue ψ l t (-x)=profileValue ψ l t x := by
  induction l generalizing t x with
  | nil => exact hψ x
  | cons p l ih =>
    change (patchTime (E := ℝ → ℝ) _ _ _ t) (-x)=(patchTime (E := ℝ → ℝ) _ _ _ t) x
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht]
      exact coleHopf_even (fun y ↦ ih 0 y) _ _ _
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _ _

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

lemma smoothApprox_even (γ : OrderParameter) (n : ℕ) (t x : ℝ) :
    smoothApprox γ n t (-x)=smoothApprox γ n t x :=
  profileValue_even (logCoshTerminal_even (n+1 : ℝ)) (γ.grid n) t x

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

lemma phi_even (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Ico (0 : ℝ) 1) (x : ℝ) : phi W γ t (-x)=phi W γ t x := by
  have hl := (smoothApprox_tendsto W γ).tendsto_at (⟨t,ht⟩,-x)
  have hr := (smoothApprox_tendsto W γ).tendsto_at (⟨t,ht⟩,x)
  exact tendsto_nhds_unique hl (hr.congr (fun n ↦ (smoothApprox_even γ n t x).symm))

lemma phi_gradient_zero (W : BrownianSpace) (γ : OrderParameter) : gradient W γ 0 0=0 :=
  deriv_even_zero (phi_even W γ (by norm_num))

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
lemma SmoothEvolution.polyJet_joint {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr):BoundedJoint T (polyJet V e) := by
  induction e with
  | const c => exact BoundedJoint.const T c
  | coord n =>
    obtain ⟨L,hL,hl⟩:=h.jet_joint n
    exact ⟨h.bound n,⟨L,hL,fun t ht s hs x y ↦ hl s hs t ht x y⟩⟩
  | add e f he hf => exact he.add hf
  | mul e f he hf => exact he.mul hf
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
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
namespace JetExpr
lemma momentExpr_eval (R:ℕ → ℝ):eval R momentExpr=(R 0)^2 := by simp only [momentExpr,square,eval,pow_two]
end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_UniformPolynomial
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open scoped Topology
namespace SKValue
lemma BoundedUniformLimit.const {A:Type*} (c:ℝ) :
    BoundedUniformLimit (fun (_:ℕ) (_:A) ↦ c) (fun _ ↦ c) :=
  ⟨by
    rw [Metric.tendstoUniformly_iff]
    exact fun ε hε ↦ Eventually.of_forall (fun _ _ ↦ by simpa using hε),|c|,abs_nonneg c,fun _ _ ↦ le_rfl,fun _ ↦ le_rfl⟩
lemma BoundedUniformLimit.add {A:Type*} {F G:ℕ → A → ℝ} {f g:A → ℝ}
    (hF:BoundedUniformLimit F f) (hG:BoundedUniformLimit G g) :
    BoundedUniformLimit (fun n x ↦ F n x+G n x) (fun x ↦ f x+g x) := by
  obtain ⟨C,hC,hb,hf⟩:=hF.bound
  obtain ⟨D,hD,hd,hg⟩:=hG.bound
  exact ⟨hF.tendsto.add hG.tendsto,C+D,add_nonneg hC hD,
    fun n x ↦ (abs_add_le _ _).trans (add_le_add (hb n x) (hd n x)),
    fun x ↦ (abs_add_le _ _).trans (add_le_add (hf x) (hg x))⟩
lemma BoundedUniformLimit.mul {A:Type*} {F G:ℕ → A → ℝ} {f g:A → ℝ}
    (hF:BoundedUniformLimit F f) (hG:BoundedUniformLimit G g) :
    BoundedUniformLimit (fun n x ↦ F n x*G n x) (fun x ↦ f x*g x) := by
  obtain ⟨C,hC,hb,hf⟩:=hF.bound
  obtain ⟨D,hD,hd,hg⟩:=hG.bound
  refine ⟨?_,C*D,mul_nonneg hC hD,?_,?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    let δ:=ε/(C+D+1)
    have hden:0<C+D+1 := by linarith
    have hδ:0<δ := div_pos hε hden
    have heq:δ*(C+D+1)=ε := div_mul_cancel₀ ε hden.ne'
    filter_upwards [(Metric.tendstoUniformly_iff.mp hF.tendsto) δ hδ,
      (Metric.tendstoUniformly_iff.mp hG.tendsto) δ hδ] with n hn hm x
    have hn':|F n x-f x|<δ := by simpa only [Real.dist_eq,abs_sub_comm] using hn x
    have hm':|G n x-g x|<δ := by simpa only [Real.dist_eq,abs_sub_comm] using hm x
    rw [Real.dist_eq,abs_sub_comm]
    have he:F n x*G n x-f x*g x=F n x*(G n x-g x)+(F n x-f x)*g x := by ring
    rw [he]
    apply (abs_add_le _ _).trans_lt
    rw [abs_mul,abs_mul]
    have h1:=mul_le_mul (hb n x) hm'.le (abs_nonneg _) hC
    have h2:=mul_le_mul hn'.le (hg x) (abs_nonneg _) hδ.le
    nlinarith
  · intro n x;rw [abs_mul];exact mul_le_mul (hb n x) (hd n x) (abs_nonneg _) hC
  · intro x;rw [abs_mul];exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hC
lemma BoundedUniformLimit.neg {A:Type*} {F:ℕ → A → ℝ} {f:A → ℝ}
    (hF:BoundedUniformLimit F f) : BoundedUniformLimit (fun n x ↦ -F n x) (fun x ↦ -f x) := by
  simpa only [neg_one_mul] using (BoundedUniformLimit.const (-1)).mul hF
lemma BoundedUniformLimit.sub {A:Type*} {F G:ℕ → A → ℝ} {f g:A → ℝ}
    (hF:BoundedUniformLimit F f) (hG:BoundedUniformLimit G g) :
    BoundedUniformLimit (fun n x ↦ F n x-G n x) (fun x ↦ f x-g x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg
lemma BoundedUniformLimit.pow {A:Type*} {F:ℕ → A → ℝ} {f:A → ℝ}
    (hF:BoundedUniformLimit F f) (k:ℕ) :
    BoundedUniformLimit (fun n x ↦ F n x^k) (fun x ↦ f x^k) := by
  induction k with
  | zero => exact BoundedUniformLimit.const 1
  | succ k ih => simpa only [pow_succ] using ih.mul hF
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatDuality
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
lemma weightedJet_bounded {ψ f : ℝ → ℝ} (hψ : BoundedSmooth (deriv ψ))
    (hf : BoundedSmooth f) (c : ℝ) (n : ℕ) : BoundedSmooth (weightedJet c ψ f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.deriv.add (ih.mul (hψ.const_mul c))
lemma weighted_iteratedDeriv {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)*f x)=
      fun x ↦ Real.exp (c*ψ x)*weightedJet c ψ f n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := hψ.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
    have hj := (weightedJet_bounded hψ.jets hf c n).smooth.differentiable
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
    convert! ((((hd x).hasDerivAt.const_mul c).exp).mul (hj x).hasDerivAt).deriv using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [weightedJet]
    ring
lemma weighted_growth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ExpGrowth (iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)*f x)) := by
  rw [weighted_iteratedDeriv hψ hf c n]
  obtain ⟨C,hC,hb⟩ := (weightedJet_bounded hψ.jets hf c n).bound_zero
  exact (ExpGrowth.exp_lipschitz hψ.lipschitz hc).mul_bounded hC hb

lemma responseJet_continuous {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ responseJet c ψ f n p.1 p.2) := by
  exact (heat_jet_continuous ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth)
    (weighted_growth hψ hf hc) n).div
    (heat_continuous (Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous))
      (ExpGrowth.exp_lipschitz hψ.lipschitz hc))
    (fun p ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc p.2 (Real.sqrt p.1)).ne')
lemma responseJet_smooth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (responseJet c ψ f n t) := by
  exact (smooth_iteratedDeriv
    (heat_contDiff ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth) (weighted_growth hψ hf hc) t) n).div
    (heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
      (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) t)
    (fun x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne')
lemma responseJet_space {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (t x : ℝ) :
    HasDerivAt (responseJet c ψ f n t)
      (responseJet c ψ f (n+1) t x-responseJet c ψ f n t x*baseJet c ψ 1 t x) x := by
  have hnum := heat_contDiff ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth) (weighted_growth hψ hf hc) t
  have hden := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) t
  have hp := (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hd := (((hnum.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) x).hasDerivAt).div
    ((hden.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne') x).hasDerivAt hp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [responseJet,baseJet,normalizedJet]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  field_simp
lemma responseJet_time {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c t : ℝ} (hc : 0 ≤ c) (ht : 0<t) (n : ℕ) (x : ℝ) :
    HasDerivAt (responseJet c ψ f n · x)
      ((1/2:ℝ)*(responseJet c ψ f (n+2) t x-responseJet c ψ f n t x*baseJet c ψ 2 t x)) t := by
  have hp := (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hd := (heat_jet_time ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth)
    (weighted_growth hψ hf hc) n x ht).div
      (heat_jet_time ((contDiff_const.mul hψ.smooth).exp)
        (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) 0 x ht) hp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [responseJet,baseJet,normalizedJet]
  simp only [iteratedDeriv_zero,zero_add]
  field_simp
lemma responseJet_bound {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C:ℝ,0≤C ∧ ∀ t x,|responseJet c ψ f n t x|≤C := by
  obtain ⟨C,hC,hb⟩ := (weightedJet_bounded hψ.jets hf c n).bound_zero
  refine ⟨C,hC,?_⟩
  intro t x
  have hs : ContDiff ℝ ∞ (fun y ↦ Real.exp (c*ψ y)*f y) := (contDiff_const.mul hψ.smooth).exp.mul hf.smooth
  have hp : 0<heat t (fun y ↦ Real.exp (c*ψ y)) x := lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)
  rw [responseJet,heat_iteratedDeriv hs (weighted_growth hψ hf hc),abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  apply heat_relative_bound ((Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous)).measurable)
    (smooth_iteratedDeriv hs n).continuous.measurable (ExpGrowth.exp_lipschitz hψ.lipschitz hc)
    (weighted_growth hψ hf hc n)
  intro y
  rw [weighted_iteratedDeriv hψ hf c n,abs_mul,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm,Function.comp_apply,Pi.mul_apply] using mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos (c*ψ y)).le
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TestHeat
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma linear_derivative_tower_bounded {ι : Type*} (S : ℕ → ι → ℝ → ℝ)
    (b : ι → ℝ → ℝ) (hs : ∀ j a,ContDiff ℝ ∞ (S j a))
    (hbs : ∀ a,ContDiff ℝ ∞ (b a))
    (hd : ∀ j a,deriv (S j a)=fun x ↦ S (j+1) a x-S j a x*b a x)
    (hb : ∀ j,∃ C:ℝ,0≤C ∧ ∀ a x,|S j a x|≤C)
    (hbb : ∀ n,∃ C:ℝ,0≤C ∧ ∀ a x,|iteratedDeriv n (b a) x|≤C) :
    ∀ n j:ℕ,∃ C:ℝ,0≤C ∧ ∀ a x,|iteratedDeriv n (S j a) x|≤C := by
  classical
  choose B hB hbB using hbb
  intro n
  induction n using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => intro j;simpa only [iteratedDeriv_zero] using hb j
    | succ n =>
      have hlo : ∀ k j:ℕ,∃ C:ℝ,0≤C ∧
          (k≤n → ∀ a x,|iteratedDeriv k (S j a) x|≤C) := by
        intro k j
        by_cases hk:k≤n
        · obtain ⟨C,hC,hbC⟩ := ih k (Nat.lt_succ_of_le hk) j
          exact ⟨C,hC,fun _ ↦ hbC⟩
        · exact ⟨0,le_rfl,fun h ↦ (hk h).elim⟩
      choose C hC hbound using hlo
      intro j
      refine ⟨C n (j+1)+∑ k∈Finset.range (n+1),(n.choose k:ℝ)*C k j*B (n-k),?_,?_⟩
      · exact add_nonneg (hC _ _) (Finset.sum_nonneg (fun k _ ↦
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC _ _)) (hB _)))
      · intro a x
        rw [iteratedDeriv_succ',hd,
          iteratedDeriv_fun_sub
            ((hs (j+1) a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            (((hs j a).mul (hbs a)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
          iteratedDeriv_fun_mul
            ((hs j a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            ((hbs a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
        apply (abs_sub _ _).trans
        apply add_le_add (hbound n (j+1) le_rfl a x)
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk':k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose k))]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hbound k j hk' a x) (Nat.cast_nonneg _))
          (hbB (n-k) a x) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC _ _))

lemma responseJet_uniform_jets {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) :
    ∀ n j:ℕ,∃ C:ℝ,0≤C ∧ ∀ t x,|iteratedDeriv n (responseJet c ψ f j t) x|≤C := by
  have hs := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
  have hp (t x:ℝ) : heat t (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
    (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hb := exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc
  apply linear_derivative_tower_bounded (responseJet c ψ f) (baseJet c ψ 1)
    (responseJet_smooth hψ hf hc)
    (normalizedJet_smooth hs hp 1)
    (fun j t ↦ funext (fun x ↦ (responseJet_space hψ hf hc j t x).deriv))
    (responseJet_bound hψ hf hc)
  intro n
  exact normalizedJet_uniform_bounded hs hp hb n 1

lemma responseJet_boundedSmooth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n:ℕ) (t:ℝ) :
    BoundedSmooth (responseJet c ψ f n t) := by
  refine ⟨responseJet_smooth hψ hf hc n t,?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := responseJet_uniform_jets hψ hf hc k n
  exact ⟨C,hC,hb t⟩

lemma baseJet_space {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n:ℕ) (t x:ℝ) :
    HasDerivAt (baseJet c ψ n t)
      (baseJet c ψ (n+1) t x-baseJet c ψ n t x*baseJet c ψ 1 t x) x := by
  have hs := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
  have hp (t x:ℝ) : heat t (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
    (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  exact ((normalizedJet_smooth hs hp n t).differentiable
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne' x).hasDerivAt.congr_deriv
      (congrFun (normalizedJet_deriv hs hp n t) x)

lemma responseJet_second {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n:ℕ) (t x:ℝ) :
    deriv (deriv (responseJet c ψ f n t)) x=
      responseJet c ψ f (n+2) t x-2*responseJet c ψ f (n+1) t x*baseJet c ψ 1 t x-
        responseJet c ψ f n t x*baseJet c ψ 2 t x+
          2*responseJet c ψ f n t x*(baseJet c ψ 1 t x)^2 := by
  have hd : deriv (responseJet c ψ f n t)=fun y ↦ responseJet c ψ f (n+1) t y-
      responseJet c ψ f n t y*baseJet c ψ 1 t y :=
    funext (fun y ↦ (responseJet_space hψ hf hc n t y).deriv)
  rw [hd]
  convert! ((responseJet_space hψ hf hc (n+1) t x).sub
    ((responseJet_space hψ hf hc n t x).mul (baseJet_space hψ hc 1 t x))).deriv using 1
  all_goals try with_reducible_and_instances rfl
  simp only [show n+1+1=n+2 by omega]
  ring

lemma responseJet_heat_drift {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c t : ℝ} (hc : 0 ≤ c) (ht : 0<t) (n:ℕ) (x:ℝ) :
    HasDerivAt (responseJet c ψ f n · x)
      ((1/2:ℝ)*deriv (deriv (responseJet c ψ f n t)) x+
        baseJet c ψ 1 t x*deriv (responseJet c ψ f n t) x) t := by
  convert! responseJet_time hψ hf hc ht n x using 1
  all_goals try with_reducible_and_instances rfl
  rw [responseJet_second hψ hf hc,(responseJet_space hψ hf hc n t x).deriv]
  ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ResponseJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma baseJet_continuous {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c:ℝ} (hc:0 ≤ c) (j:ℕ) :
    Continuous (fun p:ℝ×ℝ ↦ baseJet c ψ j p.1 p.2) :=
  heat_normalizedJet_continuous ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
    (fun t x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne') j
lemma baseJet_time {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c t:ℝ} (hc:0 ≤ c) (ht:0<t) (j:ℕ) (x:ℝ) :
    HasDerivAt (baseJet c ψ j · x)
      ((1/2:ℝ)*(baseJet c ψ (j+2) t x-baseJet c ψ j t x*baseJet c ψ 2 t x)) t :=
  heat_normalizedJet_time ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
    (fun t x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne') j x ht
lemma combinedJet_continuous {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (j:ℕ) : Continuous (fun p:ℝ×ℝ ↦ combinedJet c ψ f j p.1 p.2) := by
  unfold combinedJet
  split_ifs
  · exact baseJet_continuous hψ hc _
  · exact responseJet_continuous hψ hf hc _
lemma combinedJet_bound {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (j:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ t x,|combinedJet c ψ f j t x|≤C := by
  unfold combinedJet
  split_ifs
  · exact exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc _
  · exact responseJet_bound hψ hf hc _
lemma combinedJet_space {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (j:ℕ) (t x:ℝ) :
    HasDerivAt (combinedJet c ψ f j t)
      (combinedJet c ψ f (j+2) t x-combinedJet c ψ f j t x*combinedJet c ψ f 2 t x) x := by
  change HasDerivAt (fun y ↦ combinedJet c ψ f j t y)
    (combinedJet c ψ f (j+2) t x-combinedJet c ψ f j t x*combinedJet c ψ f 2 t x) x
  have he:(j+2)/2=j/2+1 := by omega
  have hm:(j+2)%2=j%2 := by omega
  by_cases h:j%2=0
  · simpa only [combinedJet,he,hm,h,show (2:ℕ)%2=0 from rfl,show (2:ℕ)/2=1 from rfl,ite_true] using
      baseJet_space hψ hc (j/2) t x
  · simpa only [combinedJet,he,hm,h,show (2:ℕ)%2=0 from rfl,show (2:ℕ)/2=1 from rfl,ite_true,ite_false] using
      responseJet_space hψ hf hc (j/2) t x
lemma combinedJet_time {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c t:ℝ} (hc:0 ≤ c) (ht:0<t) (j:ℕ) (x:ℝ) :
    HasDerivAt (combinedJet c ψ f j · x)
      ((1/2:ℝ)*(combinedJet c ψ f (j+4) t x-combinedJet c ψ f j t x*combinedJet c ψ f 4 t x)) t := by
  have he:(j+4)/2=j/2+2 := by omega
  have hm:(j+4)%2=j%2 := by omega
  simp only [combinedJet,he,hm,show (4:ℕ)%2=0 from rfl,show (4:ℕ)/2=2 from rfl,ite_true]
  split_ifs
  · exact baseJet_time hψ hc ht (j/2) x
  · exact responseJet_time hψ hf hc ht (j/2) x
namespace JetExpr
lemma eval_responseσx (R:ℕ → ℝ) (j:ℕ) : eval R (responseσx j)=R (j+2)-R j*R 2 := by
  simp only [responseσx,eval];ring
lemma eval_responseσt (R:ℕ → ℝ) (j:ℕ) : eval R (responseσt j)=(1/2:ℝ)*(R (j+4)-R j*R 4) := by
  simp only [responseσt,eval];ring
end JetExpr
lemma responseJet_zero_expr {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) (t:ℝ) :
    iteratedDeriv n (responseJet c ψ f 0 t)=
      fun x ↦ JetExpr.eval (fun j ↦ combinedJet c ψ f j t x) (JetExpr.responseExpr n) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,JetExpr.responseExpr,JetExpr.eval];rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    apply HasDerivAt.deriv
    apply JetExpr.hasDerivAt_eval
    intro j
    simpa only [JetExpr.eval_responseσx] using combinedJet_space hψ hf hc j t x
lemma responseJet_joint_jets {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) :
    Continuous (fun p:ℝ×ℝ ↦ iteratedDeriv n (responseJet c ψ f 0 p.1) p.2) := by
  simp_rw [responseJet_zero_expr hψ hf hc]
  exact JetExpr.continuous_eval (combinedJet_continuous hψ hf hc) _
lemma responseJet_time_jets {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) :
    ∃ d:ℝ → ℝ → ℝ,Continuous (fun p:ℝ×ℝ ↦ d p.1 p.2) ∧
      (∃ C:ℝ,0≤C ∧ ∀ t x,|d t x|≤C) ∧
      ∀ t x,0<t → HasDerivAt (fun s ↦ iteratedDeriv n (responseJet c ψ f 0 s) x) (d t x) t := by
  let E := JetExpr.D JetExpr.responseσt (JetExpr.responseExpr n)
  let d := fun t x ↦ JetExpr.eval (fun j ↦ combinedJet c ψ f j t x) E
  refine ⟨d,JetExpr.continuous_eval (combinedJet_continuous hψ hf hc) E,?_,?_⟩
  · have hb (j:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ p:ℝ×ℝ,|combinedJet c ψ f j p.1 p.2|≤C := by
      obtain ⟨C,hC,hb⟩ := combinedJet_bound hψ hf hc j
      exact ⟨C,hC,fun p ↦ hb p.1 p.2⟩
    obtain ⟨C,hC,hb⟩ := JetExpr.uniform_bound hb E
    exact ⟨C,hC,fun t x ↦ hb (t,x)⟩
  · intro t x ht
    simp_rw [responseJet_zero_expr hψ hf hc]
    apply JetExpr.hasDerivAt_eval
    intro j
    simpa only [JetExpr.eval_responseσt] using combinedJet_time hψ hf hc ht j x
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TestEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma responseJet_zero (c:ℝ) (ψ f:ℝ → ℝ) (x:ℝ) : responseJet c ψ f 0 0 x=f x := by
  simp only [responseJet,iteratedDeriv_zero,heat_zero]
  exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

lemma baseJet_one_eq {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c:ℝ} (hc:0 ≤ c) (t x:ℝ) :
    baseJet c ψ 1 t x=c*deriv (coleHopf c t ψ) x := by
  rcases hc.eq_or_lt with rfl | hc
  · have he : heat t (fun _ : ℝ ↦ (1:ℝ))=fun _ ↦ (1:ℝ) := by
      funext y
      simp [heat]
    simp only [baseJet,normalizedJet,zero_mul,Real.exp_zero,iteratedDeriv_one,he]
    simp
  · rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc t]
    dsimp only [baseJet]
    rw [mul_inv_cancel_left₀ hc.ne']

lemma responseJet_time_lipschitz {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (s t x : ℝ), (0 ≤ s) → (0 ≤ t) →
      |iteratedDeriv n (responseJet c ψ f 0 s) x-iteratedDeriv n (responseJet c ψ f 0 t) x|≤C*|s-t| := by
  obtain ⟨d,hdc,⟨C,hC,hb⟩,hd⟩ := responseJet_time_jets hψ hf hc n
  refine ⟨C,hC,?_⟩
  intro s t x hs ht
  exact nonneg_time_lipschitz hC
    ((responseJet_joint_jets hψ hf hc n).comp (continuous_id.prodMk continuous_const))
    (hdc.comp (continuous_id.prodMk continuous_const))
    (fun r hr ↦ hd r x hr) (fun r _ ↦ hb r x) hs ht

lemma responseJet_backward_pde {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (T:ℝ) {s t:ℝ} (ht:t∈Icc (0:ℝ) T) (hs:s∈Icc (0:ℝ) T) (x:ℝ) :
    responseJet c ψ f 0 (T-s) x-responseJet c ψ f 0 (T-t) x=
      -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (responseJet c ψ f 0 (T-r))) x+
        c*(deriv (coleHopf c (T-r) ψ) x*deriv (responseJet c ψ f 0 (T-r)) x)) := by
  let V := fun r ↦ responseJet c ψ f 0 (T-r)
  let A := fun r ↦ coleHopf c (T-r) ψ
  let g := fun r ↦ (1/2:ℝ)*deriv (deriv (V r)) x+c*(deriv (A r) x*deriv (V r) x)
  have hm : Continuous (fun r : ℝ ↦ (T-r,x)) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hcj (n:ℕ) : Continuous (fun r ↦ iteratedDeriv n (V r) x) := by
    have hh := (responseJet_joint_jets hψ hf hc n).comp hm
    change Continuous (fun r ↦ iteratedDeriv n (responseJet c ψ f 0 (T-r)) x)
    exact hh
  have hgc:Continuous g := by
    have h1:Continuous (fun r ↦ deriv (V r) x) := by simpa only [iteratedDeriv_one] using hcj 1
    have h2:Continuous (fun r ↦ deriv (deriv (V r)) x) := by
      simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hcj 2
    exact (continuous_const.mul h2).add (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).mul h1))
  have hd (r:ℝ) (hr:r∈Ioo (0:ℝ) T) : HasDerivAt (fun r ↦ V r x) (-g r) r := by
    have hh := (responseJet_heat_drift hψ hf hc (sub_pos.mpr hr.2) 0 x).comp r
      ((hasDerivAt_const r T).sub (hasDerivAt_id r))
    rw [baseJet_one_eq hψ hc] at hh
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [V,A,g]
    ring
  have he := integral_from_deriv_on_strip (by simpa only [iteratedDeriv_zero] using (hcj 0).continuousOn)
    hgc.neg.continuousOn hd hs ht
  change _=∫ r in t..s,-(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.linear_constant {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (T:ℝ) :
    LinearEvolution T (fun _ ↦ c) (fun t ↦ coleHopf c (T-t) ψ) (fun t ↦ responseJet c ψ f 0 (T-t)) := by
  refine ⟨fun t _ ↦ responseJet_boundedSmooth hψ hf hc 0 _,?_,?_,?_,?_⟩
  · intro n x
    have hm : Continuous (fun r : ℝ ↦ (T-r,x)) :=
      (continuous_const.sub continuous_id).prodMk continuous_const
    exact ((responseJet_joint_jets hψ hf hc n).comp hm).continuousOn
  · intro n
    obtain ⟨C,hC,hb⟩ := responseJet_uniform_jets hψ hf hc n 0
    exact ⟨C,hC,fun t _ x ↦ hb (T-t) x⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := responseJet_time_lipschitz hψ hf hc n
    refine ⟨C,hC,?_⟩
    intro s hs t ht x
    have hh := hb (T-s) (T-t) x (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2)
    simpa only [sub_sub_sub_cancel_left,abs_sub_comm] using hh
  · intro t ht s hs x
    exact responseJet_backward_pde hψ hf hc T ht hs x
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_TestPatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma patchTime_testjet {a t x:ℝ} (V W:ℝ → ℝ → ℝ) (n:ℕ) :
    iteratedDeriv n (patchTime a V W t) x=
      patchTime a (fun t ↦ iteratedDeriv n (V t) x) (fun t ↦ iteratedDeriv n (W t) x) t := by
  by_cases ht:t≤a <;> simp [patchTime,ht]

lemma LinearEvolution.rhs_integrable {T:ℝ} (hT:0≤T) {γ:ℝ → ℝ} {A V:ℝ → ℝ → ℝ}
    (h:LinearEvolution T γ A V) (hA:SmoothEvolution T γ A)
    (hg:IntervalIntegrable γ volume 0 T) (x:ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))) volume 0 T := by
  have h1:ContinuousOn (fun r ↦ deriv (V r) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have h2:ContinuousOn (fun r ↦ deriv (deriv (V r)) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using h.continuous_jet 2 x
  have ha:ContinuousOn (fun r ↦ deriv (A r) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using hA.continuous_jet 0 x
  exact ((h2.intervalIntegrable.const_mul _).add (hg.mul_continuousOn (ha.mul h1))).neg

lemma LinearEvolution.patch_pde {a b:ℝ} (ha:0≤a) (hb:0≤b)
    {γ η:ℝ → ℝ} {A B V W:ℝ → ℝ → ℝ}
    (hV:LinearEvolution a γ A V) (hW:LinearEvolution b η B W)
    (hA:SmoothEvolution a γ A) (hB:SmoothEvolution b η B)
    (hγ:IntervalIntegrable γ volume 0 a) (hη:IntervalIntegrable η volume 0 b)
    (hjoin:V a=W 0) {s t:ℝ} (hs:s∈Icc (0:ℝ) (a+b)) (ht:t∈Icc (0:ℝ) (a+b)) (x:ℝ) :
    patchTime a V W s x-patchTime a V W t x=
      -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (patchTime a V W r)) x+
        patchTime a γ η r*(deriv (patchTime a A B r) x*deriv (patchTime a V W r) x)) := by
  let p := fun r ↦ -((1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))
  let q := fun r ↦ -((1/2:ℝ)*deriv (deriv (W r)) x+η r*(deriv (B r) x*deriv (W r) x))
  have hp := hV.rhs_integrable ha hA hγ x
  have hq := hW.rhs_integrable hb hB hη x
  have hv:∀ t∈Icc (0:ℝ) a,V t x-V 0 x=∫ r in (0:ℝ)..t,p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw:∀ t∈Icc (0:ℝ) b,W t x-W 0 x=∫ r in (0:ℝ)..t,q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.pde 0 ⟨le_rfl,hb⟩ t ht x
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw (congrFun hjoin x)) hs ht
  rw [←patchTime_apply V W,←patchTime_apply V W] at he
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr:r≤a <;> simp [patchTime,hr]

lemma LinearEvolution.patch {a b:ℝ} (ha:0≤a) (hb:0≤b)
    {γ η:ℝ → ℝ} {A B V W:ℝ → ℝ → ℝ}
    (hV:LinearEvolution a γ A V) (hW:LinearEvolution b η B W)
    (hA:SmoothEvolution a γ A) (hB:SmoothEvolution b η B)
    (hγ:IntervalIntegrable γ volume 0 a) (hη:IntervalIntegrable η volume 0 b)
    (hjoin:V a=W 0) :
    LinearEvolution (a+b) (patchTime a γ η) (patchTime a A B) (patchTime a V W) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t ht
    by_cases hta:t≤a
    · rw [patchTime_left V W hta];exact hV.slices t ⟨ht.1,hta⟩
    · rw [patchTime_right V W (lt_of_not_ge hta)];exact hW.slices (t-a) ⟨by linarith,by linarith [ht.2]⟩
  · intro n x
    simp_rw [patchTime_testjet]
    apply patchTime_continuous (hV.continuous_jet n x) (hW.continuous_jet n x)
    rw [hjoin]
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.bound n
    obtain ⟨D,hD,hw⟩ := hW.bound n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro t ht x
    rw [patchTime_testjet]
    exact patchTime_bound hC hD (fun t ht ↦ hv t ht x) (fun t ht ↦ hw t ht x) t ht
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.temporal n
    obtain ⟨D,hD,hw⟩ := hW.temporal n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro s hs t ht x
    rw [patchTime_testjet,patchTime_testjet]
    apply patchTime_lipschitz ha hb hC hD (fun s hs t ht ↦ hv s hs t ht x)
      (fun s hs t ht ↦ hw s hs t ht x) _ s hs t ht
    rw [hjoin]
  · intro t ht s hs x
    exact hV.patch_pde ha hb hW hA hB hγ hη hjoin hs ht x

lemma SmoothTerminal.linear_profile {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f) (l:HeatProfile) :
    LinearEvolution (profileTime l) (profileCoeff l) (profileValue ψ l) (profileResponse ψ f l) := by
  induction l with
  | nil =>
    change LinearEvolution 0 (fun _ ↦ 0) (fun _ ↦ ψ) (fun _ ↦ f)
    refine ⟨fun t _ ↦ hf,fun _ _ ↦ continuousOn_const,?_,?_,?_⟩
    · intro n
      obtain ⟨C,hC,hb⟩ := hf.bound n
      exact ⟨C,hC,fun _ _ ↦ hb⟩
    · intro n
      exact ⟨0,le_rfl,by intros;simp⟩
    · intro t ht s hs x
      have ht0:t=0 := le_antisymm ht.2 ht.1
      have hs0:s=0 := le_antisymm hs.2 hs.1
      subst t;subst s;simp
  | cons p l ih =>
    have hA := hψ.profile_evolution l
    have hψ' := hA.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hf' := ih.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    apply (hψ'.linear_constant hf' p.2.coe_nonneg (p.1:ℝ)).patch p.1.coe_nonneg (profileTime_nonneg l)
      ih (hψ'.constant_evolution p.2.coe_nonneg (p.1:ℝ)) hA intervalIntegrable_const (profileCoeff_integrable l)
    funext x
    simp only [sub_self,responseJet_zero]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GeneralProfileShape
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SKValue
lemma profileValue_zero_cons (A:ℝ → ℝ) (p:ℝ≥0 × ℝ≥0) (l:HeatProfile) :
    profileValue A (p::l) 0=coleHopf p.2 p.1 (profileValue A l 0) := by
  simp only [profileValue,patchTime_left _ _ p.1.coe_nonneg,sub_zero]
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_FiniteCoercivity
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
lemma BoundedSmooth.pow {f:ℝ → ℝ} (hf:BoundedSmooth f) (n:ℕ) :
    BoundedSmooth (fun x ↦ f x^n) := by
  induction n with
  | zero => simpa only [pow_zero] using BoundedSmooth.const (1:ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul hf
lemma BoundedSmooth.sub {f g:ℝ → ℝ} (hf:BoundedSmooth f) (hg:BoundedSmooth g) :
    BoundedSmooth (fun x ↦ f x-g x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))
lemma SmoothTerminal.spatialJet_boundedSmooth {A:ℝ → ℝ} (hA:SmoothTerminal A)
    (c:ℝ) (n:ℕ) : BoundedSmooth (spatialJet c A n) :=
  (hA.jets.iteratedDeriv n).const_mul c

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_ProfileSplit
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
lemma profileTime_append (l r:HeatProfile) : profileTime (l++r)=profileTime l+profileTime r := by
  induction l with
  | nil => simp [profileTime]
  | cons p l ih => simp only [List.cons_append,profileTime,ih,add_assoc]
lemma profileValue_append_zero (A:ℝ → ℝ) (l r:HeatProfile) :
    profileValue A (l++r) 0=profileValue (profileValue A r 0) l 0 := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,profileValue_zero_cons,ih]
lemma profileValue_append_before (A:ℝ → ℝ) (l r:HeatProfile) {t:ℝ}
    (ht:t∈Icc (0:ℝ) (profileTime l)) :
    profileValue A (l++r) t=profileValue (profileValue A r 0) l t := by
  induction l generalizing t with
  | nil => have ht0:t=0 := le_antisymm ht.2 ht.1; subst t; rfl
  | cons p l ih =>
    change patchTime (p.1:ℝ) _ _ t=patchTime (p.1:ℝ) _ _ t
    by_cases hp:t≤(p.1:ℝ)
    · rw [patchTime_left _ _ hp,patchTime_left _ _ hp]
      congr 1
      exact profileValue_append_zero A l r
    · rw [patchTime_right _ _ (lt_of_not_ge hp),patchTime_right _ _ (lt_of_not_ge hp)]
      apply ih
      constructor
      · exact (sub_pos.mpr (lt_of_not_ge hp)).le
      · have htu:t≤(p.1:ℝ)+profileTime l := ht.2
        linarith
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma splitLength_mul (a b:ℝ) (hab:a≤b) (n:ℕ) :
    ((n+1:ℕ):ℝ)*(splitLength a b hab n)=b-a := by
  change ((n+1:ℕ):ℝ)*((b-a)/(n+1:ℝ))=b-a
  rw [Nat.cast_add,Nat.cast_one]
  field_simp
lemma OrderParameter.splitSegment_time (γ:OrderParameter) (a b:ℝ) (hab:a≤b) (n:ℕ) :
    profileTime (γ.splitSegment a b hab n)=b-a := by
  rw [OrderParameter.splitSegment,gridProfile_time,splitLength_mul]
lemma OrderParameter.splitGrid_time (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    profileTime (γ.splitGrid t n)=1 := by
  rw [OrderParameter.splitGrid,profileTime_append,γ.splitSegment_time,γ.splitSegment_time]
  ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_SplitConvergence
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue
lemma profileHeight_nonneg (l:HeatProfile) : 0 ≤ profileHeight l := by
  cases l with
  | nil => exact le_rfl
  | cons p l => exact p.2.coe_nonneg.trans (le_max_left _ _)
lemma splitSmoothParameter_pos (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    0 < splitSmoothParameter γ t n := add_pos_of_pos_of_nonneg (by positivity) (profileHeight_nonneg _)
lemma splitSmooth_evolution (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    SmoothEvolution 1 (profileCoeff (γ.splitGrid t n)) (splitSmooth γ t n) := by
  unfold splitSmooth
  convert (logCoshTerminal_smoothTerminal (splitSmoothParameter_pos γ t n)).profile_evolution (γ.splitGrid t n) using 1
  all_goals try with_reducible_and_instances rfl
  exact (γ.splitGrid_time t n).symm
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_SplitShape
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
lemma splitTerminal_eq (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    splitTerminal γ t n=splitSmooth γ t n t := by
  unfold splitSmooth OrderParameter.splitGrid
  rw [profileValue_append_before _ _ _ ⟨t.property.1.le,by rw [γ.splitSegment_time,sub_zero]⟩]
  have he:profileTime (γ.splitSegment 0 t t.property.1.le n)=(t:ℝ) := by rw [γ.splitSegment_time,sub_zero]
  exact (by simpa only [he,splitTerminal] using
    (profileValue_terminal (splitTerminal γ t n) (γ.splitSegment 0 t t.property.1.le n)).symm)
lemma splitTerminal_smooth (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    SmoothTerminal (splitTerminal γ t n) := by
  rw [splitTerminal_eq]
  exact (splitSmooth_evolution γ t n).slices t ⟨t.property.1.le,t.property.2.le⟩
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ResponseContraction
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
lemma responseJet_zero_sub {ψ f g:ℝ → ℝ} (hψ:SmoothTerminal ψ)
    (hf:BoundedSmooth f) (hg:BoundedSmooth g) {c:ℝ} (hc:0 ≤ c) (t x:ℝ) :
    responseJet c ψ f 0 t x-responseJet c ψ g 0 t x=
      responseJet c ψ (fun y ↦ f y-g y) 0 t x := by
  simp only [responseJet,iteratedDeriv_zero,←sub_div]
  congr 1
  unfold heat
  rw [←integral_sub]
  · congr 1;funext y;ring
  · exact (weighted_growth hψ hf hc 0).shift_integrable
      ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth).continuous.measurable x (Real.sqrt t)
  · exact (weighted_growth hψ hg hc 0).shift_integrable
      ((contDiff_const.mul hψ.smooth).exp.mul hg.smooth).continuous.measurable x (Real.sqrt t)
lemma responseJet_zero_contraction {ψ f g:ℝ → ℝ} (hψ:SmoothTerminal ψ)
    (hf:BoundedSmooth f) (hg:BoundedSmooth g) {c C:ℝ} (hc:0 ≤ c)
    (hb:∀ x,|f x-g x| ≤ C) (t x:ℝ) :
    |responseJet c ψ f 0 t x-responseJet c ψ g 0 t x| ≤ C := by
  have hsub:BoundedSmooth (fun y ↦ f y-g y) := by
    simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))
  rw [responseJet_zero_sub hψ hf hg hc]
  have hp:0<heat t (fun y ↦ Real.exp (c*ψ y)) x := lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)
  rw [responseJet,iteratedDeriv_zero,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  apply heat_relative_bound ((contDiff_const.mul hψ.smooth).exp).continuous.measurable
    (((contDiff_const.mul hψ.smooth).exp).mul hsub.smooth).continuous.measurable
    (ExpGrowth.exp_lipschitz hψ.lipschitz hc) (weighted_growth hψ hsub hc 0)
  intro y
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos (c*ψ y)).le
lemma SmoothTerminal.profile_response_contraction {ψ f g:ℝ → ℝ} (hψ:SmoothTerminal ψ)
    (hf:BoundedSmooth f) (hg:BoundedSmooth g) {C:ℝ}
    (hb:∀ x,|f x-g x| ≤ C) (l:HeatProfile) (t x:ℝ) :
    |profileResponse ψ f l t x-profileResponse ψ g l t x| ≤ C := by
  induction l generalizing t x with
  | nil => exact hb x
  | cons p l ih =>
    simp only [profileResponse]
    by_cases ht:t ≤ (p.1:ℝ)
    · rw [patchTime_left _ _ ht,patchTime_left _ _ ht]
      exact responseJet_zero_contraction
        ((hψ.profile_evolution l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩)
        ((hψ.linear_profile hf l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩)
        ((hψ.linear_profile hg l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩)
        p.2.coe_nonneg (fun y ↦ ih 0 y) _ x
    · rw [patchTime_right _ _ (lt_of_not_ge ht),patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _ x
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_UniformError
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open scoped Topology
namespace SKValue
lemma uniformDistance_le {A:Type*} [Nonempty A] {f g:A → ℝ} {C:ℝ}
    (h:∀ x,|f x-g x| ≤ C) : uniformDistance f g ≤ C :=
  csSup_le (range_nonempty _) (by rintro _ ⟨x,rfl⟩;exact h x)
lemma le_uniformDistance {A:Type*} {f g:A → ℝ}
    (h:∃ C:ℝ,∀ x,|f x-g x| ≤ C) (x:A) : |f x-g x| ≤ uniformDistance f g := by
  apply le_csSup _ (mem_range_self x)
  obtain ⟨C,hC⟩:=h
  exact ⟨C,by rintro _ ⟨x,rfl⟩;exact hC x⟩
lemma uniformDistance_nonneg {A:Type*} [Nonempty A] {f g:A → ℝ}
    (h:∃ C:ℝ,∀ x,|f x-g x| ≤ C) : 0 ≤ uniformDistance f g := by
  obtain ⟨x⟩:=(inferInstance : Nonempty A)
  exact (abs_nonneg _).trans (le_uniformDistance h x)
lemma uniformDistance_tendsto {A:Type*} [Nonempty A] {F:ℕ → A → ℝ} {f:A → ℝ}
    (h:TendstoUniformly F f atTop) (hb:∀ n,∃ C:ℝ,∀ x,|F n x-f x| ≤ C) :
    Tendsto (fun n ↦ uniformDistance (F n) f) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩:=eventually_atTop.mp ((Metric.tendstoUniformly_iff.mp h) (ε/2) (half_pos hε))
  refine ⟨N,fun n hn ↦ ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (uniformDistance_nonneg (hb n))]
  apply (uniformDistance_le (C:=ε/2) (fun x ↦ ?_)).trans_lt (half_lt_self hε)
  have hx:=hN n hn x
  rw [Real.dist_eq,abs_sub_comm] at hx
  exact hx.le
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_VariableTestLaw
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
lemma IsDiffusion.splitResponse_varying {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) (t:Ioo (0:ℝ) 1) {F:ℕ → ℝ → ℝ} {f:ℝ → ℝ}
    (hF:∀ n,BoundedSmooth (F n)) (hf:BoundedSmooth f) (hl:BoundedUniformLimit F f) :
    Tendsto (fun n ↦ profileResponse (splitTerminal γ t n) (F n) (γ.splitSegment 0 t t.property.1.le n) 0 0)
      atTop (𝓝 (∫ z, f (X t z) ∂W.μ)) := by
  obtain ⟨C,hC,hb,hfb⟩:=hl.bound
  have he:∀ n,∃ D:ℝ,∀ x,|F n x-f x| ≤ D :=
    fun n ↦ ⟨C+C,fun x ↦ (abs_sub _ _).trans (add_le_add (hb n x) (hfb x))⟩
  have hel:=uniformDistance_tendsto hl.tendsto he
  have hd:Tendsto (fun n ↦ profileResponse (splitTerminal γ t n) (F n) (γ.splitSegment 0 t t.property.1.le n) 0 0-
      profileResponse (splitTerminal γ t n) f (γ.splitSegment 0 t t.property.1.le n) 0 0) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ ?_) hel
    rw [Real.norm_eq_abs]
    exact (splitTerminal_smooth γ t n).profile_response_contraction (hF n) hf (le_uniformDistance (he n)) _ _ _
  have ht:=hd.add (hX.splitResponse_tendsto t hf)
  simpa only [sub_add_cancel,zero_add] using ht
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_LiteralCoercivity
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

theorem IsDiffusion.literal_coercivity {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) (t:Ioo (0:ℝ) 1) :
    (1/1000:ℝ)*(∫ z,(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4 ∂W.μ) ≤
      ∫ z,(spatialJet (γ.coeff t) (phi W γ t) 3 (X t z))^2-
        12*spatialJet (γ.coeff t) (phi W γ t) 1 (X t z)*(spatialJet (γ.coeff t) (phi W γ t) 2 (X t z))^2+
        6*(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4 ∂W.μ := by
  let J:=fun n k ↦ spatialJet (γ.coeff t+(gridDelta n:ℝ)) (splitTerminal γ t n) k
  let j:=fun k ↦ spatialJet (γ.coeff t) (phi W γ t) k
  have hJ (n k:ℕ):BoundedSmooth (J n k) := (splitTerminal_smooth γ t n).spatialJet_boundedSmooth _ _
  have hj (k:ℕ):BoundedSmooth (j k) :=
    ((phi_evolution W γ ⟨t.property.1.le,t.property.2⟩).slices t ⟨t.property.1.le,le_rfl⟩).spatialJet_boundedSmooth _ _
  have hl (k:ℕ):BoundedUniformLimit (fun n ↦ J n k) (j k) := split_spatialJet_limit W γ t k
  have hl4:=hX.splitResponse_varying t (fun n ↦ (hJ n 1).pow 4) ((hj 1).pow 4) ((hl 1).pow 4)
  have hpoly:BoundedUniformLimit (fun n x ↦ J n 3 x^2-12*J n 1 x*(J n 2 x)^2+6*(J n 1 x)^4)
      (fun x ↦ j 3 x^2-12*j 1 x*(j 2 x)^2+6*(j 1 x)^4) :=
    (((hl 3).pow 2).sub (((BoundedUniformLimit.const 12).mul (hl 1)).mul ((hl 2).pow 2))).add
      ((BoundedUniformLimit.const 6).mul ((hl 1).pow 4))
  have hlp:=hX.splitResponse_varying t
    (fun n ↦ (((hJ n 3).pow 2).sub (((hJ n 1).const_mul 12).mul ((hJ n 2).pow 2))).add (((hJ n 1).pow 4).const_mul 6))
    ((((hj 3).pow 2).sub (((hj 1).const_mul 12).mul ((hj 2).pow 2))).add (((hj 1).pow 4).const_mul 6)) hpoly
  exact le_of_tendsto_of_tendsto (hl4.const_mul (1/1000:ℝ)) hlp
    (Eventually.of_forall (fun n ↦ split_profile_coercivity γ t n))
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_CurvatureNonneg
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
lemma IsDiffusion.curvature_generator_nonneg {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1):
    0≤∫ z,(iteratedDeriv 3 (deriv (phi W γ t)) (X t z))^2-
      12*γ.coeff t*iteratedDeriv 1 (deriv (phi W γ t)) (X t z)*(iteratedDeriv 2 (deriv (phi W γ t)) (X t z))^2+
      6*(γ.coeff t)^2*(iteratedDeriv 1 (deriv (phi W γ t)) (X t z))^4 ∂W.μ := by
  have hc:=γ.nonneg t ⟨ht.1.le,ht.2⟩
  rcases hc.eq_or_lt with hc|hc
  · rw [←hc]
    simp only [mul_zero,zero_mul,sub_zero,zero_pow (by norm_num: (2:ℕ)≠0),add_zero]
    exact integral_nonneg (fun z ↦ sq_nonneg _)
  · have h:=hX.literal_coercivity ⟨t,ht⟩
    have hn:0≤(1/1000:ℝ)*(∫ z,(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4 ∂W.μ) := by
      apply mul_nonneg (by norm_num)
      exact integral_nonneg (fun z ↦ by positivity)
    have hn:=hn.trans h
    have he:(fun z ↦ (spatialJet (γ.coeff t) (phi W γ t) 3 (X t z))^2-
        12*spatialJet (γ.coeff t) (phi W γ t) 1 (X t z)*(spatialJet (γ.coeff t) (phi W γ t) 2 (X t z))^2+
        6*(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4)=
      (fun z ↦ (γ.coeff t)^2*((iteratedDeriv 3 (deriv (phi W γ t)) (X t z))^2-
        12*γ.coeff t*iteratedDeriv 1 (deriv (phi W γ t)) (X t z)*(iteratedDeriv 2 (deriv (phi W γ t)) (X t z))^2+
        6*(γ.coeff t)^2*(iteratedDeriv 1 (deriv (phi W γ t)) (X t z))^4)) := by
      funext z
      simp only [spatialJet]
      ring
    change 0≤∫ z,(spatialJet (γ.coeff t) (phi W γ t) 3 (X t z))^2-
        12*spatialJet (γ.coeff t) (phi W γ t) 1 (X t z)*(spatialJet (γ.coeff t) (phi W γ t) 2 (X t z))^2+
        6*(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4 ∂W.μ at hn
    rw [he,integral_const_mul] at hn
    exact nonneg_of_mul_nonneg_right hn (sq_pos_of_pos hc)
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_OrderVariations
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

lemma gradientMoment_bound (W : BrownianSpace) (γ : OrderParameter)
    (X : ℝ → W.Ω → ℝ) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    |gradientMoment W γ X t|≤1 := by
  simpa only [gradientMoment,Real.norm_eq_abs,probReal_univ,mul_one] using
    (norm_integral_le_of_norm_le_const (μ := W.μ) (C := (1 : ℝ))
      (f := fun ω ↦ (gradient W γ t (X t ω))^2)
      (Eventually.of_forall (fun ω ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_one_iff_abs_le_one _).mpr (gradient_bound W γ ht _))))

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
lemma continuousAt_of_constant_interval {f:ℝ → ℝ} {a b c t:ℝ}
    (ht:t∈Ioo a b) (he:∀s∈Ioo a b,f s=c):ContinuousAt f t := by
  apply continuousAt_const.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact he s hs
lemma IsDiffusion.jetMoment_continuousAt {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (e:JetExpr):
    ContinuousAt (jetMoment W γ X e) t := by
  obtain ⟨T,htT,hT⟩:=exists_between ht.2
  exact (hX.jetMoment_continuous ⟨ht.1.le.trans htT.le,hT⟩ e).continuousAt (Icc_mem_nhds ht.1 htT)
lemma momentExpr_eq_gradientMoment (W:BrownianSpace) (γ:OrderParameter) (X:ℝ → W.Ω → ℝ):
    jetMoment W γ X JetExpr.momentExpr=gradientMoment W γ X := by
  funext t
  simp only [jetMoment,polyJet,JetExpr.momentExpr_eval,iteratedDeriv_zero,gradientMoment,gradient]
lemma IsDiffusion.curvature_convexOn {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {a b c:ℝ} (ha:0≤a) (hb:b≤1)
    (he:∀t∈Ioo a b,γ.coeff t=c):ConvexOn ℝ (Ioo a b) (jetMoment W γ X JetExpr.curvatureExpr) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo a b)
    (f':=jetMoment W γ X (JetExpr.curvatureSlope c))
  · intro t ht
    exact (hX.jetMoment_continuousAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩ _).continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact (hX.curvatureExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
      (continuousAt_of_constant_interval ht he) (he t ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact (hX.curvatureSlope_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
      (continuousAt_of_constant_interval ht he) (he t ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    exact hX.curvature_generator_nonneg ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_GapBoundary
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
lemma OrderParameter.origin_eq_of_constant {γ:OrderParameter} {b c:ℝ} (hb:0<b)
    (he:∀t∈Ioo (0:ℝ) b,γ.coeff t=c):γ.coeff 0=c := by
  have hl:Tendsto γ.coeff (𝓝[>] (0:ℝ)) (𝓝 (γ.coeff 0)) :=
    (γ.rightContinuous 0 ⟨le_rfl,by norm_num⟩).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hr:Tendsto γ.coeff (𝓝[>] (0:ℝ)) (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with t ht htb
    exact (he t ⟨ht,htb⟩).symm
  exact tendsto_nhds_unique hl hr
lemma IsDiffusion.moment_origin {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X):gradientMoment W γ X 0=0 := by
  have hz:∀ᵐ z ∂W.μ,X 0 z=0 := by
    filter_upwards [hX.2,W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with z h h0
    simpa only [Real.toNNReal_zero,intervalIntegral.integral_same,add_zero,h0] using h.2 0 ⟨le_rfl,by norm_num⟩
  unfold gradientMoment
  calc
    (∫ z,(gradient W γ 0 (X 0 z))^2 ∂W.μ)=∫ z,(0:ℝ) ∂W.μ := by
      apply integral_congr_ae
      filter_upwards [hz] with z hz
      rw [hz,phi_gradient_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    _=0:=integral_zero W.Ω ℝ
end SKValue

end

section
open Set
namespace SKValue
lemma positive_gap_endpoints {G:ℝ → ℝ} (hc:ContinuousOn G (Icc (0:ℝ) 1))
    (hn:∀t∈Icc (0:ℝ) 1,0≤G t) (h1:G 1=0) {x:ℝ} (hx:x∈Ioo (0:ℝ) 1) (hxp:0<G x):
    ∃a b:ℝ,0≤a ∧ a<x ∧ x<b ∧ b≤1 ∧ (a=0 ∨ G a=0) ∧ G b=0 ∧
      ∀t∈Ioo a b,0<G t := by
  let K:=Icc (0:ℝ) 1 ∩ G ⁻¹' {0}
  have hK:IsCompact K := isCompact_Icc.of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  let L:=(K∩Iic x)∪{0}
  have hL:IsCompact L:=(hK.inter_right isClosed_Iic).union isCompact_singleton
  obtain ⟨a,ha⟩:=hL.exists_isGreatest ⟨0,Or.inr (mem_singleton 0)⟩
  let R:=K∩Ici x
  have hR:IsCompact R:=hK.inter_right isClosed_Ici
  have h1R:1∈R:=⟨⟨⟨by norm_num,le_rfl⟩,h1⟩,hx.2.le⟩
  obtain ⟨b,hb⟩:=hR.exists_isLeast ⟨1,h1R⟩
  have ha0:0≤a:=ha.2 (Or.inr (mem_singleton 0))
  have hax:a<x := by
    rcases ha.1 with ha|ha
    · exact lt_of_le_of_ne ha.2 (fun he ↦ by have hz:=ha.1.2;change G a=0 at hz;rw [he] at hz;linarith)
    · have he:a=0:=ha;simpa only [he] using hx.1
  have hxb:x<b := by
    apply lt_of_le_of_ne hb.1.2
    intro he
    have hz:=hb.1.1.2
    change G b=0 at hz
    rw [←he] at hz
    linarith
  refine ⟨a,b,ha0,hax,hxb,hb.1.1.1.2,?_,hb.1.1.2,?_⟩
  · rcases ha.1 with ha|ha
    · exact Or.inr ha.1.2
    · exact Or.inl ha
  · intro t ht
    have ht01:t∈Icc (0:ℝ) 1:=⟨ha0.trans ht.1.le,ht.2.le.trans hb.1.1.1.2⟩
    apply lt_of_le_of_ne (hn t ht01)
    intro he
    have htK:t∈K:=⟨ht01,he.symm⟩
    by_cases htx:t≤x
    · exact not_le_of_gt ht.1 (ha.2 (Or.inl ⟨htK,htx⟩))
    · exact not_le_of_gt ht.2 (hb.2 ⟨htK,(le_of_not_ge htx)⟩)
end SKValue

end

section
open Set
namespace SKValue

lemma not_three_slope_pattern {f f':ℝ → ℝ} {a x y b:ℝ}
    (hax:a<x) (hxy:x<y) (hyb:y<b) (hc:ContinuousOn f (Icc a b))
    (hd:∀t∈Ioo a b,HasDerivAt f (f' t) t) (hv:ConvexOn ℝ (Ioo a b) f')
    (hleft:f x≤f a) (hmid:f x<f y) (hright:f b≤f y):False := by
  obtain ⟨r,hr,her⟩:=exists_hasDerivAt_eq_slope f f' hax
    (hc.mono (Icc_subset_Icc le_rfl (hxy.le.trans hyb.le)))
    (fun t ht ↦ hd t ⟨ht.1,ht.2.trans hxy |>.trans hyb⟩)
  obtain ⟨s,hs,hes⟩:=exists_hasDerivAt_eq_slope f f' hxy
    (hc.mono (Icc_subset_Icc hax.le hyb.le))
    (fun t ht ↦ hd t ⟨hax.trans ht.1,ht.2.trans hyb⟩)
  obtain ⟨u,hu,heu⟩:=exists_hasDerivAt_eq_slope f f' hyb
    (hc.mono (Icc_subset_Icc (hax.le.trans hxy.le) le_rfl))
    (fun t ht ↦ hd t ⟨hax.trans hxy |>.trans ht.1,ht.2⟩)
  have hr0:f' r≤0:=by rw [her];exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hleft) (sub_pos.mpr hax).le
  have hs0:0<f' s:=by rw [hes];exact div_pos (sub_pos.mpr hmid) (sub_pos.mpr hxy)
  have hu0:f' u≤0:=by rw [heu];exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hright) (sub_pos.mpr hyb).le
  have hh:=hv.le_max_of_mem_Icc ⟨hr.1,hr.2.trans hxy |>.trans hyb⟩
    ⟨hax.trans hxy |>.trans hu.1,hu.2⟩ ⟨(hr.2.trans hs.1).le,(hs.2.trans hu.1).le⟩
  exact (not_lt_of_ge (hh.trans (max_le hr0 hu0))) hs0
end SKValue

end

section
open Set
namespace SKValue
lemma positive_hump_impossible {f f' G:ℝ → ℝ} {a b x:ℝ}
    (hax:a<x) (hxb:x<b) (_:b≤1)
    (hGc:ContinuousOn G (Icc a b)) (hGd:∀t∈Ioo a b,HasDerivAt G (-f t) t)
    (hGa:G a=0) (hGb:G b=0) (hGx:0<G x)
    (hfc:ContinuousOn f (Ico a 1)) (hfd:∀t∈Ioo a b,HasDerivAt f (f' t) t)
    (hfa:f a=0) (hv:ConvexOn ℝ (Ioo a b) f')
    (hend:∀s∈Ioo a b,0<f s → ∃z∈Ioo s 1,z≤b ∧ f z≤f s):False := by
  obtain ⟨r,hr,her⟩:=exists_hasDerivAt_eq_slope G (fun t ↦ -f t) hax
    (hGc.mono (Icc_subset_Icc le_rfl hxb.le)) (fun t ht ↦ hGd t ⟨ht.1,ht.2.trans hxb⟩)
  obtain ⟨s,hs,hes⟩:=exists_hasDerivAt_eq_slope G (fun t ↦ -f t) hxb
    (hGc.mono (Icc_subset_Icc hax.le le_rfl)) (fun t ht ↦ hGd t ⟨hax.trans ht.1,ht.2⟩)
  have hr0:f r<0 := by
    rw [hGa,sub_zero] at her
    have hh:=div_pos hGx (sub_pos.mpr hax)
    linarith
  have hs0:0<f s := by
    rw [hGb,zero_sub] at hes
    have hh:=div_neg_of_neg_of_pos (neg_neg_of_pos hGx) (sub_pos.mpr hxb)
    linarith
  obtain ⟨z,hz,hzb,hfz⟩:=hend s ⟨hax.trans hs.1,hs.2⟩ hs0
  apply not_three_slope_pattern hr.1 (hr.2.trans hs.1) hz.1
    (hfc.mono (fun t ht ↦ ⟨ht.1,ht.2.trans_lt hz.2⟩))
    (fun t ht ↦ hfd t ⟨ht.1,ht.2.trans_le hzb⟩)
    (hv.subset (Ioo_subset_Ioo le_rfl hzb) (convex_Ioo a z))
  · simpa only [hfa] using hr0.le
  · exact hr0.trans hs0
  · exact hfz
lemma endpoint_condition {f:ℝ → ℝ} {a b:ℝ} (hb:b≤1)
    (hfb:b<1 → f b=0) (hbound:∀t∈Ioo a 1,f t≤1-t):
    ∀s∈Ioo a b,0<f s → ∃z∈Ioo s 1,z≤b ∧ f z≤f s := by
  intro s hs hfs
  rcases hb.lt_or_eq with hb|rfl
  · exact ⟨b,⟨hs.2,hb⟩,le_rfl,by rw [hfb hb];exact hfs.le⟩
  · have hm:max s (1-f s)<1:=max_lt hs.2 (by linarith)
    obtain ⟨z,hz,hz1⟩:=exists_between hm
    refine ⟨z,⟨(le_max_left _ _).trans_lt hz,hz1⟩,hz1.le,?_⟩
    have hsz:s<z:=(le_max_left _ _).trans_lt hz
    have hgz:1-f s<z:=(le_max_right _ _).trans_lt hz
    have hh:=hbound z ⟨hs.1.trans hsz,hz1⟩
    linarith
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_ZeroGapHump
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set
namespace SKValue
lemma positive_right_hump_impossible {f G:ℝ → ℝ} {a b x:ℝ}
    (hax:a<x) (hxb:x<b)
    (hGc:ContinuousOn G (Icc a b)) (hGd:∀t∈Ioo a b,HasDerivAt G (-f t) t)
    (hGb:G b=0) (hGx:0<G x) (hfa:f a=0)
    (hv:∀z∈Ioo a 1,z≤b → ConvexOn ℝ (Icc a z) f)
    (hend:∀s∈Ioo a b,0<f s → ∃z∈Ioo s 1,z≤b ∧ f z≤f s):False := by
  obtain ⟨s,hs,hes⟩:=exists_hasDerivAt_eq_slope G (fun t ↦ -f t) hxb
    (hGc.mono (Icc_subset_Icc hax.le le_rfl)) (fun t ht ↦ hGd t ⟨hax.trans ht.1,ht.2⟩)
  have hs0:0<f s := by
    rw [hGb,zero_sub] at hes
    have hh:=div_neg_of_neg_of_pos (neg_neg_of_pos hGx) (sub_pos.mpr hxb)
    linarith
  obtain ⟨z,hz,hzb,hfz⟩:=hend s ⟨hax.trans hs.1,hs.2⟩ hs0
  have has:a < s:=hax.trans hs.1
  have hav:a<z:=has.trans hz.1
  have hc:=hv z ⟨hav,hz.2⟩ hzb
  have hh:=hc.slope_mono_adjacent ⟨le_rfl,hav.le⟩ ⟨hav.le,le_rfl⟩ has hz.1
  have hl:0<(f s-f a)/(s-a):=div_pos (by rw [hfa,sub_zero];exact hs0) (sub_pos.mpr has)
  have hr:(f z-f s)/(z-s)≤0:=div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hfz) (sub_pos.mpr hz.1).le
  exact not_lt_of_ge (hh.trans hr) hl
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Variation_MinimizerContact
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

lemma IsMinimizer.contactPotential_zero {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hγ:IsMinimizer W γ) (hX:IsDiffusion W γ X) {x:ℝ} (hx:x∈Ioo (0:ℝ) 1):
    contactPotential W γ X x=0 := by
  by_contra hne
  have hxp:0 < contactPotential W γ X x:=lt_of_le_of_ne
    (hγ.contactPotential_nonneg hX ⟨hx.1.le,hx.2.le⟩) (Ne.symm hne)
  obtain ⟨a,b,ha,hax,hxb,hb,haG,hGb,hpos⟩:=positive_gap_endpoints
    hX.contactPotential_continuous (fun t ht ↦ hγ.contactPotential_nonneg hX ht)
    (by simp only [contactPotential,intervalIntegral.integral_same]) hx hxp
  have hab:a<b:=hax.trans hxb
  have ha1:a<1:=hax.trans hx.2
  have hb0:0<b:=hx.1.trans hxb
  let c:=γ.coeff x
  have he:∀t∈Ioo a b,γ.coeff t=c := fun t ht ↦
    hγ.coeff_constant_of_contactPositive hX ha hb hpos t ht x ⟨hax,hxb⟩
  let f:=fun t ↦ gradientMoment W γ X t-t
  have hf0:f a=0 := by
    rcases haG with ha0|haG
    · simp only [f,ha0,hX.moment_origin,sub_self]
    · by_cases ha0:a=0
      · simp only [f,ha0,hX.moment_origin,sub_self]
      · exact sub_eq_zero.mpr (hγ.moment_eq_at_contact hX ⟨lt_of_le_of_ne ha (Ne.symm ha0),ha1⟩ haG)
  have hGc:ContinuousOn (contactPotential W γ X) (Icc a b):=
    hX.contactPotential_continuous.mono (Icc_subset_Icc ha hb)
  have hGd:∀t∈Ioo a b,HasDerivAt (contactPotential W γ X) (-f t) t := by
    intro t ht
    simpa only [f,neg_sub] using hX.contactPotential_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
  have hfc:ContinuousOn f (Ico a 1):=
    (hX.gradientMoment_continuous.sub continuousOn_id).mono (Ico_subset_Ico_left ha)
  have hend:∀s∈Ioo a b,0<f s → ∃z∈Ioo s 1,z≤b ∧ f z≤f s := by
    apply endpoint_condition hb
    · intro hb1
      exact sub_eq_zero.mpr (hγ.moment_eq_at_contact hX ⟨hb0,hb1⟩ hGb)
    · intro t ht
      have hh:gradientMoment W γ X t≤1:=(le_abs_self _).trans
        (gradientMoment_bound W γ X ⟨(ha.trans_lt ht.1).le,ht.2.le⟩)
      dsimp only [f];linarith
  by_cases hc:c=0
  · apply positive_right_hump_impossible hax hxb hGc hGd hGb hxp hf0 ?_ hend
    intro z hz hzb
    have hv:=hX.moment_convexOn_zero_closed ha hz.2
      (fun t ht ↦ (he t ⟨ht.1,ht.2.trans_le hzb⟩).trans hc)
    exact hv.sub (concaveOn_id (convex_Icc a z))
  · have hcpos:0 < c:=lt_of_le_of_ne (γ.nonneg x ⟨hx.1.le,hx.2⟩) (Ne.symm hc)
    have hGa:contactPotential W γ X a=0 := by
      rcases haG with ha0|haG
      · subst a
        have h0:=γ.origin_eq_of_constant hb0 he
        exact hγ.contact_origin_of_positive hX (by simpa only [h0] using hcpos)
      · exact haG
    let f':=fun t ↦ jetMoment W γ X JetExpr.curvatureExpr t-1
    have hfd:∀t∈Ioo a b,HasDerivAt f (f' t) t := by
      intro t ht
      have hd:=hX.momentExpr_hasDerivAt ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
        (continuousAt_of_constant_interval ht he)
      rw [momentExpr_eq_gradientMoment] at hd
      exact hd.sub (hasDerivAt_id t)
    have hcv:ConvexOn ℝ (Ioo a b) f':=
      (hX.curvature_convexOn ha hb he).sub (concaveOn_const 1 (convex_Ioo a b))
    exact positive_hump_impossible hax hxb hb hGc hGd hGa hGb hxp hfc hfd hf0 hcv hend

theorem IsMinimizer.gradient_moment_contact_oai {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hγ:IsMinimizer W γ) (hX:IsDiffusion W γ X):
    ∀t∈Ico (0:ℝ) 1,(∫ z,(gradient W γ t (X t z))^2 ∂W.μ)=t := by
  intro t ht
  change gradientMoment W γ X t=t
  rcases ht.1.eq_or_lt with he|he
  · rw [←he];exact hX.moment_origin
  · exact hγ.moment_eq_at_contact hX ⟨he,ht.2⟩ (hγ.contactPotential_zero hX ⟨he,ht.2⟩)
end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.IsMinimizer.gradient_moment_contact_oai := @OAI.SKValue.IsMinimizer.gradient_moment_contact_oai
