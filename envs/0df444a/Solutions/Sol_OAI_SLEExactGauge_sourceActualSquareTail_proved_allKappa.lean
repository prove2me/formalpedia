-- Prove2me | solution 1 for OAI.SLEExactGauge.sourceActualSquareTail_proved_allKappa
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:47:28.351041+00:00
-- url     : https://prove2.me/submissions/5ae54f92-1331-4c78-81bf-0a5d4a343235

import Mathlib
import Definitions.Def_SLELowerPositivity
import Definitions.Def_OAIQ27Sle000
import Theorems.Thm_OAI_SLEExactGauge_RegularSLEPresentation_source_past_spatial_slab_finite_exponential
import Theorems.Thm_OAI_SLEExactGauge_source_mesh_parameters

section
-- module Solutions.OAIQ27_SLE.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_BrownianGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Brownian Generators for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma brownian_increment_indep_natural
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s t : ℝ≥0) :
    Indep (Filtration.natural B (fun t => (hm t).stronglyMeasurable) s)
      ((borel ℝ).comap (fun ω => B (s + t) ω - B s ω)) P := by
  have hi := ((hB.indepFun_shift s).comp (measurable_pi_apply t) measurable_id).symm
  rw [Filtration.natural_eq_comap B _ s]
  exact (IndepFun_iff_Indep _ _ _).mp hi

lemma brownian_increment_indep_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s t : ℝ≥0) {f : Ω → ℝ}
    (hf : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] f) :
    IndepFun f (fun ω => B (s + t) ω - B s ω) P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le (brownian_increment_indep_natural hB hm s t) hf.comap_le le_rfl

lemma gaussian_square_integral (δ : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 δ) = δ := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := δ)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at h
  simpa using h

lemma gaussian_centered_square_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {δ : ℝ≥0} (hX : HasLaw X (gaussianReal 0 δ) P) :
    (∫ ω, X ω ^ 2 - (δ : ℝ) ∂P) = 0 := by
  have he := hX.integral_comp (f := fun x : ℝ => x ^ 2 - (δ : ℝ)) (by fun_prop)
  simp only [Function.comp_apply] at he
  rw [he]
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 δ) :=
    (memLp_id_gaussianReal (μ := 0) (v := δ) 2).integrable_sq
  rw [integral_sub h2 (integrable_const _), gaussian_square_integral]
  simp

lemma real_second_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (K : ℝ≥0) (hK : ∀ z, |iteratedDeriv 3 f z| ≤ K) (x y : ℝ) :
    |f (x + y) - f x - deriv f x * y - (1 / 2 : ℝ) * iteratedDeriv 2 f x * y ^ 2| ≤
      (K : ℝ) * |y| ^ 3 := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (x := x) (y := y)
    (fun (_t : ℝ) (_ht : _ ∈ Icc (0 : ℝ) 1) => hf.contDiffAt)
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at ht
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one] at ht
  have hi : |∫ t : ℝ in 0..1, (1 - t) ^ 2 * (y ^ 3 * iteratedDeriv 3 f (x + t * y))| ≤
      (K : ℝ) * |y| ^ 3 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := (K : ℝ) * |y| ^ 3)
      (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => (1 - t) ^ 2 * (y ^ 3 * iteratedDeriv 3 f (x + t * y))) ?_
    · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
    · intro t ht
      have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
      have ht1 : |1 - t| ≤ 1 := by rw [abs_of_nonneg (by linarith [ht'.2])]; linarith [ht'.1]
      simp only [Real.norm_eq_abs, abs_mul, abs_pow]
      calc
        |1 - t| ^ 2 * (|y| ^ 3 * |iteratedDeriv 3 f (x + t * y)|) ≤
            1 ^ 2 * (|y| ^ 3 * (K : ℝ)) := by gcongr; exact hK _
        _ = (K : ℝ) * |y| ^ 3 := by ring
  have he : f (x + y) - f x - deriv f x * y - (1 / 2 : ℝ) * iteratedDeriv 2 f x * y ^ 2 =
      (1 / 2 : ℝ) * ∫ t : ℝ in 0..1, (1 - t) ^ 2 * (y ^ 3 * iteratedDeriv 3 f (x + t * y)) := by
    rw [ht]
    ring
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith [show 0 ≤ (K : ℝ) * |y| ^ 3 by positivity]

lemma standardGaussianAbsMoment_nonneg (m : ℕ) : 0 ≤ standardGaussianAbsMoment m :=
  integral_nonneg fun x => pow_nonneg (abs_nonneg x) m

lemma gaussian_abs_moment_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {δ : ℝ≥0} (hX : HasLaw X (gaussianReal 0 δ) P)
    (m : ℕ) (hm : m ≠ 0) : Integrable (fun ω => |X ω| ^ m) P := by
  have hm' : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
  have hp : MemLp X m P := hX.hasGaussianLaw.memLp hm'
  simpa only [Real.norm_eq_abs] using hp.integrable_norm_pow hm

lemma gaussian_abs_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {δ : ℝ≥0} (hX : HasLaw X (gaussianReal 0 δ) P)
    (m : ℕ) : (∫ ω, |X ω| ^ m ∂P) = (Real.sqrt δ) ^ m * standardGaussianAbsMoment m := by
  have he := hX.integral_comp (f := fun x : ℝ => |x| ^ m) (by fun_prop)
  simp only [Function.comp_apply] at he
  rw [he]
  have hm : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt δ * x) = gaussianReal 0 δ := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt δ.coe_nonneg]
  rw [← hm, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, mul_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [integral_const_mul]
  rfl

lemma gaussian_abs_cube {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {δ : ℝ≥0} (hX : HasLaw X (gaussianReal 0 δ) P) :
    (∫ ω, |X ω| ^ 3 ∂P) = (δ : ℝ) * Real.sqrt δ * standardGaussianAbsMoment 3 := by
  rw [gaussian_abs_moment hX]
  congr 1
  rw [pow_succ, Real.sq_sqrt δ.coe_nonneg]

lemma SmoothTimeBrownianField.eval_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (t : ℝ≥0) (j : ℕ) (hj : j ≤ 2)
    {V : Ω → ℝ} (hV : Measurable V) :
    Measurable (fun ω => iteratedDeriv j (F t ω) (V ω)) :=
  (hF.joint j hj).comp ((measurable_const.prodMk measurable_id).prodMk hV)

lemma SmoothTimeBrownianField.eval_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (t : ℝ≥0) (j : ℕ) (hj : j ≤ 2) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) t]
      (fun ω => iteratedDeriv j (F t ω) (B t ω)) := by
  have hBt := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable) t).measurable
  exact (hF.adapted t j hj).comp (measurable_id.prodMk hBt)

lemma brownian_increment_orthogonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s δ : ℝ≥0) {f : Ω → ℝ}
    (hf : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] f) :
    (∫ ω, f ω * (B (s + δ) ω - B s ω) ∂P) = 0 := by
  have hif := brownian_increment_indep_adapted hB hm s δ hf
  have hfm : Measurable f := hf.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hlaw := (hB.shift s).hasLaw_eval δ
  rw [hif.integral_fun_mul_eq_mul_integral hfm.aestronglyMeasurable
    ((hm _).sub (hm _)).aestronglyMeasurable, hlaw.integral_eq]
  simp

lemma brownian_centered_square_orthogonal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s δ : ℝ≥0) {f : Ω → ℝ}
    (hf : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] f) :
    (∫ ω, f ω * ((B (s + δ) ω - B s ω) ^ 2 - (δ : ℝ)) ∂P) = 0 := by
  have hif := (brownian_increment_indep_adapted hB hm s δ hf).comp
    measurable_id (by fun_prop : Measurable (fun x : ℝ => x ^ 2 - (δ : ℝ)))
  have hfm : Measurable f := hf.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hlaw := (hB.shift s).hasLaw_eval δ
  have he := hif.integral_fun_mul_eq_mul_integral
    hfm.aestronglyMeasurable (((hm _).sub (hm _)).pow_const 2 |>.sub measurable_const).aestronglyMeasurable
  simp only [Function.comp_apply, id_eq] at he
  rw [he, gaussian_centered_square_integral hlaw, mul_zero]

lemma brownian_set_integral_increment_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s δ : ℝ≥0) {f : Ω → ℝ} {E : Set Ω}
    (hf : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] f)
    (hE : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] E) :
    (∫ ω in E, f ω * (B (s + δ) ω - B s ω) ∂P) = 0 := by
  have hEm : MeasurableSet E :=
    (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s _ hE
  have h := brownian_increment_orthogonal hB hm s δ (hf.indicator hE)
  rw [← integral_indicator hEm]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  by_cases hω : ω ∈ E <;> simp [hω]

lemma brownian_set_integral_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s δ C : ℝ≥0) {f : Ω → ℝ} {E : Set Ω}
    (hf : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] f)
    (hbound : ∀ ω, |f ω| ≤ C)
    (hE : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] E) :
    (∫ ω in E, f ω * (B (s + δ) ω - B s ω) ^ 2 ∂P) =
      (δ : ℝ) * ∫ ω in E, f ω ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hEm : MeasurableSet E :=
    (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s _ hE
  have hfm := hf.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hfi : Integrable f (P.restrict E) :=
    Integrable.of_bound hfm.aestronglyMeasurable _ (Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hbound ω)
  have hi2 : Integrable (fun ω => (B (s + δ) ω - B s ω) ^ 2) (P.restrict E) :=
    ((hB.shift s).hasLaw_eval δ).hasGaussianLaw.memLp_two.integrable_sq.restrict
  have hprod := hi2.bdd_mul hfm.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound ω)
  have h := brownian_centered_square_orthogonal hB hm s δ (hf.indicator hE)
  have hz : (∫ ω in E, f ω * ((B (s + δ) ω - B s ω) ^ 2 - (δ : ℝ)) ∂P) = 0 := by
    rw [← integral_indicator hEm]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  simp_rw [mul_sub] at hz
  rw [integral_sub hprod (hfi.mul_const _), integral_mul_const] at hz
  linarith

lemma smooth_field_taylor_set_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (K : ℝ≥0) {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (s δ : ℝ≥0) {E : Set Ω}
    (hE : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] E) :
    |(∫ ω in E, F s ω (B (s + δ) ω) - F s ω (B s ω) ∂P) -
      (1 / 2 : ℝ) * (δ : ℝ) * ∫ ω in E, iteratedDeriv 2 (F s ω) (B s ω) ∂P| ≤
      (K : ℝ) * (δ : ℝ) * Real.sqrt δ * standardGaussianAbsMoment 3 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let X (ω : Ω) := B (s + δ) ω - B s ω
  let c₁ (ω : Ω) := iteratedDeriv 1 (F s ω) (B s ω)
  let c₂ (ω : Ω) := iteratedDeriv 2 (F s ω) (B s ω)
  let T (ω : Ω) := F s ω (B (s + δ) ω) - F s ω (B s ω)
  let R (ω : Ω) := T ω - c₁ ω * X ω - (1 / 2 : ℝ) * (c₂ ω * X ω ^ 2)
  have hXlaw : HasLaw X (gaussianReal 0 δ) P := (hB.shift s).hasLaw_eval δ
  have hXm : Measurable X := (hm _).sub (hm _)
  have hc₁m : Measurable c₁ := hF.eval_measurable s 1 (by decide) (hm s)
  have hc₂m : Measurable c₂ := hF.eval_measurable s 2 (by decide) (hm s)
  have hc₁b (ω) : |c₁ ω| ≤ K := hF.bound s ω _ 1 (by decide)
  have hc₂b (ω) : |c₂ ω| ≤ K := hF.bound s ω _ 2 (by decide)
  have hI (t : ℝ≥0) : Integrable (fun ω => F s ω (B t ω)) (P.restrict E) := by
    have hm' : Measurable (fun ω => F s ω (B t ω)) := by
      simpa only [iteratedDeriv_zero] using hF.eval_measurable s 0 (by decide) (hm t)
    refine Integrable.of_bound hm'.aestronglyMeasurable K (Eventually.of_forall fun ω => ?_)
    simpa only [Real.norm_eq_abs, iteratedDeriv_zero] using hF.bound s ω (B t ω) 0 (by decide)
  have hTi : Integrable T (P.restrict E) := (hI _).sub (hI _)
  have hlin : Integrable (fun ω => c₁ ω * X ω) (P.restrict E) :=
    hXlaw.hasGaussianLaw.integrable.restrict.bdd_mul hc₁m.aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hc₁b ω)
  have hquad : Integrable (fun ω => c₂ ω * X ω ^ 2) (P.restrict E) :=
    hXlaw.hasGaussianLaw.memLp_two.integrable_sq.restrict.bdd_mul hc₂m.aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hc₂b ω)
  have hRi : Integrable R (P.restrict E) := (hTi.sub hlin).sub (hquad.const_mul _)
  have hlin0 : (∫ ω in E, c₁ ω * X ω ∂P) = 0 :=
    brownian_set_integral_increment_zero hB hm s δ (hF.eval_adapted s 1 (by decide)) hE
  have hquad0 : (∫ ω in E, c₂ ω * X ω ^ 2 ∂P) = (δ : ℝ) * ∫ ω in E, c₂ ω ∂P :=
    brownian_set_integral_square hB hm s δ K (hF.eval_adapted s 2 (by decide)) hc₂b hE
  have hRint : (∫ ω in E, R ω ∂P) = (∫ ω in E, T ω ∂P) -
      (1 / 2 : ℝ) * (δ : ℝ) * ∫ ω in E, c₂ ω ∂P := by
    dsimp only [R]
    have hsubi : Integrable (fun ω => T ω - c₁ ω * X ω) (P.restrict E) := hTi.sub hlin
    rw [integral_sub hsubi (hquad.const_mul (1 / 2 : ℝ)), integral_sub hTi hlin,
      hlin0, sub_zero, integral_const_mul, hquad0]
    ring
  have hRb (ω) : |R ω| ≤ (K : ℝ) * |X ω| ^ 3 := by
    have h := real_second_taylor_bound (hF.smooth s ω) K
      (fun z => hF.bound s ω z 3 (by decide)) (B s ω) (X ω)
    have he : B s ω + X ω = B (s + δ) ω := by dsimp [X]; ring
    rw [he] at h
    simpa only [R, T, c₁, c₂, iteratedDeriv_one, mul_assoc] using h
  change |(∫ ω in E, T ω ∂P) - (1 / 2 : ℝ) * (δ : ℝ) * ∫ ω in E, c₂ ω ∂P| ≤ _
  rw [← hRint]
  have hcube := gaussian_abs_moment_integrable hXlaw 3 (by decide)
  calc
    |∫ ω in E, R ω ∂P| ≤ ∫ ω in E, |R ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P.restrict E) R
    _ ≤ ∫ ω in E, (K : ℝ) * |X ω| ^ 3 ∂P :=
      integral_mono hRi.abs (hcube.restrict.const_mul _) hRb
    _ ≤ ∫ ω, (K : ℝ) * |X ω| ^ 3 ∂P :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun _ => by positivity) (hcube.const_mul _)
    _ = (K : ℝ) * (δ : ℝ) * Real.sqrt δ * standardGaussianAbsMoment 3 := by
      rw [integral_const_mul, gaussian_abs_cube hXlaw]
      ring

lemma brownian_expected_abs_increment_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (r t δ : ℝ≥0) (hgap : |(t : ℝ) - r| ≤ δ) (E : Set Ω) :
    (∫ ω in E, |B t ω - B r ω| ∂P) ≤ Real.sqrt δ * standardGaussianAbsMoment 1 := by
  have hlaw : HasLaw (fun ω => B t ω - B r ω)
      (gaussianReal 0 (nndist (t : ℝ) (r : ℝ))) P := hB.hasLaw_sub t r
  have hint : Integrable (fun ω => |B t ω - B r ω|) P := hlaw.hasGaussianLaw.integrable.abs
  calc
    (∫ ω in E, |B t ω - B r ω| ∂P) ≤ ∫ ω, |B t ω - B r ω| ∂P :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun _ => abs_nonneg _) hint
    _ = Real.sqrt (nndist (t : ℝ) (r : ℝ)) * standardGaussianAbsMoment 1 := by
      simpa only [pow_one, Pi.sub_apply] using gaussian_abs_moment hlaw 1
    _ ≤ Real.sqrt δ * standardGaussianAbsMoment 1 := by
      apply mul_le_mul_of_nonneg_right _ (standardGaussianAbsMoment_nonneg 1)
      apply Real.sqrt_le_sqrt
      simpa only [coe_nndist, Real.dist_eq] using hgap

lemma bounded_interval_integral_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (a b : ℝ) (hab : a ≤ b) (G : ℝ → Ω → ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ)
    (hbound : ∀ u ω, |G u ω| ≤ C) :
    Integrable (fun ω => ∫ u in a..b, G u ω) P := by
  have hI : Integrable (Function.uncurry G) ((volume.restrict (Ioc a b)).prod P) :=
    Integrable.of_bound hG.aestronglyMeasurable C
      (Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs, Function.uncurry] using hbound q.1 q.2)
  simpa only [intervalIntegral.integral_of_le hab, Function.uncurry] using hI.integral_prod_right

lemma bounded_interval_integral_expectation_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (a b : ℝ) (hab : a ≤ b) (G : ℝ → Ω → ℝ)
    (hG : Measurable (Function.uncurry G)) (C D : ℝ)
    (hbound : ∀ u ω, |G u ω| ≤ C)
    (hmean : ∀ u ∈ Ioc a b, |∫ ω, G u ω ∂P| ≤ D) :
    |∫ ω, (∫ u in a..b, G u ω) ∂P| ≤ D * (b - a) := by
  have hI : Integrable (Function.uncurry G) ((volume.restrict (Ioc a b)).prod P) :=
    Integrable.of_bound hG.aestronglyMeasurable C
      (Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs, Function.uncurry] using hbound q.1 q.2)
  simp_rw [intervalIntegral.integral_of_le hab]
  rw [← integral_integral_swap hI]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun u => ∫ ω, G u ω ∂P) (C := D) (fun u hu => by
      simpa only [Real.norm_eq_abs] using hmean u (by simpa only [uIoc_of_le hab] using hu))
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_of_le hab,
    abs_of_nonneg (sub_nonneg.mpr hab)] using h

lemma bounded_time_section_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω] (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Ω → ℝ) (hG : Measurable (Function.uncurry G)) (C : ℝ)
    (hbound : ∀ u ω, |G u ω| ≤ C) (ω : Ω) :
    IntervalIntegrable (fun u => G u ω) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Integrable.of_bound ((hG.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) C
  exact Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs, Function.comp_apply, Function.uncurry, id_eq] using hbound u ω

lemma smooth_field_time_set_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (K : ℝ≥0) {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (s δ : ℝ≥0) (E : Set Ω) :
    |(∫ ω in E, F (s + δ) ω (B (s + δ) ω) - F s ω (B (s + δ) ω) ∂P) -
      ∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), a u.toNNReal ω (B u.toNNReal ω)) ∂P| ≤
      (K : ℝ) * (δ : ℝ) * Real.sqrt δ * standardGaussianAbsMoment 1 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let C (u : ℝ) (ω : Ω) := a u.toNNReal ω (B (s + δ) ω)
  let D (u : ℝ) (ω : Ω) := a u.toNNReal ω (B u.toNNReal ω)
  let G (u : ℝ) (ω : Ω) := C u ω - D u ω
  have htime : Measurable (fun q : ℝ × Ω => (q.1.toNNReal, q.2)) := by fun_prop
  have hC : Measurable (Function.uncurry C) :=
    hF.drift_joint.comp (htime.prodMk ((hm (s + δ)).comp measurable_snd))
  have hD : Measurable (Function.uncurry D) :=
    hF.drift_joint.comp (htime.prodMk (hBm.comp htime))
  have hG : Measurable (Function.uncurry G) := hC.sub hD
  have hCb (u ω) : |C u ω| ≤ K := hF.drift_bound _ _ _
  have hDb (u ω) : |D u ω| ≤ K := hF.drift_bound _ _ _
  have hGb (u ω) : |G u ω| ≤ 2 * (K : ℝ) := by
    exact (abs_sub _ _).trans (by linarith [hCb u ω, hDb u ω])
  have hle : (s : ℝ) ≤ (s + δ : ℝ≥0) := by
    simp only [NNReal.coe_add]; exact le_add_of_nonneg_right δ.coe_nonneg
  have hCI := bounded_interval_integral_integrable (P := P.restrict E) _ _ hle C hC K hCb
  have hDI := bounded_interval_integral_integrable (P := P.restrict E) _ _ hle D hD K hDb
  have he : (∫ ω in E, F (s + δ) ω (B (s + δ) ω) - F s ω (B (s + δ) ω) ∂P) -
      (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), D u ω) ∂P) =
      ∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), G u ω) ∂P := by
    simp_rw [hF.time_increment s (s + δ) (le_add_of_nonneg_right (zero_le))]
    change (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), C u ω) ∂P) - _ = _
    rw [← integral_sub hCI hDI]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω =>
      (intervalIntegral.integral_sub
        (bounded_time_section_intervalIntegrable _ _ hle C hC K hCb ω)
        (bounded_time_section_intervalIntegrable _ _ hle D hD K hDb ω)).symm
  change |(∫ ω in E, F (s + δ) ω (B (s + δ) ω) - F s ω (B (s + δ) ω) ∂P) -
    (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), D u ω) ∂P)| ≤ _
  rw [he]
  have hmean (u : ℝ) (hu : u ∈ Ioc (s : ℝ) (s + δ : ℝ≥0)) :
      |∫ ω in E, G u ω ∂P| ≤ (K : ℝ) * Real.sqrt δ * standardGaussianAbsMoment 1 := by
    have hgi : Integrable (G u) (P.restrict E) :=
      Integrable.of_bound (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (2 * (K : ℝ)) (Eventually.of_forall fun ω => by
          simpa only [Real.norm_eq_abs] using hGb u ω)
    have hxi : Integrable (fun ω => |B (s + δ) ω - B u.toNNReal ω|) (P.restrict E) :=
      ((hB.hasLaw_sub (s + δ) u.toNNReal).hasGaussianLaw.integrable.abs).restrict
    have hgap : |((s + δ : ℝ≥0) : ℝ) - (u.toNNReal : ℝ)| ≤ δ := by
      rw [Real.coe_toNNReal _ (le_trans s.coe_nonneg hu.1.le),
        abs_of_nonneg (sub_nonneg.mpr hu.2), NNReal.coe_add]
      linarith [hu.1]
    calc
      |∫ ω in E, G u ω ∂P| ≤ ∫ ω in E, |G u ω| ∂P := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P.restrict E) (G u)
      _ ≤ ∫ ω in E, (K : ℝ) * |B (s + δ) ω - B u.toNNReal ω| ∂P :=
        integral_mono hgi.abs (hxi.const_mul _) (fun ω => hF.drift_lipschitz _ _ _ _)
      _ = (K : ℝ) * ∫ ω in E, |B (s + δ) ω - B u.toNNReal ω| ∂P := integral_const_mul _ _
      _ ≤ (K : ℝ) * (Real.sqrt δ * standardGaussianAbsMoment 1) :=
        mul_le_mul_of_nonneg_left (brownian_expected_abs_increment_le hB _ _ _ hgap E) K.coe_nonneg
      _ = (K : ℝ) * Real.sqrt δ * standardGaussianAbsMoment 1 := by ring
  have hb := bounded_interval_integral_expectation_bound (P := P.restrict E) _ _ hle G hG
    (2 * (K : ℝ)) ((K : ℝ) * Real.sqrt δ * standardGaussianAbsMoment 1) hGb hmean
  simpa only [NNReal.coe_add, add_sub_cancel_left, mul_right_comm, mul_assoc] using hb

lemma smooth_field_second_mean_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (K : ℝ≥0) {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (s δ : ℝ≥0) (E : Set Ω)
    (u : ℝ) (hu : u ∈ Ioc (s : ℝ) (s + δ : ℝ≥0)) :
    |∫ ω in E, iteratedDeriv 2 (F s ω) (B s ω) -
      iteratedDeriv 2 (F u.toNNReal ω) (B u.toNNReal ω) ∂P| ≤
      (K : ℝ) * ((δ : ℝ) + Real.sqrt δ * standardGaussianAbsMoment 1) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let C (u : ℝ) (ω : Ω) := iteratedDeriv 2 (F s ω) (B s ω)
  let D (u : ℝ) (ω : Ω) := iteratedDeriv 2 (F u.toNNReal ω) (B u.toNNReal ω)
  let G (u : ℝ) (ω : Ω) := C u ω - D u ω
  have htime : Measurable (fun q : ℝ × Ω => (q.1.toNNReal, q.2)) := by fun_prop
  have hC : Measurable (Function.uncurry C) :=
    (hF.eval_measurable s 2 (by decide) (hm s)).comp measurable_snd
  have hD : Measurable (Function.uncurry D) := by
    change Measurable (fun q : ℝ × Ω =>
      iteratedDeriv 2 (F q.1.toNNReal q.2) (B q.1.toNNReal q.2))
    simpa only [Function.comp_def] using
      (hF.joint 2 (by decide)).comp (htime.prodMk (hBm.comp htime))
  have hG : Measurable (Function.uncurry G) := hC.sub hD
  have hCb (u ω) : |C u ω| ≤ K := hF.bound _ _ _ 2 (by decide)
  have hDb (u ω) : |D u ω| ≤ K := hF.bound _ _ _ 2 (by decide)
  have hGb (u ω) : |G u ω| ≤ 2 * (K : ℝ) :=
    (abs_sub _ _).trans (by linarith [hCb u ω, hDb u ω])
  have hgi : Integrable (G u) (P.restrict E) :=
    Integrable.of_bound (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (2 * (K : ℝ)) (Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hGb u ω)
  have hxi : Integrable (fun ω => |B u.toNNReal ω - B s ω|) (P.restrict E) :=
    ((hB.hasLaw_sub u.toNNReal s).hasGaussianLaw.integrable.abs).restrict
  have hgap : |(u.toNNReal : ℝ) - (s : ℝ)| ≤ δ := by
    rw [Real.coe_toNNReal _ (le_trans s.coe_nonneg hu.1.le), abs_of_nonneg (sub_nonneg.mpr hu.1.le)]
    have hh := hu.2
    simp only [NNReal.coe_add] at hh
    linarith
  have hpoint (ω) : |G u ω| ≤ (K : ℝ) * ((δ : ℝ) + |B u.toNNReal ω - B s ω|) := by
    calc
      |G u ω| = |D u ω - C u ω| := abs_sub_comm _ _
      _ ≤ (K : ℝ) * (|(u.toNNReal : ℝ) - (s : ℝ)| + |B u.toNNReal ω - B s ω|) :=
        hF.second_lipschitz s u.toNNReal ω _ _
      _ ≤ (K : ℝ) * ((δ : ℝ) + |B u.toNNReal ω - B s ω|) :=
        mul_le_mul_of_nonneg_left (add_le_add hgap le_rfl) K.coe_nonneg
  have hconst : (∫ _ω in E, (δ : ℝ) ∂P) ≤ δ := by
    calc
      (∫ _ω in E, (δ : ℝ) ∂P) ≤ ∫ _ω, (δ : ℝ) ∂P :=
        integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun _ => δ.coe_nonneg) (integrable_const _)
      _ = δ := by simp
  calc
    |∫ ω in E, G u ω ∂P| ≤ ∫ ω in E, |G u ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P.restrict E) (G u)
    _ ≤ ∫ ω in E, (K : ℝ) * ((δ : ℝ) + |B u.toNNReal ω - B s ω|) ∂P :=
      integral_mono hgi.abs (((integrable_const _).add hxi).const_mul _) hpoint
    _ = (K : ℝ) * ((∫ _ω in E, (δ : ℝ) ∂P) +
        ∫ ω in E, |B u.toNNReal ω - B s ω| ∂P) := by
      rw [integral_const_mul, integral_add (integrable_const _) hxi]
    _ ≤ (K : ℝ) * ((δ : ℝ) + Real.sqrt δ * standardGaussianAbsMoment 1) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hconst (brownian_expected_abs_increment_le hB _ _ _ hgap E)) K.coe_nonneg

lemma smooth_field_second_set_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (K : ℝ≥0) {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (s δ : ℝ≥0) (E : Set Ω) :
    |(δ : ℝ) * (∫ ω in E, iteratedDeriv 2 (F s ω) (B s ω) ∂P) -
      ∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0),
        iteratedDeriv 2 (F u.toNNReal ω) (B u.toNNReal ω)) ∂P| ≤
      (K : ℝ) * (δ : ℝ) * ((δ : ℝ) + Real.sqrt δ * standardGaussianAbsMoment 1) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let C (u : ℝ) (ω : Ω) := iteratedDeriv 2 (F s ω) (B s ω)
  let D (u : ℝ) (ω : Ω) := iteratedDeriv 2 (F u.toNNReal ω) (B u.toNNReal ω)
  let G (u : ℝ) (ω : Ω) := C u ω - D u ω
  have htime : Measurable (fun q : ℝ × Ω => (q.1.toNNReal, q.2)) := by fun_prop
  have hC : Measurable (Function.uncurry C) :=
    (hF.eval_measurable s 2 (by decide) (hm s)).comp measurable_snd
  have hD : Measurable (Function.uncurry D) := by
    change Measurable (fun q : ℝ × Ω =>
      iteratedDeriv 2 (F q.1.toNNReal q.2) (B q.1.toNNReal q.2))
    simpa only [Function.comp_def] using
      (hF.joint 2 (by decide)).comp (htime.prodMk (hBm.comp htime))
  have hG : Measurable (Function.uncurry G) := hC.sub hD
  have hCb (u ω) : |C u ω| ≤ K := hF.bound _ _ _ 2 (by decide)
  have hDb (u ω) : |D u ω| ≤ K := hF.bound _ _ _ 2 (by decide)
  have hGb (u ω) : |G u ω| ≤ 2 * (K : ℝ) :=
    (abs_sub _ _).trans (by linarith [hCb u ω, hDb u ω])
  have hle : (s : ℝ) ≤ (s + δ : ℝ≥0) := by
    simp only [NNReal.coe_add]; exact le_add_of_nonneg_right δ.coe_nonneg
  have hCI := bounded_interval_integral_integrable (P := P.restrict E) _ _ hle C hC K hCb
  have hDI := bounded_interval_integral_integrable (P := P.restrict E) _ _ hle D hD K hDb
  have he : (δ : ℝ) * (∫ ω in E, C 0 ω ∂P) -
      (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), D u ω) ∂P) =
      ∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), G u ω) ∂P := by
    have hconst : (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), C u ω) ∂P) =
        (δ : ℝ) * ∫ ω in E, C 0 ω ∂P := by
      simp only [C, intervalIntegral.integral_const, NNReal.coe_add,
        add_sub_cancel_left, smul_eq_mul, integral_const_mul]
    rw [← hconst, ← integral_sub hCI hDI]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω =>
      (intervalIntegral.integral_sub
        (bounded_time_section_intervalIntegrable _ _ hle C hC K hCb ω)
        (bounded_time_section_intervalIntegrable _ _ hle D hD K hDb ω)).symm
  change |(δ : ℝ) * (∫ ω in E, C 0 ω ∂P) -
    (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), D u ω) ∂P)| ≤ _
  rw [he]
  have hmean (u : ℝ) (hu : u ∈ Ioc (s : ℝ) (s + δ : ℝ≥0)) :
      |∫ ω in E, G u ω ∂P| ≤ (K : ℝ) * ((δ : ℝ) + Real.sqrt δ * standardGaussianAbsMoment 1) :=
    smooth_field_second_mean_error hB hm hBm K hF s δ E u hu
  have hb := bounded_interval_integral_expectation_bound (P := P.restrict E) _ _ hle G hG
    (2 * (K : ℝ)) ((K : ℝ) * ((δ : ℝ) + Real.sqrt δ * standardGaussianAbsMoment 1)) hGb hmean
  calc
    _ ≤ (K : ℝ) * ((δ : ℝ) + Real.sqrt δ * standardGaussianAbsMoment 1) *
        (((s + δ : ℝ≥0) : ℝ) - s) := hb
    _ = _ := by simp only [NNReal.coe_add]; ring

lemma SmoothTimeBrownianField.eval_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (t : ℝ≥0) (j : ℕ) (hj : j ≤ 2)
    {V : Ω → ℝ} (hV : Measurable V) :
    Integrable (fun ω => iteratedDeriv j (F t ω) (V ω)) P := by
  apply Integrable.of_bound (hF.eval_measurable t j hj hV).aestronglyMeasurable K
  exact Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using hF.bound t ω (V ω) j (by omega)

lemma SmoothTimeBrownianField.deriv_real_joint
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (j : ℕ) (hj : j ≤ 2) :
    Measurable (fun q : ℝ × Ω => iteratedDeriv j (F q.1.toNNReal q.2) (B q.1.toNNReal q.2)) := by
  have ht : Measurable (fun q : ℝ × Ω => (q.1.toNNReal, q.2)) := by fun_prop
  simpa only [Function.comp_def] using (hF.joint j hj).comp (ht.prodMk (hBm.comp ht))

lemma SmoothTimeBrownianField.drift_real_joint
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) :
    Measurable (fun q : ℝ × Ω => a q.1.toNNReal q.2 (B q.1.toNNReal q.2)) := by
  have ht : Measurable (fun q : ℝ × Ω => (q.1.toNNReal, q.2)) := by fun_prop
  exact hF.drift_joint.comp (ht.prodMk (hBm.comp ht))

lemma bounded_interval_integral_expectation_add
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (a b c : ℝ) (hab : a ≤ b) (G H : ℝ → Ω → ℝ)
    (hG : Measurable (Function.uncurry G)) (hH : Measurable (Function.uncurry H))
    (C D : ℝ) (hGb : ∀ u ω, |G u ω| ≤ C) (hHb : ∀ u ω, |H u ω| ≤ D) :
    (∫ ω, (∫ u in a..b, G u ω + c * H u ω) ∂P) =
      (∫ ω, (∫ u in a..b, G u ω) ∂P) + c * (∫ ω, (∫ u in a..b, H u ω) ∂P) := by
  have hGI := bounded_interval_integral_integrable a b hab G hG C hGb (P := P)
  have hHI := bounded_interval_integral_integrable a b hab H hH D hHb (P := P)
  calc
    _ = ∫ ω, ((∫ u in a..b, G u ω) + c * (∫ u in a..b, H u ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [intervalIntegral.integral_add
        (bounded_time_section_intervalIntegrable a b hab G hG C hGb ω)
        ((bounded_time_section_intervalIntegrable a b hab H hH D hHb ω).const_mul c),
        intervalIntegral.integral_const_mul]
    _ = _ := by rw [integral_add hGI (hHI.const_mul c), integral_const_mul]

lemma dynkinRate_tendsto_zero : Tendsto dynkinRate (𝓝 0) (𝓝 0) := by
  have hc : Continuous dynkinRate := by unfold dynkinRate; fun_prop
  simpa [ContinuousAt, dynkinRate] using hc.continuousAt (x := 0)

lemma abs_dynkin_algebra_bound (T A S I J eT eA eS δ : ℝ)
    (hT : |T - (1 / 2 : ℝ) * δ * S| ≤ eT)
    (hA : |A - I| ≤ eA) (hS : |δ * S - J| ≤ eS) :
    |(T + A) - (I + (1 / 2 : ℝ) * J)| ≤ eT + eA + (1 / 2 : ℝ) * eS := by
  have he : (T + A) - (I + (1 / 2 : ℝ) * J) =
      (T - (1 / 2 : ℝ) * δ * S) + (A - I) + (1 / 2 : ℝ) * (δ * S - J) := by ring
  rw [he]
  calc
    _ ≤ |T - (1 / 2 : ℝ) * δ * S| + |A - I| + |(1 / 2 : ℝ) * (δ * S - J)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |T - (1 / 2 : ℝ) * δ * S| + |A - I| + (1 / 2 : ℝ) * |δ * S - J| := by
      rw [abs_mul]; norm_num
    _ ≤ _ := add_le_add (add_le_add hT hA) (mul_le_mul_of_nonneg_left hS (by norm_num))

lemma smooth_field_one_step_error
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (K : ℝ≥0) {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (s δ : ℝ≥0) {E : Set Ω}
    (hE : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] E) :
    |(∫ ω in E, F (s + δ) ω (B (s + δ) ω) - F s ω (B s ω) ∂P) -
      (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), brownianFieldDrift B F a u ω) ∂P)| ≤
      (K : ℝ) * (δ : ℝ) * dynkinRate δ := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hI (v t : ℝ≥0) : Integrable (fun ω => F v ω (B t ω)) (P.restrict E) := by
    simpa only [iteratedDeriv_zero] using hF.eval_integrable v 0 (by decide) (hm t) (P := P.restrict E)
  have hsplit : (∫ ω in E, F (s + δ) ω (B (s + δ) ω) - F s ω (B s ω) ∂P) =
      (∫ ω in E, F s ω (B (s + δ) ω) - F s ω (B s ω) ∂P) +
      (∫ ω in E, F (s + δ) ω (B (s + δ) ω) - F s ω (B (s + δ) ω) ∂P) := by
    rw [integral_sub (hI _ _) (hI _ _), integral_sub (hI _ _) (hI _ _),
      integral_sub (hI _ _) (hI _ _)]
    ring
  have hle : (s : ℝ) ≤ (s + δ : ℝ≥0) := by
    simp only [NNReal.coe_add]; exact le_add_of_nonneg_right δ.coe_nonneg
  have hsplitD : (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), brownianFieldDrift B F a u ω) ∂P) =
      (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0), a u.toNNReal ω (B u.toNNReal ω)) ∂P) +
      (1 / 2 : ℝ) * (∫ ω in E, (∫ u in (s : ℝ)..(s + δ : ℝ≥0),
        iteratedDeriv 2 (F u.toNNReal ω) (B u.toNNReal ω)) ∂P) := by
    apply bounded_interval_integral_expectation_add _ _ _ hle _ _
      (hF.drift_real_joint hBm) (hF.deriv_real_joint hBm 2 (by decide)) (K : ℝ) (K : ℝ)
    · exact fun u ω => hF.drift_bound _ _ _
    · exact fun u ω => hF.bound _ _ _ 2 (by decide)
  rw [hsplit, hsplitD]
  have h := abs_dynkin_algebra_bound _ _ _ _ _ _ _ _ _
    (smooth_field_taylor_set_error hB hm K hF s δ hE)
    (smooth_field_time_set_error hB hm hBm K hF s δ E)
    (smooth_field_second_set_error hB hm hBm K hF s δ E)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold dynkinRate
  ring

 

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_OptionalStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Optional Stopping for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
lemma eq_of_uniform_small_increment
    (f : ℝ≥0 → ℝ) (rate : ℝ≥0 → ℝ) (C : ℝ)
    (hrate : Tendsto rate (𝓝 0) (𝓝 0))
    (hb : ∀ s δ, |f (s + δ) - f s| ≤ C * (δ : ℝ) * rate δ)
    (s t : ℝ≥0) (hst : s ≤ t) : f t = f s := by
  have mesh (n : ℕ) : |f t - f s| ≤ C * ((t : ℝ) - s) * rate ((t - s) / (n + 1)) := by
    let δ : ℝ≥0 := (t - s) / (n + 1)
    let u (i : ℕ) : ℝ≥0 := s + i * δ
    have hn : (n + 1 : ℝ≥0) ≠ 0 := by positivity
    have hlast : u (n + 1) = t := by
      dsimp only [u, δ]
      push_cast
      rw [mul_div_cancel₀ _ hn, add_tsub_cancel_of_le hst]
    have hstep (i : ℕ) : u (i + 1) = u i + δ := by
      dsimp [u]; push_cast; ring
    have htel : (∑ i ∈ Finset.range (n + 1), (f (u (i + 1)) - f (u i))) = f t - f s := by
      rw [Finset.sum_range_sub (fun i => f (u i))]
      simp only [hlast, u, Nat.cast_zero, zero_mul, add_zero]
    have hδ : ((n : ℝ) + 1) * (δ : ℝ) = (t : ℝ) - s := by
      dsimp only [δ]
      rw [NNReal.coe_div, NNReal.coe_sub hst]
      push_cast
      exact mul_div_cancel₀ _ (by positivity)
    calc
      |f t - f s| = |∑ i ∈ Finset.range (n + 1), (f (u (i + 1)) - f (u i))| := by rw [htel]
      _ ≤ ∑ i ∈ Finset.range (n + 1), |f (u (i + 1)) - f (u i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (n + 1), C * (δ : ℝ) * rate δ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [hstep]
        exact hb (u i) δ
      _ = C * ((t : ℝ) - s) * rate δ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        calc
          ((n : ℝ) + 1) * (C * (δ : ℝ) * rate δ) = C * (((n : ℝ) + 1) * (δ : ℝ)) * rate δ := by ring
          _ = _ := by rw [hδ]
  have hmesh : Tendsto (fun n : ℕ => (t - s) / (n + 1 : ℝ≥0)) atTop (𝓝 0) := by
    apply NNReal.tendsto_coe.mp
    simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_zero]
    apply tendsto_const_nhds.div_atTop
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hl : Tendsto (fun n : ℕ => C * ((t : ℝ) - s) * rate ((t - s) / (n + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using tendsto_const_nhds.mul (hrate.comp hmesh)
  have he : |f t - f s| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hl
    (Eventually.of_forall mesh)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp he)

lemma bounded_interval_integral_expectation_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (G : ℝ → Ω → ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hGb : ∀ u ω, |G u ω| ≤ C) :
    (∫ ω, (∫ u in a..c, G u ω) ∂P) - (∫ ω, (∫ u in a..b, G u ω) ∂P) =
      ∫ ω, (∫ u in b..c, G u ω) ∂P := by
  have hi₁ := bounded_interval_integral_integrable a b hab G hG C hGb (P := P)
  have hi₂ := bounded_interval_integral_integrable b c hbc G hG C hGb (P := P)
  have he : (∫ ω, (∫ u in a..c, G u ω) ∂P) =
      (∫ ω, (∫ u in a..b, G u ω) ∂P) + (∫ ω, (∫ u in b..c, G u ω) ∂P) := by
    rw [← integral_add hi₁ hi₂]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => (intervalIntegral.integral_add_adjacent_intervals
      (bounded_time_section_intervalIntegrable a b hab G hG C hGb ω)
      (bounded_time_section_intervalIntegrable b c hbc G hG C hGb ω)).symm
  rw [he, add_sub_cancel_left]

lemma SmoothTimeBrownianField.generator_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) :
    Measurable (Function.uncurry (brownianFieldDrift B F a)) := by
  change Measurable (fun q : ℝ × Ω => a q.1.toNNReal q.2 (B q.1.toNNReal q.2) +
    (1 / 2 : ℝ) * iteratedDeriv 2 (F q.1.toNNReal q.2) (B q.1.toNNReal q.2))
  exact (hF.drift_real_joint hBm).add (measurable_const.mul (hF.deriv_real_joint hBm 2 (by decide)))

lemma SmoothTimeBrownianField.generator_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (u : ℝ) (ω : Ω) :
    |brownianFieldDrift B F a u ω| ≤ 2 * (K : ℝ) := by
  unfold brownianFieldDrift
  have hb := hF.bound u.toNNReal ω (B u.toNNReal ω) 2 (by decide)
  have ha := hF.drift_bound u.toNNReal ω (B u.toNNReal ω)
  have ht := abs_add_le (a u.toNNReal ω (B u.toNNReal ω))
    ((1 / 2 : ℝ) * iteratedDeriv 2 (F u.toNNReal ω) (B u.toNNReal ω))
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
  linarith [K.coe_nonneg]

 

theorem brownian_time_field_dynkin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (K : ℝ≥0) (F a : ℝ≥0 → Ω → ℝ → ℝ)
    (hF : SmoothTimeBrownianField B hm K F a)
    (s t : ℝ≥0) (hst : s ≤ t) {E : Set Ω}
    (hE : MeasurableSet[Filtration.natural B
      (fun t => (hm t).stronglyMeasurable) s] E) :
    (∫ ω in E, F t ω (B t ω) - F s ω (B s ω) ∂P) =
      ∫ ω in E, (∫ u in (s : ℝ)..(t : ℝ), brownianFieldDrift B F a u ω) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let c (r : ℝ≥0) := ∫ ω in E, (∫ u in (s : ℝ)..(s + r : ℝ≥0), brownianFieldDrift B F a u ω) ∂P
  let v (r : ℝ≥0) := ∫ ω in E, F r ω (B r ω) ∂P
  let f (r : ℝ≥0) := v (s + r) - c r
  have hI (r : ℝ≥0) : Integrable (fun ω => F r ω (B r ω)) (P.restrict E) := by
    simpa only [iteratedDeriv_zero] using hF.eval_integrable r 0 (by decide) (hm r) (P := P.restrict E)
  have hinc (r δ : ℝ≥0) : |f (r + δ) - f r| ≤ (K : ℝ) * (δ : ℝ) * dynkinRate δ := by
    have hsr : s ≤ s + r := le_add_of_nonneg_right (zero_le)
    have hE' : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) (s + r)] E :=
      (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hsr E hE
    have h := smooth_field_one_step_error hB hm hBm K hF (s + r) δ hE'
    have hcomp : c (r + δ) - c r =
        ∫ ω in E, (∫ u in (s + r : ℝ≥0)..((s + r) + δ : ℝ≥0), brownianFieldDrift B F a u ω) ∂P := by
      dsimp only [c]
      rw [← add_assoc]
      apply bounded_interval_integral_expectation_sub _ _ _
        (by exact_mod_cast hsr) (by simp only [NNReal.coe_add]; linarith [δ.coe_nonneg]) _
        (hF.generator_measurable hBm) (2 * (K : ℝ)) (hF.generator_bound)
    have hv : v ((s + r) + δ) - v (s + r) =
        ∫ ω in E, F ((s + r) + δ) ω (B ((s + r) + δ) ω) - F (s + r) ω (B (s + r) ω) ∂P :=
      (integral_sub (hI _) (hI _)).symm
    have he : f (r + δ) - f r =
        (∫ ω in E, F ((s + r) + δ) ω (B ((s + r) + δ) ω) - F (s + r) ω (B (s + r) ω) ∂P) -
        (∫ ω in E, (∫ u in (s + r : ℝ≥0)..((s + r) + δ : ℝ≥0), brownianFieldDrift B F a u ω) ∂P) := by
      dsimp only [f]
      rw [← add_assoc]
      linarith
    rw [he]
    exact h
  have heq := eq_of_uniform_small_increment f dynkinRate K dynkinRate_tendsto_zero hinc 0 (t - s) (zero_le)
  have hc0 : c 0 = 0 := by simp [c]
  have hst' : s + (t - s) = t := add_tsub_cancel_of_le hst
  change v (s + (t - s)) - c (t - s) = v (s + 0) - c 0 at heq
  rw [hst', add_zero, hc0, sub_zero] at heq
  have hc : c (t - s) = ∫ ω in E, (∫ u in (s : ℝ)..(t : ℝ), brownianFieldDrift B F a u ω) ∂P := by
    dsimp only [c]
    rw [hst']
  rw [integral_sub (hI _) (hI _)]
  change v t - v s = _
  linarith


lemma stopGridIndex_le (n k : ℕ) (t : ℝ≥0) :
    stopGridIndex n t ≤ k ↔ t ≤ stopGridTime n k := by
  have hd : 0 < (n : ℝ≥0) + 1 := by positivity
  simp only [stopGridIndex, Nat.ceil_le, stopGridTime, le_div_iff₀ hd, mul_comm]

lemma stopGrid_bounds (n : ℕ) (t : ℝ≥0) :
    t ≤ stopGrid n t ∧ stopGrid n t ≤ t + 1 / ((n : ℝ≥0) + 1) := by
  have hd : 0 < (n : ℝ≥0) + 1 := by positivity
  constructor
  · exact (stopGridIndex_le n _ t).mp le_rfl
  · dsimp [stopGrid, stopGridTime, stopGridIndex]
    rw [div_le_iff₀ hd]
    calc
      _ ≤ ((n : ℝ≥0) + 1) * t + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      _ = (t + 1 / ((n : ℝ≥0) + 1)) * ((n : ℝ≥0) + 1) := by
        conv_rhs => rw [add_mul, div_mul_cancel₀ _ hd.ne']
        ac_rfl

lemma stopGrid_tendsto (t : ℝ≥0) : Tendsto (fun n => stopGrid n t) atTop (𝓝 t) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))))
  · exact fun n => (stopGrid_bounds n t).1
  · intro n
    simpa only [one_div] using (stopGrid_bounds n t).2

lemma measurable_discrete_eval {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Measurable (f k))
    {j : Ω → ℕ} (hj : Measurable j) : Measurable (fun ω => f (j ω) ω) := by
  exact (measurable_from_prod_countable_right (f := fun p : ℕ × Ω => f p.1 p.2) hf).comp (hj.prodMk measurable_id)

lemma stopping_time_measurable_nnreal {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) : Measurable τ := by
  simpa only [WithTop.untopD_coe] using hτ.measurable'.untopD 0

lemma stopGridIndex_measurable {Ω : Type*} [MeasurableSpace Ω]
    {τ : Ω → ℝ≥0} (hτ : Measurable τ) (n : ℕ) :
    Measurable (fun ω => stopGridIndex n (τ ω)) := by
  exact (measurable_const.mul hτ).nat_ceil

lemma SmoothTimeBrownianField.time_increment_all
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (s t : ℝ≥0) (ω : Ω) (x : ℝ) :
    F t ω x - F s ω x = ∫ u in (s : ℝ)..(t : ℝ), a u.toNNReal ω x := by
  rcases le_total s t with h | h
  · exact hF.time_increment s t h ω x
  · rw [intervalIntegral.integral_symm, ← hF.time_increment t s h ω x]
    ring

lemma SmoothTimeBrownianField.time_dist_le
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (s t : ℝ≥0) (ω : Ω) (x : ℝ) :
    dist (F t ω x) (F s ω x) ≤ (K : ℝ) * dist t s := by
  rw [Real.dist_eq, hF.time_increment_all]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (s : ℝ)) (b := (t : ℝ))
    (f := fun u => a u.toNNReal ω x) (C := (K : ℝ))
    (fun u hu => by simpa only [Real.norm_eq_abs] using hF.drift_bound u.toNNReal ω x)
  change |(∫ u in (s : ℝ)..(t : ℝ), a u.toNNReal ω x)| ≤ (K : ℝ) * |(t : ℝ) - s|
  simpa only [Real.norm_eq_abs] using hb

lemma SmoothTimeBrownianField.space_lipschitz
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (t : ℝ≥0) (ω : Ω) :
    LipschitzWith K (F t ω) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((hF.smooth t ω).differentiable (by norm_num))
  intro x
  change ‖deriv (F t ω) x‖ ≤ (K : ℝ)
  simpa only [iteratedDeriv_one, Real.norm_eq_abs] using hF.bound t ω x 1 (by decide)

lemma SmoothTimeBrownianField.path_continuous
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    Continuous (fun t => F t ω (B t ω)) := by
  have hpair : LipschitzWith (2 * K) (fun p : ℝ≥0 × ℝ => F p.1 ω p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    calc
      dist (F p.1 ω p.2) (F q.1 ω q.2) ≤
        dist (F p.1 ω p.2) (F q.1 ω p.2) + dist (F q.1 ω p.2) (F q.1 ω q.2) := dist_triangle _ _ _
      _ ≤ (K : ℝ) * dist p.1 q.1 + (K : ℝ) * dist p.2 q.2 :=
        add_le_add (hF.time_dist_le q.1 p.1 ω p.2) ((hF.space_lipschitz q.1 ω).dist_le_mul p.2 q.2)
      _ ≤ (K : ℝ) * dist p q + (K : ℝ) * dist p q := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
      _ = _ := by change _ = (2 * (K : ℝ)) * dist p q; ring
  exact hpair.continuous.comp (continuous_id.prodMk (hc ω))

lemma cumulative_integral_measurable
    {Ω : Type*} [MeasurableSpace Ω] (G : ℝ → Ω → ℝ)
    (hG : Measurable (Function.uncurry G)) :
    Measurable (fun q : ℝ≥0 × Ω => ∫ u in (0 : ℝ)..(q.1 : ℝ), G u q.2) := by
  have hf : Measurable (fun q : (ℝ≥0 × Ω) × ℝ => G q.2 q.1.2) :=
    hG.comp (measurable_snd.prodMk measurable_fst.snd)
  let A : Set ((ℝ≥0 × Ω) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ (q.1.1 : ℝ)}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp measurable_fst.fst))
  have hm := ((hf.indicator hA).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  rw [intervalIntegral.integral_of_le q.1.coe_nonneg, ← integral_indicator measurableSet_Ioc]
  rfl

lemma SmoothTimeBrownianField.compensated_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (t : ℝ≥0) :
    Integrable (brownianFieldCompensated B F a t) P := by
  have hi : Integrable (fun ω => F t ω (B t ω)) P :=
    hF.eval_integrable t 0 (by decide) (hm t)
  exact hi.sub (bounded_interval_integral_integrable 0 t t.coe_nonneg _
    (hF.generator_measurable hBm) (2 * (K : ℝ)) hF.generator_bound)

lemma SmoothTimeBrownianField.compensated_past_integral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a) (s t : ℝ≥0) (hst : s ≤ t)
    {E : Set Ω} (hE : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] E) :
    (∫ ω in E, brownianFieldCompensated B F a t ω - brownianFieldCompensated B F a s ω ∂P) = 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hGm := hF.generator_measurable hBm
  have hGi (a b : ℝ) (h : a ≤ b) (ω : Ω) :=
    bounded_time_section_intervalIntegrable a b h _ hGm (2 * (K : ℝ)) hF.generator_bound ω
  have hp (ω : Ω) : brownianFieldCompensated B F a t ω - brownianFieldCompensated B F a s ω =
      (F t ω (B t ω) - F s ω (B s ω)) - ∫ u in (s : ℝ)..(t : ℝ), brownianFieldDrift B F a u ω := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hGi 0 s s.coe_nonneg ω) (hGi s t hst ω)
    dsimp only [brownianFieldCompensated]
    linarith
  simp_rw [hp]
  have hf : Integrable (fun ω => F t ω (B t ω) - F s ω (B s ω)) (P.restrict E) :=
    (hF.eval_integrable t 0 (by decide) (hm t)).sub (hF.eval_integrable s 0 (by decide) (hm s))
  rw [integral_sub hf (bounded_interval_integral_integrable s t hst _ hGm (2 * (K : ℝ)) hF.generator_bound),
    brownian_time_field_dynkin hB hm hBm K F a hF s t hst hE, sub_self]

lemma sum_stopped_increments (f : ℕ → ℝ) (k N : ℕ) (hk : k ≤ N) :
    (∑ j ∈ Finset.range N, if j < k then f (j + 1) - f j else 0) = f k - f 0 := by
  have hs : (∑ j ∈ Finset.range k, if j < k then f (j + 1) - f j else 0) =
      ∑ j ∈ Finset.range N, if j < k then f (j + 1) - f j else 0 := by
    apply Finset.sum_subset (Finset.range_mono hk)
    intro j hj hjk
    exact ite_eq_right (fun hh => hjk (Finset.mem_range.mpr hh))
  rw [← hs]
  calc
    _ = ∑ j ∈ Finset.range k, (f (j + 1) - f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact ite_eq_left (Finset.mem_range.mp hj)
    _ = _ := Finset.sum_range_sub f k

 

lemma finite_grid_stopped_integral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (ℱ : Filtration ℕ mΩ) (C : ℕ → Ω → ℝ)
    (hi : ∀ j, Integrable (C j) P) (σ : Ω → ℕ) (N : ℕ)
    (hb : ∀ ω, σ ω ≤ N)
    (hE : ∀ j, MeasurableSet[ℱ j] {ω | j < σ ω})
    (hzero : ∀ j (E : Set Ω), MeasurableSet[ℱ j] E →
      (∫ ω in E, C (j + 1) ω - C j ω ∂P) = 0) :
    (∫ ω, C (σ ω) ω ∂P) = ∫ ω, C 0 ω ∂P := by
  classical
  let D (j : ℕ) : Ω → ℝ := {ω | j < σ ω}.indicator (fun ω => C (j + 1) ω - C j ω)
  have hD (j : ℕ) : Integrable (D j) P :=
    ((hi (j + 1)).sub (hi j)).indicator (ℱ.le j _ (hE j))
  have hDi (j : ℕ) : (∫ ω, D j ω ∂P) = 0 := by
    change (∫ ω, {ω | j < σ ω}.indicator (fun ω => C (j + 1) ω - C j ω) ω ∂P) = 0
    rw [integral_indicator (ℱ.le j _ (hE j))]
    exact hzero j _ (hE j)
  have hpoint (ω : Ω) : C (σ ω) ω = C 0 ω + ∑ j ∈ Finset.range N, D j ω := by
    have hh := sum_stopped_increments (fun j => C j ω) (σ ω) N (hb ω)
    have hsum : (∑ j ∈ Finset.range N, D j ω) =
        ∑ j ∈ Finset.range N, if j < σ ω then C (j + 1) ω - C j ω else 0 := by
      apply Finset.sum_congr rfl
      intro index _
      by_cases hindex : index < σ ω <;> simp [D, hindex]
    rw [hsum, hh]
    ring
  simp_rw [hpoint]
  rw [integral_add (hi 0) (integrable_finsetSum _ (fun j hj => hD j)), integral_finsetSum]
  · simp only [hDi, Finset.sum_const_zero, add_zero]
  · intro j hj; exact hD j

lemma brownian_compensated_grid_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) (n : ℕ) :
    (∫ ω, brownianFieldCompensated B F a (stopGrid n (τ ω)) ω ∂P) =
      ∫ ω, F 0 ω (B 0 ω) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let ℱn := gridFiltration ℱ n
  have hbound (ω : Ω) : stopGridIndex n (τ ω) ≤ stopGridIndex n T := by
    apply (stopGridIndex_le n _ _).mpr
    exact (hb ω).trans (stopGrid_bounds n T).1
  have hE (j : ℕ) : MeasurableSet[ℱn j] {ω | j < stopGridIndex n (τ ω)} := by
    have hle : MeasurableSet[ℱ (stopGridTime n j)] {ω | τ ω ≤ stopGridTime n j} := by
      simpa only [WithTop.coe_le_coe] using hτ (stopGridTime n j)
    have he : {ω | j < stopGridIndex n (τ ω)} = {ω | τ ω ≤ stopGridTime n j}ᶜ := by
      ext ω
      simp only [mem_compl_iff, mem_ofPred_eq, ← stopGridIndex_le, not_le]
    rw [he]
    exact hle.compl
  have he := finite_grid_stopped_integral_eq ℱn
    (fun j => brownianFieldCompensated B F a (stopGridTime n j))
    (fun j => hF.compensated_integrable hBm _)
    (fun ω => stopGridIndex n (τ ω)) (stopGridIndex n T) hbound hE
    (fun j E hE => hF.compensated_past_integral_zero hB hm hBm _ _
      (monotone_stopGridTime n (Nat.le_succ j)) hE)
  simpa only [stopGrid, stopGridTime, Nat.cast_zero, zero_div,
    brownianFieldCompensated, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero] using he

lemma bounded_cumulative_at_grid
    {Ω : Type*} [MeasurableSpace Ω] (G : ℝ → Ω → ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ u ω, |G u ω| ≤ C) (τ : Ω → ℝ≥0)
    (hz : ∀ ω u, 0 ≤ u → u < (τ ω : ℝ) → G u ω = 0) (n : ℕ) (ω : Ω) :
    |∫ u in (0 : ℝ)..(stopGrid n (τ ω) : ℝ), G u ω| ≤ C * (1 / ((n : ℝ) + 1)) := by
  have h0 : (∫ u in (0 : ℝ)..(τ ω : ℝ), G u ω) = 0 := by
    calc
      _ = ∫ u in (0 : ℝ)..(τ ω : ℝ), (0 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le (τ ω).coe_nonneg (fun u hu => hz ω u hu.1.le hu.2)
      _ = _ := by simp
  have hle : (τ ω : ℝ) ≤ stopGrid n (τ ω) := (stopGrid_bounds n (τ ω)).1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (bounded_time_section_intervalIntegrable 0 (τ ω) (τ ω).coe_nonneg G hG C hb ω)
    (bounded_time_section_intervalIntegrable (τ ω) (stopGrid n (τ ω)) hle G hG C hb ω)
  rw [h0, zero_add] at hsplit
  rw [← hsplit]
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (τ ω : ℝ)) (b := (stopGrid n (τ ω) : ℝ)) (C := C) (f := fun u => G u ω)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hb u ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] at hbnd
  refine hbnd.trans (mul_le_mul_of_nonneg_left ?_ hC)
  have hupper := (stopGrid_bounds n (τ ω)).2
  have hu : (stopGrid n (τ ω) : ℝ) ≤ (τ ω : ℝ) + 1 / ((n : ℝ) + 1) := by exact_mod_cast hupper
  linarith

 

theorem brownian_time_field_optional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (K : ℝ≥0) (F a : ℝ≥0 → Ω → ℝ → ℝ)
    (hF : SmoothTimeBrownianField B hm K F a)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hzero : ∀ ω u, 0 ≤ u → u < (τ ω : ℝ) → brownianFieldDrift B F a u ω = 0) :
    (∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P) = (∫ ω, F 0 ω (B 0 ω) ∂P) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hτm := stopping_time_measurable_nnreal hτ
  let V (n : ℕ) (ω : Ω) := F (stopGrid n (τ ω)) ω (B (stopGrid n (τ ω)) ω)
  let H (n : ℕ) (ω : Ω) := ∫ u in (0 : ℝ)..(stopGrid n (τ ω) : ℝ), brownianFieldDrift B F a u ω
  have hVm (n : ℕ) : Measurable (V n) :=
    measurable_discrete_eval (fun k ω => F (stopGridTime n k) ω (B (stopGridTime n k) ω))
      (fun k => hF.eval_measurable _ 0 (by decide) (hm _)) (stopGridIndex_measurable hτm n)
  have hVb (n : ℕ) (ω : Ω) : |V n ω| ≤ (K : ℝ) :=
    hF.bound _ ω _ 0 (by decide)
  have hVi (n : ℕ) : Integrable (V n) P :=
    Integrable.of_bound (hVm n).aestronglyMeasurable (K : ℝ)
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hVb n ω)
  have hGm := hF.generator_measurable hBm
  have hHjoint := cumulative_integral_measurable _ hGm
  have hHm (n : ℕ) : Measurable (H n) :=
    measurable_discrete_eval (fun k ω => ∫ u in (0 : ℝ)..(stopGridTime n k : ℝ), brownianFieldDrift B F a u ω)
      (fun k => hHjoint.comp measurable_prodMk_left) (stopGridIndex_measurable hτm n)
  have hHb (n : ℕ) (ω : Ω) : |H n ω| ≤ (2 * (K : ℝ)) * (1 / ((n : ℝ) + 1)) :=
    bounded_cumulative_at_grid _ hGm (2 * (K : ℝ)) (by positivity) hF.generator_bound τ hzero n ω
  have hHi (n : ℕ) : Integrable (H n) P :=
    Integrable.of_bound (hHm n).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hHb n ω)
  have hmean (n : ℕ) : (∫ ω, V n ω ∂P) - (∫ ω, F 0 ω (B 0 ω) ∂P) = ∫ ω, H n ω ∂P := by
    have hh := brownian_compensated_grid_integral hB hm hBm hF τ hτ T hb n
    change (∫ ω, V n ω - H n ω ∂P) = _ at hh
    rw [integral_sub (hVi n) (hHi n)] at hh
    linarith
  have herror (n : ℕ) : dist (∫ ω, V n ω ∂P) (∫ ω, F 0 ω (B 0 ω) ∂P) ≤
      (2 * (K : ℝ)) * (1 / ((n : ℝ) + 1)) := by
    rw [Real.dist_eq, hmean]
    have hh := norm_integral_le_of_norm_le_const (μ := P) (Eventually.of_forall fun ω =>
      show ‖H n ω‖ ≤ (2 * (K : ℝ)) * (1 / ((n : ℝ) + 1)) from by
        simpa only [Real.norm_eq_abs] using hHb n ω)
    simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hh
  have hlim : Tendsto (fun n => ∫ ω, V n ω ∂P) atTop (𝓝 (∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (K : ℝ))
      (fun n => (hVm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hVb n ω)
    exact Eventually.of_forall fun ω => (hF.path_continuous hBc ω).continuousAt.tendsto.comp (stopGrid_tendsto (τ ω))
  have hlim0 : Tendsto (fun n => ∫ ω, V n ω ∂P) atTop (𝓝 (∫ ω, F 0 ω (B 0 ω) ∂P)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) herror
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (K : ℝ))
  exact tendsto_nhds_unique hlim hlim0

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ClippedCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Clipped Coordinates for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma spatialPartial_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialPartial φ n) := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

lemma spatialPartial_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E × ℝ → ℝ) (hφ : HasCompactSupport φ) (n : ℕ) :
    HasCompactSupport (spatialPartial φ n) := by
  induction n with
  | zero => exact hφ
  | succ n ih =>
    exact (ih.fderiv ℝ).comp_left (g := fun D : (E × ℝ) →L[ℝ] ℝ => D (0, 1)) (by simp)

lemma spatialPartial_eq_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (n : ℕ) (q : E) (x : ℝ) :
    spatialPartial φ n (q, x) = iteratedDeriv n (fun y => φ (q, y)) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hd : HasDerivAt (fun y => spatialPartial φ n (q, y))
        (fderiv ℝ (spatialPartial φ n) (q, x) (0, 1)) x := by
      exact (((spatialPartial_smooth φ hφ n).differentiable (by simp)) (q, x)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_const x q).prodMk (hasDerivAt_id x))
    simpa only [spatialPartial, iteratedDeriv_succ, ← funext ih] using hd.deriv.symm

lemma compact_smooth_bounded_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : E → F) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∃ C : ℝ≥0, (∀ p, ‖φ p‖ ≤ C) ∧ LipschitzWith C φ := by
  obtain ⟨A, hA⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨D, hD⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hφc.fderiv ℝ)
  let C := Real.toNNReal (max A D)
  have hAC : A ≤ (C : ℝ) := (le_max_left _ _).trans (Real.le_coe_toNNReal _)
  have hDC : D ≤ (C : ℝ) := (le_max_right _ _).trans (Real.le_coe_toNNReal _)
  refine ⟨C, fun p => (hA p).trans hAC, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable (by simp))
  intro p
  exact_mod_cast (hD p).trans hDC

 

theorem compact_state_smooth_brownian_field
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (Q V : ℝ → Ω → E) (L : ℝ≥0)
    (hQm : Measurable (fun p : ℝ × Ω => Q p.1 p.2))
    (hQa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t : ℝ≥0 => Q t))
    (hQl : ∀ ω, LipschitzWith L (fun t => Q t ω))
    (hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2))
    (hVb : ∀ t ω, ‖V t ω‖ ≤ L)
    (hQd : ∀ t ω, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω) (V t ω) (Ici 0) t)
    (φ : E × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∃ K : ℝ≥0, SmoothTimeBrownianField B hm K
      (fun t ω x => φ (Q t ω, x))
      (fun t ω x => fderiv ℝ φ (Q t ω, x) (V t ω, 0)) := by

  classical
  have hr (j : ℕ) := compact_smooth_bounded_lipschitz (spatialPartial φ j)
    (spatialPartial_smooth φ hφ j) (spatialPartial_compact φ hφc j)
  choose C hCb hCl using hr
  let C₀ : ℝ≥0 := ∑ j ∈ Finset.range 4, C j
  have hC (j : ℕ) (hj : j ≤ 3) : C j ≤ C₀ :=
    Finset.single_le_sum (fun i _ => (zero_le : (0 : ℝ≥0) ≤ C i)) (Finset.mem_range.mpr (by omega))
  have hCb' (j : ℕ) (hj : j ≤ 3) (p : E × ℝ) : |spatialPartial φ j p| ≤ C₀ := by
    have hh := (hCb j p).trans (show (C j : ℝ) ≤ C₀ by exact_mod_cast hC j hj)
    simpa only [Real.norm_eq_abs] using hh
  have hC2 : LipschitzWith C₀ (spatialPartial φ 2) := (hCl 2).weaken (hC 2 (by decide))
  obtain ⟨D, hDb, hDl⟩ := compact_smooth_bounded_lipschitz (fderiv ℝ φ)
    (hφ.fderiv_right (by simp)) (hφc.fderiv ℝ)
  let K : ℝ≥0 := (C₀ + D) * (L + 1)
  have hKC : (C₀ : ℝ) ≤ (K : ℝ) := by
    change (C₀ : ℝ) ≤ ((C₀ : ℝ) + D) * ((L : ℝ) + 1)
    nlinarith [C₀.coe_nonneg, D.coe_nonneg, L.coe_nonneg]
  have hKDL : (D : ℝ) * L ≤ (K : ℝ) := by
    change (D : ℝ) * L ≤ ((C₀ : ℝ) + D) * ((L : ℝ) + 1)
    nlinarith [C₀.coe_nonneg, D.coe_nonneg, L.coe_nonneg]
  have hKCL : (C₀ : ℝ) * ((L : ℝ) + 1) ≤ (K : ℝ) := by
    change (C₀ : ℝ) * ((L : ℝ) + 1) ≤ ((C₀ : ℝ) + D) * ((L : ℝ) + 1)
    nlinarith [C₀.coe_nonneg, D.coe_nonneg, L.coe_nonneg]
  have hQn : Measurable (fun p : ℝ≥0 × Ω => Q p.1 p.2) :=
    hQm.comp ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hVn : Measurable (fun p : ℝ≥0 × Ω => V p.1 p.2) :=
    hVm.comp ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have happ : Continuous (fun p : (E × ℝ) × (E × ℝ) => fderiv ℝ φ p.1 p.2) :=
    ((hφ.continuous_fderiv (by simp)).comp continuous_fst).clm_apply continuous_snd
  have hameas : Measurable (fun p : (ℝ≥0 × Ω) × ℝ => fderiv ℝ φ (Q p.1.1 p.1.2, p.2) (V p.1.1 p.1.2, 0)) :=
    happ.measurable.comp (((hQn.comp measurable_fst).prodMk measurable_snd).prodMk
      ((hVn.comp measurable_fst).prodMk measurable_const))
  have habound (t : ℝ≥0) (ω : Ω) (x : ℝ) :
      |fderiv ℝ φ (Q t ω, x) (V t ω, 0)| ≤ K := by
    calc
      _ = ‖fderiv ℝ φ (Q t ω, x) (V t ω, 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ φ (Q t ω, x)‖ * ‖(V t ω, (0 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ φ (Q t ω, x)‖ * ‖V t ω‖ := by simp
      _ ≤ (D : ℝ) * L := mul_le_mul (hDb _) (hVb t ω) (norm_nonneg _) D.coe_nonneg
      _ ≤ K := hKDL
  have haLip (t : ℝ≥0) (ω : Ω) (x y : ℝ) :
      |fderiv ℝ φ (Q t ω, x) (V t ω, 0) - fderiv ℝ φ (Q t ω, y) (V t ω, 0)| ≤
        (K : ℝ) * |x - y| := by
    have hd : ‖fderiv ℝ φ (Q t ω, x) - fderiv ℝ φ (Q t ω, y)‖ ≤ (D : ℝ) * |x - y| := by
      simpa [dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using hDl.dist_le_mul (Q t ω, x) (Q t ω, y)
    calc
      _ = ‖(fderiv ℝ φ (Q t ω, x) - fderiv ℝ φ (Q t ω, y)) (V t ω, 0)‖ := by
        rw [sub_apply, Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ φ (Q t ω, x) - fderiv ℝ φ (Q t ω, y)‖ * ‖(V t ω, (0 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ φ (Q t ω, x) - fderiv ℝ φ (Q t ω, y)‖ * ‖V t ω‖ := by simp
      _ ≤ ((D : ℝ) * |x - y|) * L := mul_le_mul hd (hVb t ω) (norm_nonneg _) (by positivity)
      _ = ((D : ℝ) * L) * |x - y| := by ring
      _ ≤ (K : ℝ) * |x - y| := mul_le_mul_of_nonneg_right hKDL (abs_nonneg _)
  refine ⟨K, ⟨?_, ?_, ?_, hameas, ?_, habound, haLip, ?_, ?_⟩⟩
  · intro t ω
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => φ (Q t ω, x)) :=
      hφ.comp (contDiff_const.prodMk contDiff_id)
    exact hc.of_le (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  · intro t j hj
    simp_rw [← spatialPartial_eq_iteratedDeriv φ hφ]
    exact (spatialPartial_smooth φ hφ j).continuous.measurable.comp
      (((hQa t).comp measurable_fst).prodMk measurable_snd)
  · intro j hj
    simp_rw [← spatialPartial_eq_iteratedDeriv φ hφ]
    exact (spatialPartial_smooth φ hφ j).continuous.measurable.comp
      ((hQn.comp measurable_fst).prodMk measurable_snd)
  · intro t ω x j hj
    rw [← spatialPartial_eq_iteratedDeriv φ hφ]
    exact (hCb' j hj _).trans hKC
  · intro s t ω x y
    rw [← spatialPartial_eq_iteratedDeriv φ hφ, ← spatialPartial_eq_iteratedDeriv φ hφ]
    have hQdist := (hQl ω).dist_le_mul (t : ℝ) (s : ℝ)
    rw [Real.dist_eq] at hQdist
    calc
      _ = dist (spatialPartial φ 2 (Q t ω, x)) (spatialPartial φ 2 (Q s ω, y)) := (Real.dist_eq _ _).symm
      _ ≤ (C₀ : ℝ) * dist (Q t ω, x) (Q s ω, y) := hC2.dist_le_mul _ _
      _ ≤ (C₀ : ℝ) * (dist (Q t ω) (Q s ω) + |x - y|) := by
        apply mul_le_mul_of_nonneg_left _ C₀.coe_nonneg
        rw [Prod.dist_eq, Real.dist_eq]
        exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left dist_nonneg)
      _ ≤ (C₀ : ℝ) * ((L : ℝ) * |(t : ℝ) - s| + |x - y|) :=
        mul_le_mul_of_nonneg_left (show dist (Q (t : ℝ) ω) (Q (s : ℝ) ω) + |x - y| ≤
          (L : ℝ) * |(t : ℝ) - s| + |x - y| by linarith) C₀.coe_nonneg
      _ ≤ ((C₀ : ℝ) * ((L : ℝ) + 1)) * (|(t : ℝ) - s| + |x - y|) := by
        nlinarith [mul_nonneg C₀.coe_nonneg (abs_nonneg ((t : ℝ) - s)),
          mul_nonneg (mul_nonneg C₀.coe_nonneg L.coe_nonneg) (abs_nonneg (x - y))]
      _ ≤ (K : ℝ) * (|(t : ℝ) - s| + |x - y|) :=
        mul_le_mul_of_nonneg_right hKCL (by positivity)
  · intro s t hst ω x
    have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun u : ℝ => φ (Q u ω, x))
      (f' := fun u : ℝ => fderiv ℝ φ (Q u.toNNReal ω, x) (V u.toNNReal ω, 0)) hst'
    · exact (hφ.continuous.comp ((hQl ω).continuous.prodMk continuous_const)).continuousOn
    · intro u hu
      have hu0 : 0 < u := lt_of_le_of_lt s.coe_nonneg hu.1
      have hd := (hQd u ω hu0.le).hasDerivAt (Ici_mem_nhds hu0)
      have hpair := hd.prodMk (hasDerivAt_const u x)
      have hc := ((hφ.differentiable (by simp)) (Q u ω, x)).hasFDerivAt.comp_hasDerivAt u hpair
      simpa only [Function.comp_def, Real.coe_toNNReal _ hu0.le] using hc
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst']
      have hmA : Measurable (fun u : ℝ => fderiv ℝ φ (Q u.toNNReal ω, x) (V u.toNNReal ω, 0)) :=
        hameas.comp ((continuous_real_toNNReal.measurable.prodMk measurable_const).prodMk measurable_const)
      apply Integrable.of_bound hmA.aestronglyMeasurable (K : ℝ)
      exact Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using habound u.toNNReal ω x

lemma greenLogDensity_contDiff (κ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => p.1.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst.fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => p.1.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst.fst
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℂ × ℝ) × ℝ => greenLogNormSq κ p.1 p.2) := by
    exact ((hre.sub (contDiff_const.mul contDiff_snd)).pow 2).add
      ((contDiff_const.mul him).exp)
  have hlog := hN.log (fun p => (greenLogNormSq_pos κ p.1 p.2).ne')
  unfold greenLogDensity
  apply ContDiff.exp
  exact (((contDiff_const.add (contDiff_const.mul contDiff_fst.snd)).add
    (contDiff_const.mul him)).sub (contDiff_const.mul hlog))

lemma greenLogDensity_spatial_derivative (κ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    HasDerivAt (greenLogDensity κ q)
      (greenLogDensity κ q x * (greenExponent κ * Real.sqrt κ * (q.1.re - Real.sqrt κ * x) /
        greenLogNormSq κ q x)) x := by
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2 * (q.1.re - Real.sqrt κ * x) * (-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2 * q.1.im)) using 1 <;> try rfl
    simp
  have hlog := hN.log (greenLogNormSq_pos κ q x).ne'
  have hd := ((hasDerivAt_const x (-codimension κ * Real.log 2 + codimension κ * q.2 +
    (greenExponent κ - codimension κ) * q.1.im)).sub
      (hlog.const_mul (greenExponent κ / 2))).exp
  convert hd using 1 <;> try rfl
  dsimp only [greenLogDensity, Pi.sub_apply, Pi.mul_apply, Function.comp_def]
  ring

lemma greenLogDensity_spatial_second (κ : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    iteratedDeriv 2 (greenLogDensity κ q) x =
      greenLogDensity κ q x * κ * greenExponent κ *
        ((greenExponent κ + 1) * (q.1.re - Real.sqrt κ * x) ^ 2 - Real.exp (2 * q.1.im)) /
        (greenLogNormSq κ q x) ^ 2 := by
  have hd : deriv (greenLogDensity κ q) = fun x =>
      greenLogDensity κ q x * (greenExponent κ * Real.sqrt κ * (q.1.re - Real.sqrt κ * x) /
        greenLogNormSq κ q x) := funext fun x => (greenLogDensity_spatial_derivative κ q x).deriv
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2 * (q.1.re - Real.sqrt κ * x) * (-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2 * q.1.im)) using 1 <;> try rfl
    simp
  have hcoef := (hX.const_mul (greenExponent κ * Real.sqrt κ)).div hN
    (greenLogNormSq_pos κ q x).ne'
  have hsecond := (greenLogDensity_spatial_derivative κ q x).mul hcoef
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq] at hsecond
  change HasDerivAt (fun y => greenLogDensity κ q y *
    (greenExponent κ * Real.sqrt κ * (q.1.re - Real.sqrt κ * y) / greenLogNormSq κ q y)) _ x at hsecond
  rw [hsecond.deriv]
  have hn := (greenLogNormSq_pos κ q x).ne'
  dsimp only [greenLogNormSq]
  generalize greenLogDensity κ q x = f
  generalize greenExponent κ = a
  generalize q.1.re - Real.sqrt κ * x = X
  generalize Real.exp (2 * q.1.im) = Y
  have hs := Real.sq_sqrt hκ
  generalize Real.sqrt κ = r at *
  rw [← hs]
  field_simp
  ring

lemma greenLogDensity_directional (κ : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => greenLogDensity κ r x) q) v =
      greenLogDensity κ q x * (codimension κ * v.2 +
        (greenExponent κ - codimension κ) * v.1.im - (greenExponent κ / 2) *
          ((2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
            2 * Real.exp (2 * q.1.im) * v.1.im) / greenLogNormSq κ q x)) := by
  have hzre : HasDerivAt (fun t : ℝ => (q + t • v).1.re) v.1.re 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_re, Complex.smul_re, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.re).const_add q.1.re
  have hzim : HasDerivAt (fun t : ℝ => (q + t • v).1.im) v.1.im 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_im, Complex.smul_im, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.im).const_add q.1.im
  have hj : HasDerivAt (fun t : ℝ => (q + t • v).2) v.2 0 := by
    simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, id_eq, one_mul]
      using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add q.2
  have hN : HasDerivAt (fun t : ℝ => greenLogNormSq κ (q + t • v) x)
      (2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
        2 * Real.exp (2 * q.1.im) * v.1.im) 0 := by
    convert ((hzre.sub_const (Real.sqrt κ * x)).pow 2).add ((hzim.const_mul 2).exp) using 1 <;> try rfl
    simp only [zero_smul, add_zero, Nat.cast_ofNat]
    ring
  have hlog := hN.log (by simpa only [zero_smul, add_zero] using (greenLogNormSq_pos κ q x).ne')
  have hcalc := (((hj.const_mul (codimension κ)).const_add (-codimension κ * Real.log 2)).add
    (hzim.const_mul (greenExponent κ - codimension κ))).sub
      (hlog.const_mul (greenExponent κ / 2))
  have hline : HasDerivAt (fun t : ℝ => greenLogDensity κ (q + t • v) x)
      (greenLogDensity κ q x * (codimension κ * v.2 +
        (greenExponent κ - codimension κ) * v.1.im - (greenExponent κ / 2) *
          ((2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
            2 * Real.exp (2 * q.1.im) * v.1.im) / greenLogNormSq κ q x))) 0 := by
    convert hcalc.exp using 1 <;> try rfl
    simp only [Pi.sub_apply, Pi.add_apply, zero_smul, add_zero]
    simp only [greenLogDensity]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => greenLogDensity κ r x) :=
    (greenLogDensity_contDiff κ).comp (contDiff_id.prodMk contDiff_const)
  have haff : HasDerivAt (fun t : ℝ => q + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (fun r : ℂ × ℝ => greenLogDensity κ r x)
      (fderiv ℝ (fun r : ℂ × ℝ => greenLogDensity κ r x) q) (q + (0 : ℝ) • v) := by
    simpa using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hchain := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hchain.unique hline


theorem green_physical_generator_zero (κ : ℝ) (hκ : 0 < κ) (_hκ8 : κ < 8)
    (q : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => greenLogDensity κ r x) q)
      (physicalLogLoewnerField (Real.sqrt κ * x) q) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (greenLogDensity κ q) x = 0 := by
  rw [greenLogDensity_directional, greenLogDensity_spatial_second κ hκ.le]
  obtain ⟨hr, hi, hj⟩ := physicalLogLoewnerField_components κ q x
  rw [hr, hi, hj]
  have ha : κ * (greenExponent κ + 1) = 8 := by
    simp only [greenExponent, sub_add_cancel]
    field_simp
  have hp : κ * greenExponent κ = 8 * codimension κ := by
    dsimp only [greenExponent, codimension, dimension]
    field_simp
    ring
  have hc1 : -4 * greenExponent κ + κ * greenExponent κ * (greenExponent κ + 1) / 2 = 0 := by
    linear_combination (greenExponent κ / 2) * ha
  have hc2 : 4 * codimension κ - κ * greenExponent κ / 2 = 0 := by
    linarith
  calc
    _ = greenLogDensity κ q x *
      ((-4 * greenExponent κ + κ * greenExponent κ * (greenExponent κ + 1) / 2) *
        (q.1.re - Real.sqrt κ * x) ^ 2 +
        (4 * codimension κ - κ * greenExponent κ / 2) * Real.exp (2 * q.1.im)) /
      (greenLogNormSq κ q x) ^ 2 := by
        have hn := (greenLogNormSq_pos κ q x).ne'
        field_simp
        dsimp only [greenLogNormSq]
        ring
    _ = 0 := by rw [hc1, hc2]; ring

lemma greenLogDensity_pair_directional (κ : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) (q, x) (v, 0) =
      fderiv ℝ (fun r : ℂ × ℝ => greenLogDensity κ r x) q v := by
  have hd := ((greenLogDensity_contDiff κ).differentiable (by simp)) (q, x)
  have hp := (hasFDerivAt_id (𝕜 := ℝ) q).prodMk (hasFDerivAt_const (𝕜 := ℝ) (E := ℂ × ℝ) x q)
  have hc := (hd.hasFDerivAt.comp q hp).fderiv
  have he := congrArg (fun D : (ℂ × ℝ) →L[ℝ] ℝ => D v) hc
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, id_eq, zero_apply] using he.symm

 

lemma exists_compact_green_field (κ R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : (ℂ × ℝ) × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ q x, ‖(q, x)‖ ≤ R → φ (q, x) = greenLogDensity κ q x) ∧
      (∀ q x, ‖(q, x)‖ ≤ R →
        fderiv ℝ φ (q, x) = fderiv ℝ (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) (q, x)) ∧
      (∀ q x, ‖(q, x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (q, y)) x =
        iteratedDeriv 2 (greenLogDensity κ q) x) := by
  let b : ContDiffBump (0 : (ℂ × ℝ) × ℝ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let φ (p : (ℂ × ℝ) × ℝ) : ℝ := b p * greenLogDensity κ p.1 p.2
  have hnear (p : (ℂ × ℝ) × ℝ) (hp : ‖p‖ ≤ R) :
      φ =ᶠ[𝓝 p] (fun r : (ℂ × ℝ) × ℝ => greenLogDensity κ r.1 r.2) := by
    have hball : p ∈ Metric.ball (0 : (ℂ × ℝ) × ℝ) b.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      change ‖p‖ < R + 1
      linarith
    filter_upwards [b.eventuallyEq_one_of_mem_ball hball] with r hr
    simp only [φ, hr, Pi.one_apply, one_mul]
  refine ⟨φ, b.contDiff.mul (greenLogDensity_contDiff κ), b.hasCompactSupport.mul_right,
    (fun q x h => (hnear (q, x) h).eq_of_nhds), ?_, ?_⟩
  · intro q x h
    exact (hnear (q, x) h).fderiv_eq
  · intro q x h
    have he := (hnear (q, x) h).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)
    exact he.iteratedDeriv_eq 2

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_LoewnerCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Loewner Charts for chordal SLE. -/

section
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge


lemma IsCapacityTwoWitness.fullRadius_positive
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    0 < fullRadius G T z := by
  exact div_pos (mul_pos (by norm_num) (h.imag_positive T z hz))
    (h.derivative_norm_positive hU T z hz)

lemma loewnerPairCoefficient_re (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ) :
    (loewnerPairCoefficient U G z z u).re =
      -2 * ((G u.toNNReal z - (U u.toNNReal : ℂ)).re ^ 2 - (G u.toNNReal z).im ^ 2) /
        Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ)) ^ 2 := by
  simp only [loewnerPairCoefficient, Complex.div_re, Complex.neg_re, Complex.re_ofNat,
    Complex.neg_im, Complex.im_ofNat, neg_zero, zero_mul, zero_div, add_zero,
    Complex.mul_re, Complex.normSq_mul, Complex.sub_im, Complex.ofReal_im, sub_zero,
    pow_two]

lemma IsCapacityTwoWitness.radius_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun v : ℝ => fullRadius G v.toNNReal z)
      (-4 * (G u.toNNReal z).im ^ 2 /
        Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ)) ^ 2 * fullRadius G u.toNNReal z)
      (Icc 0 (T : ℝ)) u := by
  have hlu := h.live_at_real_time T z hz u hu.2
  have hJ := h.derivative_norm_positive hU u.toNNReal z hlu
  have hN : Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ)) ≠ 0 :=
    (Complex.normSq_pos.mpr (h.centered_ne_zero _ z hlu)).ne'
  have hd := ((h.imag_derivative T z hz u hu).const_mul 2).div
    (h.derivative_norm_derivative hU T z hz u hu) hJ.ne'
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  try rfl
  rw [loewnerPairCoefficient_re]
  let X := (G u.toNNReal z - (U u.toNNReal : ℂ)).re
  let Y := (G u.toNNReal z).im
  let J := ‖deriv (G u.toNNReal) z‖
  let N := Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ))
  have hNeq : N = X ^ 2 + Y ^ 2 := by
    simp only [N, X, Y, Complex.normSq_apply, Complex.sub_im, Complex.ofReal_im, sub_zero, pow_two]
  change -4 * Y ^ 2 / N ^ 2 * (2 * Y / J) =
    ((2 * (-2 * Y / N)) * J - 2 * Y * (J * (-2 * (X ^ 2 - Y ^ 2) / N ^ 2))) / J ^ 2
  have hn : N ≠ 0 := hN
  have hj : J ≠ 0 := hJ.ne'
  field_simp
  rw [hNeq]
  ring

 
theorem loewner_radius_clock_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (u : ℝ) (hu : u ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt
      (fun v : ℝ => Real.log ((2 * z.im) / fullRadius G v.toNNReal z))
      (4 * (G u.toNNReal z).im ^ 2 /
        (Complex.normSq (G u.toNNReal z - (U u.toNNReal : ℂ))) ^ 2)
      (Icc 0 (T : ℝ)) u := by
  have hp := h.fullRadius_positive hU u.toNNReal z (h.live_at_real_time T z hz u hu.2)
  have hc : 2 * z.im ≠ 0 := ne_of_gt (mul_pos (by norm_num) hz.1.1)
  have hr := h.radius_derivative hU T z hz u hu
  have hd := ((hasDerivWithinAt_const u (Icc 0 (T : ℝ)) (2 * z.im)).div hr hp.ne').log
    (div_ne_zero hc hp.ne')
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  try rfl
  simp only [Pi.div_apply]
  field_simp [hp.ne', hc, (show z.im ≠ 0 from hz.1.1.ne')]
  ring

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_BoundaryDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Density for chordal SLE. -/

section


section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge

lemma continuous_hittingBtwn_mem {Ω : Type*} (H : ℝ≥0 → Ω → ℝ)
    (hHc : ∀ ω, Continuous (fun t => H t ω)) (T : ℝ≥0) (ω : Ω)
    (he : ∃ j ∈ Icc 0 T, H j ω ∈ ({0} : Set ℝ)) :
    H (hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω) ω = 0 := by
  have hc : IsClosed (Icc 0 T ∩ {t : ℝ≥0 | H t ω ∈ ({0} : Set ℝ)}) :=
    isClosed_Icc.inter (isClosed_singleton.preimage (hHc ω))
  have hn : (Icc 0 T ∩ {t : ℝ≥0 | H t ω ∈ ({0} : Set ℝ)}).Nonempty := by
    obtain ⟨j, hj, hh⟩ := he
    exact ⟨j, hj, hh⟩
  have hh := hc.csInf_mem hn (bddBelow_Icc.inter_of_left)
  simpa only [hittingBtwn_def, ite_eq_left he, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff] using hh.2

lemma continuous_zero_iff_dense
    (H : ℝ≥0 → ℝ) (hHc : Continuous H) (hHn : ∀ t, 0 ≤ H t) (t : ℝ≥0) :
    (∃ s ≤ t, H s = 0) ↔
      ∀ n : ℕ, ∃ k : ℕ,
        H (TopologicalSpace.denseSeq (Iic t) k) < 1 / ((n : ℝ) + 1) := by
  let : Nonempty (Iic t) := ⟨⟨0, show (0 : ℝ≥0) ≤ t from zero_le⟩⟩
  constructor
  · rintro ⟨s, hs, he⟩ n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact (TopologicalSpace.denseRange_denseSeq (Iic t)).exists_mem_open
      (isOpen_lt (hHc.comp continuous_subtype_val) continuous_const)
      ⟨⟨s, hs⟩, by simpa only [mem_ofPred_eq, Function.comp_apply, he] using hpos⟩
  · intro he
    have hcc : IsCompact (Iic t) := by
      have heq : Iic t = Icc 0 t := by ext s; simp
      rw [heq]
      exact isCompact_Icc
    obtain ⟨s, hs, hmin⟩ := hcc.exists_isMinOn
      ⟨0, show (0 : ℝ≥0) ≤ t from zero_le⟩ hHc.continuousOn
    refine ⟨s, hs, le_antisymm ?_ (hHn s)⟩
    apply ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact Eventually.of_forall fun n => by
      obtain ⟨k, hk⟩ := he n
      exact (hmin (TopologicalSpace.denseSeq (Iic t) k).property).trans hk.le

theorem continuous_nonnegative_first_zero_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : Filtration ℝ≥0 mΩ)
    (H : ℝ≥0 → Ω → ℝ) (hHa : Adapted f H)
    (hHc : ∀ ω, Continuous (fun t => H t ω))
    (hHn : ∀ t ω, 0 ≤ H t ω) (T : ℝ≥0) :
    IsStoppingTime f (fun ω => ((hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω : ℝ≥0) : WithTop ℝ≥0)) ∧
    (∀ ω, hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω ≤ T) ∧
    (∀ ω t, t < hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω → 0 < H t ω) ∧
    (∀ ω, hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω < T → H (hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω) ω = 0) := by
  classical
  have hb (ω : Ω) := hittingBtwn_le (u := H) (s := ({0} : Set ℝ)) (n := 0) (m := T) ω
  have hmem (ω : Ω) (h : hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω < T) :
      H (hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω) ω = 0 := by
    apply continuous_hittingBtwn_mem H hHc T ω
    by_contra he
    simp only [hittingBtwn_def, ite_eq_right he] at h
    exact lt_irrefl _ h
  refine ⟨?_, hb, ?_, hmem⟩
  · intro t
    by_cases hT : T ≤ t
    · have he : {ω : Ω | ((hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} = univ := by
        ext ω
        simp only [mem_ofPred_eq, mem_univ, iff_true, WithTop.coe_le_coe]
        exact (hb ω).trans hT
      rw [he]
      exact MeasurableSet.univ
    · have ht : t < T := lt_of_not_ge hT
      let : Nonempty (Iic t) := ⟨⟨0, show (0 : ℝ≥0) ≤ t from zero_le⟩⟩
      have he (ω : Ω) : hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω ≤ t ↔ ∃ s ≤ t, H s ω = 0 := by
        constructor
        · intro h
          exact ⟨_, h, hmem ω (h.trans_lt ht)⟩
        · rintro ⟨s, hs, h0⟩
          exact (hittingBtwn_le_of_mem (zero_le) (hs.trans ht.le) (by simpa using h0)).trans hs
      have hset : {ω : Ω | ((hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
          ⋂ n : ℕ, ⋃ k : ℕ, {ω : Ω | H (TopologicalSpace.denseSeq (Iic t) k) ω < 1 / ((n : ℝ) + 1)} := by
        ext ω
        simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_iInter, mem_iUnion]
        exact (he ω).trans (continuous_zero_iff_dense (fun s => H s ω) (hHc ω) (fun s => hHn s ω) t)
      rw [hset]
      apply MeasurableSet.iInter
      intro n
      apply MeasurableSet.iUnion
      intro k
      have hm := (hHa (TopologicalSpace.denseSeq (Iic t) k)).mono
        (f.mono (TopologicalSpace.denseSeq (Iic t) k).property) le_rfl
      exact measurableSet_lt hm measurable_const
  · intro ω t ht
    have hn := notMem_of_lt_hittingBtwn ht (zero_le)
    exact lt_of_le_of_ne (hHn t ω) (by simpa only [mem_singleton_iff, ne_eq, eq_comm] using hn)

end SLEExactGauge
end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma logAngleSq_pos (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    0 < logAngleSq κ q b :=
  div_pos (Real.exp_pos _) (greenLogNormSq_pos κ q b)

lemma logAngleSq_le_one (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    logAngleSq κ q b ≤ 1 := by
  apply (div_le_one (greenLogNormSq_pos κ q b)).mpr
  exact le_add_of_nonneg_left (sq_nonneg _)

lemma continuous_logAngleSq (κ : ℝ) :
    Continuous (fun p : (ℂ × ℝ) × ℝ => logAngleSq κ p.1 p.2) := by
  have hi : Continuous (fun p : (ℂ × ℝ) × ℝ => p.1.1.im) :=
    Complex.continuous_im.comp (continuous_fst.fst)
  have hr : Continuous (fun p : (ℂ × ℝ) × ℝ => p.1.1.re) :=
    Complex.continuous_re.comp (continuous_fst.fst)
  exact (Real.continuous_exp.comp (continuous_const.mul hi)).div
    (((hr.sub (continuous_const.mul continuous_snd)).pow 2).add
      (Real.continuous_exp.comp (continuous_const.mul hi)))
    (fun p => (greenLogNormSq_pos κ p.1 p.2).ne')

lemma greenLogDensity_radius_angle (κ η₀ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    greenLogDensity κ q b =
      Real.exp (codimension κ * (logRadiusClock η₀ q - Real.log 2 - η₀)) *
        (logAngleSq κ q b) ^ (greenExponent κ / 2) := by
  rw [Real.rpow_def_of_pos (logAngleSq_pos κ q b), ← Real.exp_add]
  unfold logAngleSq
  rw [Real.log_div (Real.exp_ne_zero _) (greenLogNormSq_pos κ q b).ne', Real.log_exp]
  unfold greenLogDensity logRadiusClock
  congr 1
  ring

lemma codimension_pos (κ : ℝ) (hκ8 : κ < 8) : 0 < codimension κ := by
  dsimp [codimension, dimension]
  linarith

lemma greenExponent_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < greenExponent κ := by
  unfold greenExponent
  have : 1 < 8 / κ := (lt_div_iff₀ hκ).mpr (by simpa using hκ8)
  linarith

lemma greenLogDensity_le_at_angular_exit
    (κ η₀ u ε : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (q : ℂ × ℝ) (b : ℝ)
    (hclock : logRadiusClock η₀ q ≤ u) (hangle : logAngleSq κ q b ≤ ε) :
    greenLogDensity κ q b ≤
      Real.exp (codimension κ * (u - Real.log 2 - η₀)) * ε ^ (greenExponent κ / 2) := by
  rw [greenLogDensity_radius_angle κ η₀ q b]
  apply mul_le_mul
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith)
      (codimension_pos κ hκ8).le)
  · exact Real.rpow_le_rpow (logAngleSq_pos κ q b).le hangle
      (div_nonneg (greenExponent_pos κ hκ hκ8).le (by norm_num))
  · exact Real.rpow_nonneg (logAngleSq_pos κ q b).le _
  · exact (Real.exp_pos _).le

lemma logClockRate_angle (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    logClockRate κ q b = 4 * logAngleSq κ q b ^ 2 / Real.exp (2 * q.1.im) := by
  unfold logClockRate logAngleSq
  field_simp [(Real.exp_pos (2 * q.1.im)).ne', (greenLogNormSq_pos κ q b).ne']

lemma log_height_clock_derivative_nonneg
    (κ ε : ℝ) (hε : 0 < ε) (q : ℂ × ℝ) (b : ℝ)
    (ha : ε ≤ logAngleSq κ q b) :
    0 ≤ -2 / greenLogNormSq κ q b + logClockRate κ q b / (2 * ε) := by
  have hN := greenLogNormSq_pos κ q b
  have h1 : 1 ≤ logAngleSq κ q b / ε := (le_div_iff₀ hε).mpr (by simpa using ha)
  have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 / greenLogNormSq κ q b by positivity)
  have he : logClockRate κ q b / (2 * ε) =
      (2 / greenLogNormSq κ q b) * (logAngleSq κ q b / ε) := by
    unfold logClockRate logAngleSq
    field_simp
    ring
  rw [he, neg_div]
  simpa only [mul_one, sub_eq_add_neg, add_comm] using sub_nonneg.mpr h2

lemma log_clock_rate_lower (κ ε η₀ : ℝ) (hε : 0 < ε) (q : ℂ × ℝ) (b : ℝ)
    (ha : ε ≤ logAngleSq κ q b) (hi : q.1.im ≤ η₀) :
    4 * ε ^ 2 / Real.exp (2 * η₀) ≤ logClockRate κ q b := by
  rw [logClockRate_angle]
  have hs : ε ^ 2 ≤ logAngleSq κ q b ^ 2 := sq_le_sq₀ hε.le (logAngleSq_pos κ q b).le |>.mpr ha
  have he : Real.exp (2 * q.1.im) ≤ Real.exp (2 * η₀) :=
    Real.exp_le_exp.mpr (by linarith)
  exact div_le_div₀ (by positivity) (by nlinarith) (Real.exp_pos _) he

 

theorem log_loewner_height_clock_bounds
    {Q : ℝ → ℂ × ℝ} {B : ℝ → ℝ} {κ T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hQ0 : (Q 0).2 = 0)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (physicalLogLoewnerField (Real.sqrt κ * B t) (Q t)) (Icc 0 T) t)
    (hangle : ∀ t ∈ Icc 0 T, ε ≤ logAngleSq κ (Q t) (B t)) :
    (Q T).1.im ≤ (Q 0).1.im ∧
    (Q 0).1.im - logRadiusClock (Q 0).1.im (Q T) / (2 * ε) ≤ (Q T).1.im ∧
    (4 * ε ^ 2 / Real.exp (2 * (Q 0).1.im)) * T ≤ logRadiusClock (Q 0).1.im (Q T) := by
  let η₀ := (Q 0).1.im
  let c := 4 * ε ^ 2 / Real.exp (2 * η₀)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousWithinAt
  have hi : AntitoneOn (fun t => (Q t).1.im) (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hQc))
      (fun t ht => (log_ode_im_derivative (hQ t (interior_subset ht))).mono interior_subset)
    intro t ht
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (greenLogNormSq_pos κ (Q t) (B t)).le
  have hib (t : ℝ) (ht : t ∈ Icc 0 T) : (Q t).1.im ≤ η₀ := hi h0 ht ht.1
  have hS0 : logRadiusClock η₀ (Q 0) = 0 := by simp [logRadiusClock, η₀, hQ0]
  have hSc : ContinuousOn (fun t => logRadiusClock η₀ (Q t)) (Icc 0 T) :=
    (continuous_logRadiusClock η₀).comp_continuousOn hQc
  have hlo : MonotoneOn (fun t => (Q t).1.im +
      logRadiusClock η₀ (Q t) / (2 * ε)) (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      ((Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hQc)).add
        (hSc.div_const _))
      (fun t ht => ((log_ode_im_derivative (hQ t (interior_subset ht))).add
        ((log_ode_clock_derivative η₀ (hQ t (interior_subset ht))).div_const _)).mono interior_subset)
    intro t ht
    exact log_height_clock_derivative_nonneg κ ε hε (Q t) (B t) (hangle t (interior_subset ht))
  have hrate : MonotoneOn (fun t => logRadiusClock η₀ (Q t) - c * t) (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (hSc.sub (continuous_const.mul continuous_id).continuousOn)
      (fun t ht => ((log_ode_clock_derivative η₀ (hQ t (interior_subset ht))).sub
        ((hasDerivWithinAt_id t (Icc 0 T)).const_mul c)).mono interior_subset)
    intro t ht
    have hb := log_clock_rate_lower κ ε η₀ hε (Q t) (B t)
      (hangle t (interior_subset ht)) (hib t (interior_subset ht))
    change 0 ≤ logClockRate κ (Q t) (B t) - c * 1
    simpa only [mul_one] using sub_nonneg.mpr hb
  refine ⟨hib T hTT, ?_, ?_⟩
  · have hh := hlo h0 hTT hT
    dsimp only at hh
    rw [hS0, zero_div, add_zero] at hh
    linarith
  · have hh := hrate h0 hTT hT
    dsimp only at hh
    rw [hS0, mul_zero, sub_zero] at hh
    linarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma compact_green_drift_zero
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (lo hi : ℝ) (hle : lo ≤ hi)
    (φ : (ℂ × ℝ) × ℝ → ℝ) (q : ℂ × ℝ) (x : ℝ)
    (hφD : fderiv ℝ φ (q, x) =
      fderiv ℝ (fun p : (ℂ × ℝ) × ℝ => greenLogDensity κ p.1 p.2) (q, x))
    (hφ2 : iteratedDeriv 2 (fun y => φ (q, y)) x =
      iteratedDeriv 2 (greenLogDensity κ q) x)
    (hq : q.1.im ∈ Icc lo hi) :
    fderiv ℝ φ (q, x)
        (clippedLogLoewnerField lo hi hle (Real.sqrt κ * x) q, 0) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (fun y => φ (q, y)) x = 0 := by
  rw [hφD, hφ2, greenLogDensity_pair_directional,
    clippedLogLoewnerField_eq_physical lo hi hle _ _ hq]
  exact green_physical_generator_zero κ hκ hκ8 q x

 

theorem ClippedLogSolution.stopped_green
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) :
    Integrable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
        greenLogDensity κ q₀ 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_green_field κ R hR
  obtain ⟨L₀, K₀, hL₀, _⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) :=
    clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)
  have hBr : Measurable (fun p : ℝ × Ω => Real.sqrt κ * B p.1.toNNReal p.2) :=
    (hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      measurable_snd)).const_mul _
  have hpair : Measurable (fun p : ℝ × Ω =>
      (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)) := hBr.prodMk c.measurable
  have hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun p : ℝ × Ω => (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)))
    exact (continuous_clippedLogLoewnerField lo hi hle).measurable.comp hpair
  have hVb (t : ℝ) (ω : Ω) : ‖V t ω‖ ≤ (max c.L L₀ : ℝ≥0) :=
    (hL₀ _ _).trans (by exact_mod_cast le_max_right c.L L₀)
  obtain ⟨K, hfield⟩ := compact_state_smooth_brownian_field B hm c.Q V (max c.L L₀)
    c.measurable c.adapted (fun ω => (c.lipschitz ω).weaken (le_max_left _ _)) hVm hVb
    (fun t ω ht => c.derivative ω t ht) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (c.Q t ω, x)
  let a (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (c.Q t ω, x) (V t ω, 0)
  have hzero (ω : Ω) (u : ℝ) (hu : 0 ≤ u) (hut : u < (τ ω : ℝ)) :
      brownianFieldDrift B F a u ω = 0 := by
    have ht : u.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr hut.le
    obtain ⟨hball, hlo, hhi⟩ := hinside ω u.toNNReal ht
    change fderiv ℝ φ (c.Q (u.toNNReal : ℝ) ω, B u.toNNReal ω)
      (V (u.toNNReal : ℝ) ω, 0) + _ = 0
    dsimp only [V]
    rw [Real.toNNReal_coe]
    exact compact_green_drift_zero κ hκ hκ8 lo hi hle φ _ _
      (hφD _ _ hball) (hφ2 _ _ hball) ⟨hlo, hhi⟩
  have hopt := brownian_time_field_optional hB hm hBm hBc K F a hfield τ hτ T hb hzero
  have hτm := stopping_time_measurable_nnreal hτ
  have hBmτ : Measurable (fun ω => B (τ ω) ω) := hBm.comp (hτm.prodMk measurable_id)
  have hQmτ : Measurable (fun ω => c.Q (τ ω) ω) :=
    c.measurable.comp ((NNReal.continuous_coe.measurable.comp hτm).prodMk measurable_id)
  have hfm : Measurable (fun ω => F (τ ω) ω (B (τ ω) ω)) :=
    hφ.continuous.measurable.comp (hQmτ.prodMk hBmτ)
  have hfi : Integrable (fun ω => F (τ ω) ω (B (τ ω) ω)) P := by
    apply Integrable.of_bound hfm.aestronglyMeasurable (K : ℝ)
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, iteratedDeriv_zero] using
        hfield.bound (τ ω) ω (B (τ ω) ω) 0 (by decide)
  have hfeq (ω : Ω) : F (τ ω) ω (B (τ ω) ω) =
      greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) :=
    hφeq _ _ (hinside ω (τ ω) le_rfl).1
  refine ⟨hfi.congr (Eventually.of_forall hfeq), ?_⟩
  calc
    _ = ∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (hfeq ω).symm)
    _ = ∫ ω, F 0 ω (B 0 ω) ∂P := hopt
    _ = ∫ _, greenLogDensity κ q₀ 0 ∂P := by
      apply integral_congr_ae
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hB0
      change φ (c.Q 0 ω, B 0 ω) = _
      have hh : ‖(c.Q 0 ω, B 0 ω)‖ ≤ R := by
        simpa only [NNReal.coe_zero] using (hinside ω 0 zero_le).1
      rw [hφeq _ _ hh, c.initial ω, hB0]
    _ = greenLogDensity κ q₀ 0 := by simp

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_FiniteRadiusStop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Radius Stop for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma continuous_nonneg_at_boundary (D : ℝ≥0 → ℝ) (hD : Continuous D)
    (h0 : 0 ≤ D 0) (τ : ℝ≥0) (hb : ∀ t, t < τ → 0 < D t) :
    ∀ t, t ≤ τ → 0 ≤ D t := by
  intro t ht
  by_cases hτ : τ = 0
  · have : t = 0 := le_antisymm (ht.trans hτ.le) zero_le
    simpa only [this] using h0
  · have hτpos : 0 < τ := pos_iff_ne_zero.mpr hτ
    apply le_on_closure (s := Iio τ) (f := fun _ : ℝ≥0 => (0 : ℝ)) (g := D)
      (fun s hs => (hb s hs).le) continuous_const.continuousOn hD.continuousOn
    rw [closure_Iio' (show (Iio τ).Nonempty from ⟨0, hτpos⟩)]
    exact ht

 

theorem first_margin_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ) (hDa : Adapted f D)
    (hDc : ∀ ω, Continuous (fun t => D t ω)) (hD0 : ∀ ω, 0 ≤ D 0 ω)
    (T : ℝ≥0) :
    ∃ τ : Ω → ℝ≥0,
      IsStoppingTime f (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, τ ω ≤ T) ∧
      (∀ ω t, t ≤ τ ω → 0 ≤ D t ω) ∧
      (∀ ω t, t < τ ω → 0 < D t ω) ∧
      (∀ ω, τ ω < T → D (τ ω) ω = 0) := by
  let H (t : ℝ≥0) (ω : Ω) := max 0 (D t ω)
  have hHa : Adapted f H := fun t => measurable_const.max (hDa t)
  have hHc (ω : Ω) : Continuous (fun t => H t ω) := continuous_const.max (hDc ω)
  have hHn (t : ℝ≥0) (ω : Ω) : 0 ≤ H t ω := le_max_left _ _
  let τ (ω : Ω) := hittingBtwn H ({0} : Set ℝ) (0 : ℝ≥0) T ω
  obtain ⟨hτ, hb, hpre, hat⟩ := continuous_nonnegative_first_zero_stopping f H hHa hHc hHn T
  have hDpre (ω : Ω) (t : ℝ≥0) (ht : t < τ ω) : 0 < D t ω := by
    have hh := hpre ω t ht
    simpa only [H, lt_max_iff, lt_self_iff_false, false_or] using hh
  have hDle (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) : 0 ≤ D t ω :=
    continuous_nonneg_at_boundary (fun s => D s ω) (hDc ω) (hD0 ω) (τ ω) (hDpre ω) t ht
  refine ⟨τ, hτ, hb, hDle, hDpre, ?_⟩
  intro ω ht
  apply le_antisymm _ (hDle ω (τ ω) le_rfl)
  have hh := le_max_right 0 (D (τ ω) ω)
  exact hh.trans (hat ω ht).le


lemma continuous_logStopMargin (κ η₀ u lo hi ε N : ℝ) :
    Continuous (fun p : (ℂ × ℝ) × ℝ => logStopMargin κ η₀ u lo hi ε N p.1 p.2) := by
  unfold logStopMargin
  exact (continuous_const.sub ((continuous_logRadiusClock η₀).comp continuous_fst)).min
    (((continuous_logAngleSq κ).sub continuous_const).min
      (((Complex.continuous_im.comp continuous_fst.fst).sub continuous_const).min
        ((continuous_const.sub (Complex.continuous_im.comp continuous_fst.fst)).min
          (continuous_const.sub continuous_snd.abs))))

lemma logStopMargin_nonneg_iff (κ η₀ u lo hi ε N : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    0 ≤ logStopMargin κ η₀ u lo hi ε N q b ↔
      logRadiusClock η₀ q ≤ u ∧ ε ≤ logAngleSq κ q b ∧
        lo ≤ q.1.im ∧ q.1.im ≤ hi ∧ |b| ≤ N := by
  simp only [logStopMargin, le_min_iff, sub_nonneg]

lemma logStopMargin_pos_iff (κ η₀ u lo hi ε N : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    0 < logStopMargin κ η₀ u lo hi ε N q b ↔
      logRadiusClock η₀ q < u ∧ ε < logAngleSq κ q b ∧
        lo < q.1.im ∧ q.1.im < hi ∧ |b| < N := by
  simp only [logStopMargin, lt_min_iff, sub_pos]

lemma ClippedLogSolution.norm_le
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (ω : Ω) (t T : ℝ≥0) (ht : t ≤ T) :
    ‖c.Q t ω‖ ≤ ‖q₀‖ + c.L * T := by
  have hh := (c.lipschitz ω).norm_sub_le (t : ℝ) 0
  rw [c.initial ω, sub_zero, Real.norm_eq_abs, abs_of_nonneg t.coe_nonneg] at hh
  have hn := norm_add_le (c.Q t ω - q₀) q₀
  rw [sub_add_cancel] at hn
  have hmul : (c.L : ℝ) * t ≤ c.L * T :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast ht) c.L.coe_nonneg
  linarith

 

theorem ClippedLogSolution.finite_radius_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hq0 : q₀.2 = 0)
    (u ε N : ℝ) (hu : 0 ≤ u) (hε : 0 < ε) (hN : 0 ≤ N)
    (hε0 : ε ≤ logAngleSq κ q₀ 0)
    (hlo : lo < q₀.1.im - u / (2 * ε)) (hhi : q₀.1.im < hi)
    (T : ℝ≥0) (hT : u < (4 * ε ^ 2 / Real.exp (2 * q₀.1.im)) * T) :
    ∃ τ : Ω → ℝ≥0,
      IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, τ ω < T) ∧
      (∀ ω t, t ≤ τ ω →
        logRadiusClock q₀.1.im (c.Q t ω) ≤ u ∧
        ε ≤ logAngleSq κ (c.Q t ω) (B t ω) ∧
        lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi ∧ |B t ω| ≤ N) ∧
      (∀ ω t, t < τ ω →
        logRadiusClock q₀.1.im (c.Q t ω) < u ∧
        ε < logAngleSq κ (c.Q t ω) (B t ω) ∧
        lo < (c.Q t ω).1.im ∧ (c.Q t ω).1.im < hi ∧ |B t ω| < N) ∧
      (∀ ω, logRadiusClock q₀.1.im (c.Q (τ ω) ω) = u ∨
        logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = ε ∨ |B (τ ω) ω| = N) ∧
      Integrable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) = greenLogDensity κ q₀ 0 := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let D (t : ℝ≥0) (ω : Ω) := logStopMargin κ q₀.1.im u lo hi ε N (c.Q t ω) (B t ω)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hDa : Adapted f D := by
    intro t
    change Measurable[f t] ((fun p : (ℂ × ℝ) × ℝ => logStopMargin κ q₀.1.im u lo hi ε N p.1 p.2) ∘
      (fun ω => (c.Q t ω, B t ω)))
    exact (continuous_logStopMargin κ q₀.1.im u lo hi ε N).measurable.comp
      ((c.adapted t).prodMk (hBa t))
  have hDc (ω : Ω) : Continuous (fun t => D t ω) := by
    change Continuous ((fun p : (ℂ × ℝ) × ℝ => logStopMargin κ q₀.1.im u lo hi ε N p.1 p.2) ∘
      (fun t : ℝ≥0 => (c.Q t ω, B t ω)))
    exact (continuous_logStopMargin κ q₀.1.im u lo hi ε N).comp
      (((c.lipschitz ω).continuous.comp NNReal.continuous_coe).prodMk (hBc ω))
  have hD0 (ω : Ω) : 0 ≤ D 0 ω := by
    change 0 ≤ logStopMargin κ q₀.1.im u lo hi ε N (c.Q (0 : ℝ≥0) ω) (B 0 ω)
    rw [NNReal.coe_zero, c.initial ω, hB0 ω, logStopMargin_nonneg_iff]
    refine ⟨?_, hε0, ?_, hhi.le, ?_⟩
    · simpa only [logRadiusClock, sub_self, zero_add, hq0] using hu
    · have hd : 0 ≤ u / (2 * ε) := div_nonneg hu (by positivity)
      linarith
    · simpa only [abs_zero] using hN
  obtain ⟨τ, hτ, hb, hleD, hltD, hzero⟩ := first_margin_stopping f D hDa hDc hD0 T
  have hin (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) :
      logRadiusClock q₀.1.im (c.Q t ω) ≤ u ∧
      ε ≤ logAngleSq κ (c.Q t ω) (B t ω) ∧
      lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi ∧ |B t ω| ≤ N :=
    (logStopMargin_nonneg_iff κ q₀.1.im u lo hi ε N _ _).mp (hleD ω t ht)
  have hg (ω : Ω) :
      (c.Q (τ ω) ω).1.im ≤ q₀.1.im ∧
      q₀.1.im - logRadiusClock q₀.1.im (c.Q (τ ω) ω) / (2 * ε) ≤ (c.Q (τ ω) ω).1.im ∧
      (4 * ε ^ 2 / Real.exp (2 * q₀.1.im)) * τ ω ≤ logRadiusClock q₀.1.im (c.Q (τ ω) ω) := by
    have hd (s : ℝ) (hs : s ∈ Icc 0 (τ ω : ℝ)) :
        HasDerivWithinAt (fun t => c.Q t ω)
          (physicalLogLoewnerField (Real.sqrt κ * B s.toNNReal ω) (c.Q s ω))
          (Icc 0 (τ ω : ℝ)) s := by
      have hst : s.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr hs.2
      have hbounds := (hin ω s.toNNReal hst).2.2
      rw [Real.coe_toNNReal _ hs.1] at hbounds
      have hh := (c.derivative ω s hs.1).mono (show Icc (0 : ℝ) (τ ω : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
      rwa [clippedLogLoewnerField_eq_physical lo hi hle _ _ ⟨hbounds.1, hbounds.2.1⟩] at hh
    have ha (s : ℝ) (hs : s ∈ Icc 0 (τ ω : ℝ)) :
        ε ≤ logAngleSq κ (c.Q s ω) (B s.toNNReal ω) := by
      have hh := (hin ω s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)).2.1
      simpa only [Real.coe_toNNReal _ hs.1] using hh
    have hq : (c.Q 0 ω).2 = 0 := by rw [c.initial ω, hq0]
    have hh := log_loewner_height_clock_bounds (τ ω).coe_nonneg hε hq hd ha
    simpa only [c.initial ω] using hh
  have hτlt (ω : Ω) : τ ω < T := by
    by_contra hn
    have he : τ ω = T := le_antisymm (hb ω) (not_lt.mp hn)
    have hh := (hg ω).2.2.trans (hin ω (τ ω) le_rfl).1
    rw [he] at hh
    exact (not_le_of_gt hT) hh
  have he (ω : Ω) :
      logRadiusClock q₀.1.im (c.Q (τ ω) ω) = u ∨
      logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = ε ∨ |B (τ ω) ω| = N := by
    obtain ⟨hr, ha, hl, hh, hbn⟩ := hin ω (τ ω) le_rfl
    have hstrictlo : lo < (c.Q (τ ω) ω).1.im := by
      have hdiv := div_le_div_of_nonneg_right hr (show 0 ≤ 2 * ε by positivity)
      linarith [(hg ω).2.1]
    have hstricthi : (c.Q (τ ω) ω).1.im < hi := (hg ω).1.trans_lt hhi
    by_contra hn
    push Not at hn
    have hp : 0 < D (τ ω) ω :=
      (logStopMargin_pos_iff κ q₀.1.im u lo hi ε N _ _).mpr
        ⟨lt_of_le_of_ne hr hn.1, lt_of_le_of_ne ha (Ne.symm hn.2.1),
          hstrictlo, hstricthi, lt_of_le_of_ne hbn hn.2.2⟩
    rw [hzero ω (hτlt ω)] at hp
    exact lt_irrefl 0 hp
  let R := max (‖q₀‖ + c.L * T) N
  have hR : 0 ≤ R := hN.trans (le_max_right _ _)
  have hinside (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) :
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi := by
    refine ⟨?_, (hin ω t ht).2.2.1, (hin ω t ht).2.2.2.1⟩
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    exact ⟨(c.norm_le ω t T (ht.trans (hb ω))).trans (le_max_left _ _),
      (hin ω t ht).2.2.2.2.trans (le_max_right _ _)⟩
  obtain ⟨hint, hmean⟩ := c.stopped_green hB hBm hBc hκ hκ8 R hR τ hτ T hb hinside
  refine ⟨τ, hτ, hτlt, hin, ?_, he, hint, hmean⟩
  intro ω t ht
  exact (logStopMargin_pos_iff κ q₀.1.im u lo hi ε N _ _).mp (hltD ω t ht)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma continuous_path_bounded_by_nat (B : ℝ≥0 → ℝ) (hB : Continuous B) (T : ℝ≥0) :
    ∃ n : ℕ, ∀ t : ℝ≥0, t ≤ T → |B t| < (n : ℝ) + 1 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).exists_bound_of_continuousOn hB.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, fun t ht => ?_⟩
  have hh : |B t| ≤ C := by simpa only [Real.norm_eq_abs] using hC t ⟨zero_le, ht⟩
  linarith

lemma first_radius_angle_le (S A : ℝ≥0 → ℝ) (u ε : ℝ) (s t : ℝ≥0)
    (hpre : ∀ v, v < s → S v < u ∧ ε < A v)
    (hat : S t = u ∨ A t = ε) : s ≤ t := by
  by_contra hn
  obtain ⟨hr, ha⟩ := hpre t (not_le.mp hn)
  rcases hat with h | h
  · exact (ne_of_lt hr) h
  · exact (ne_of_gt ha) h

lemma bounded_iSup_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : Filtration ℝ≥0 mΩ)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, IsStoppingTime f (fun ω => (τ n ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ n ω, τ n ω ≤ T) :
    IsStoppingTime f (fun ω => ((⨆ n, τ n ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro t
  have he : {ω | ((⨆ n, τ n ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
      ⋂ n : ℕ, {ω | (τ n ω : WithTop ℝ≥0) ≤ t} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_iInter]
    exact ciSup_le_iff ⟨T, by rintro v ⟨n, rfl⟩; exact hb n ω⟩
  rw [he]
  exact MeasurableSet.iInter (fun n => hτ n t)

lemma greenLogDensity_nonneg (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) : 0 ≤ greenLogDensity κ q b :=
  (Real.exp_pos _).le

lemma greenLogDensity_le_radius
    (κ η₀ u : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (q : ℂ × ℝ) (b : ℝ)
    (hclock : logRadiusClock η₀ q ≤ u) :
    greenLogDensity κ q b ≤ Real.exp (codimension κ * (u - Real.log 2 - η₀)) := by
  simpa only [Real.one_rpow, mul_one] using
    greenLogDensity_le_at_angular_exit κ η₀ u 1 hκ hκ8 q b hclock (logAngleSq_le_one κ q b)

 

theorem ClippedLogSolution.finite_angular_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hq0 : q₀.2 = 0)
    (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε)
    (hε0 : ε ≤ logAngleSq κ q₀ 0)
    (hlo : lo < q₀.1.im - u / (2 * ε)) (hhi : q₀.1.im < hi)
    (T : ℝ≥0) (hT : u < (4 * ε ^ 2 / Real.exp (2 * q₀.1.im)) * T) :
    ∃ τ : Ω → ℝ≥0,
      IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, τ ω < T) ∧
      (∀ ω t, t ≤ τ ω →
        logRadiusClock q₀.1.im (c.Q t ω) ≤ u ∧
        ε ≤ logAngleSq κ (c.Q t ω) (B t ω) ∧
        lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) ∧
      (∀ ω t, t < τ ω →
        logRadiusClock q₀.1.im (c.Q t ω) < u ∧ ε < logAngleSq κ (c.Q t ω) (B t ω)) ∧
      (∀ ω, logRadiusClock q₀.1.im (c.Q (τ ω) ω) = u ∨
        logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = ε) ∧
      Integrable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) = greenLogDensity κ q₀ 0 := by
  classical
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hall (n : ℕ) := c.finite_radius_cutoff hB hBm hBc hB0 hκ hκ8 hq0
    u ε ((n : ℝ) + 1) hu hε (by positivity) hε0 hlo hhi T hT
  choose τn hstop htime hin hpre hboundary hint hmean using hall
  let τ (ω : Ω) : ℝ≥0 := ⨆ n, τn n ω
  have hb (n : ℕ) (ω : Ω) : τn n ω ≤ T := (htime n ω).le
  have hbd (ω : Ω) : BddAbove (range (fun n => τn n ω)) :=
    ⟨T, by rintro v ⟨n, rfl⟩; exact hb n ω⟩
  have hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)) := bounded_iSup_stopping _ τn hstop T hb
  have hstable (ω : Ω) : ∃ n : ℕ, τ ω = τn n ω ∧
      (∀ m, n ≤ m → τn m ω = τ ω) ∧
      (logRadiusClock q₀.1.im (c.Q (τ ω) ω) = u ∨
        logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) = ε) := by
    obtain ⟨n, hnb⟩ := continuous_path_bounded_by_nat (fun t => B t ω) (hBc ω) T
    have hhit (m : ℕ) (hnm : n ≤ m) :
        logRadiusClock q₀.1.im (c.Q (τn m ω) ω) = u ∨
          logAngleSq κ (c.Q (τn m ω) ω) (B (τn m ω) ω) = ε := by
      rcases hboundary m ω with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have hh := hnb (τn m ω) (hb m ω)
        have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
        linarith
    have hle (m : ℕ) : τn m ω ≤ τn n ω :=
      first_radius_angle_le _ _ u ε _ _ (fun t ht => ⟨(hpre m ω t ht).1, (hpre m ω t ht).2.1⟩)
        (hhit n le_rfl)
    have he : τ ω = τn n ω := le_antisymm (ciSup_le hle) (le_ciSup (hbd ω) n)
    refine ⟨n, he, ?_, ?_⟩
    · intro m hnm
      rw [he]
      apply le_antisymm (hle m)
      exact first_radius_angle_le _ _ u ε _ _
        (fun t ht => ⟨(hpre n ω t ht).1, (hpre n ω t ht).2.1⟩) (hhit m hnm)
    · rw [he]
      exact hhit n le_rfl
  have hτtime (ω : Ω) : τ ω < T := by
    obtain ⟨n, he, _⟩ := hstable ω
    rw [he]
    exact htime n ω
  have hτin (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) :
      logRadiusClock q₀.1.im (c.Q t ω) ≤ u ∧
      ε ≤ logAngleSq κ (c.Q t ω) (B t ω) ∧
      lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi := by
    obtain ⟨n, he, _⟩ := hstable ω
    obtain ⟨h1, h2, h3, h4, _⟩ := hin n ω t (by simpa only [he] using ht)
    exact ⟨h1, h2, h3, h4⟩
  have hτpre (ω : Ω) (t : ℝ≥0) (ht : t < τ ω) :
      logRadiusClock q₀.1.im (c.Q t ω) < u ∧ ε < logAngleSq κ (c.Q t ω) (B t ω) := by
    obtain ⟨n, he, _⟩ := hstable ω
    have hh := hpre n ω t (by simpa only [he] using ht)
    exact ⟨hh.1, hh.2.1⟩
  let K := Real.exp (codimension κ * (u - Real.log 2 - q₀.1.im))
  have hbound (n : ℕ) (ω : Ω) :
      ‖greenLogDensity κ (c.Q (τn n ω) ω) (B (τn n ω) ω)‖ ≤ K := by
    rw [Real.norm_eq_abs, abs_of_nonneg (greenLogDensity_nonneg _ _ _)]
    exact greenLogDensity_le_radius κ q₀.1.im u hκ hκ8 _ _ (hin n ω (τn n ω) le_rfl).1
  have hlim (ω : Ω) : Tendsto
      (fun n => greenLogDensity κ (c.Q (τn n ω) ω) (B (τn n ω) ω)) atTop
      (𝓝 (greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω))) := by
    obtain ⟨n, _, he, _⟩ := hstable ω
    apply tendsto_const_nhds.congr'
    exact (eventually_ge_atTop n).mono (fun m hm => by dsimp only; rw [he m hm])
  have hτm := stopping_time_measurable_nnreal hτ
  have hQm : Measurable (fun ω => c.Q (τ ω) ω) :=
    c.measurable.comp ((NNReal.continuous_coe.measurable.comp hτm).prodMk measurable_id)
  have hBmτ : Measurable (fun ω => B (τ ω) ω) := hBm.comp (hτm.prodMk measurable_id)
  have hfm : Measurable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) :=
    (greenLogDensity_contDiff κ).continuous.measurable.comp (hQm.prodMk hBmτ)
  have hfi : Integrable (fun ω => greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)) P := by
    apply Integrable.of_bound hfm.aestronglyMeasurable K
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (greenLogDensity_nonneg _ _ _)]
      exact greenLogDensity_le_radius κ q₀.1.im u hκ hκ8 _ _ (hτin ω (τ ω) le_rfl).1
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : Ω => K)
    (fun n => (hint n).aestronglyMeasurable) (integrable_const K)
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  have hmean' : (∫ ω, greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
      greenLogDensity κ q₀ 0 := by
    apply tendsto_nhds_unique hconv
    simp only [hmean]
    exact tendsto_const_nhds
  exact ⟨τ, hτ, hτtime, hτin, hτpre, fun ω => (hstable ω).choose_spec.2.2, hfi, hmean'⟩

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma powerLogDensity_contDiff (κ p a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => powerLogDensity κ p a zz.1 zz.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => zz.1.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst.fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => zz.1.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst.fst
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => greenLogNormSq κ zz.1 zz.2) := by
    exact ((hre.sub (contDiff_const.mul contDiff_snd)).pow 2).add
      ((contDiff_const.mul him).exp)
  have hlog := hN.log (fun zz => (greenLogNormSq_pos κ zz.1 zz.2).ne')
  unfold powerLogDensity
  apply ContDiff.exp
  exact (((contDiff_const.add (contDiff_const.mul contDiff_fst.snd)).add
    (contDiff_const.mul him)).sub (contDiff_const.mul hlog))

lemma powerLogDensity_spatial_derivative (κ p a : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    HasDerivAt (powerLogDensity κ p a q)
      (powerLogDensity κ p a q x * (a * Real.sqrt κ * (q.1.re - Real.sqrt κ * x) /
        greenLogNormSq κ q x)) x := by
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2 * (q.1.re - Real.sqrt κ * x) * (-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2 * q.1.im)) using 1 <;> try rfl
    simp
  have hlog := hN.log (greenLogNormSq_pos κ q x).ne'
  have hd := ((hasDerivAt_const x (-p * Real.log 2 + p * q.2 +
    (a - p) * q.1.im)).sub
      (hlog.const_mul (a / 2))).exp
  convert hd using 1 <;> try rfl
  dsimp only [powerLogDensity, Pi.sub_apply, Pi.mul_apply, Function.comp_def]
  ring

lemma powerLogDensity_spatial_second (κ p a : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    iteratedDeriv 2 (powerLogDensity κ p a q) x =
      powerLogDensity κ p a q x * κ * a *
        ((a + 1) * (q.1.re - Real.sqrt κ * x) ^ 2 - Real.exp (2 * q.1.im)) /
        (greenLogNormSq κ q x) ^ 2 := by
  have hd : deriv (powerLogDensity κ p a q) = fun x =>
      powerLogDensity κ p a q x * (a * Real.sqrt κ * (q.1.re - Real.sqrt κ * x) /
        greenLogNormSq κ q x) := funext fun x => (powerLogDensity_spatial_derivative κ p a q x).deriv
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2 * (q.1.re - Real.sqrt κ * x) * (-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2 * q.1.im)) using 1 <;> try rfl
    simp
  have hcoef := (hX.const_mul (a * Real.sqrt κ)).div hN
    (greenLogNormSq_pos κ q x).ne'
  have hsecond := (powerLogDensity_spatial_derivative κ p a q x).mul hcoef
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq] at hsecond
  change HasDerivAt (fun y => powerLogDensity κ p a q y *
    (a * Real.sqrt κ * (q.1.re - Real.sqrt κ * y) / greenLogNormSq κ q y)) _ x at hsecond
  rw [hsecond.deriv]
  have hn := (greenLogNormSq_pos κ q x).ne'
  dsimp only [greenLogNormSq]
  generalize powerLogDensity κ p a q x = f
  generalize q.1.re - Real.sqrt κ * x = X
  generalize Real.exp (2 * q.1.im) = Y
  have hs := Real.sq_sqrt hκ
  generalize Real.sqrt κ = r at *
  rw [← hs]
  field_simp
  ring

lemma powerLogDensity_directional (κ p a : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) q) v =
      powerLogDensity κ p a q x * (p * v.2 +
        (a - p) * v.1.im - (a / 2) *
          ((2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
            2 * Real.exp (2 * q.1.im) * v.1.im) / greenLogNormSq κ q x)) := by
  have hzre : HasDerivAt (fun t : ℝ => (q + t • v).1.re) v.1.re 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_re, Complex.smul_re, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.re).const_add q.1.re
  have hzim : HasDerivAt (fun t : ℝ => (q + t • v).1.im) v.1.im 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_im, Complex.smul_im, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.im).const_add q.1.im
  have hj : HasDerivAt (fun t : ℝ => (q + t • v).2) v.2 0 := by
    simpa only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, id_eq, one_mul]
      using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add q.2
  have hN : HasDerivAt (fun t : ℝ => greenLogNormSq κ (q + t • v) x)
      (2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
        2 * Real.exp (2 * q.1.im) * v.1.im) 0 := by
    convert ((hzre.sub_const (Real.sqrt κ * x)).pow 2).add ((hzim.const_mul 2).exp) using 1 <;> try rfl
    simp only [zero_smul, add_zero, Nat.cast_ofNat]
    ring
  have hlog := hN.log (by simpa only [zero_smul, add_zero] using (greenLogNormSq_pos κ q x).ne')
  have hcalc := (((hj.const_mul (p)).const_add (-p * Real.log 2)).add
    (hzim.const_mul (a - p))).sub
      (hlog.const_mul (a / 2))
  have hline : HasDerivAt (fun t : ℝ => powerLogDensity κ p a (q + t • v) x)
      (powerLogDensity κ p a q x * (p * v.2 +
        (a - p) * v.1.im - (a / 2) *
          ((2 * (q.1.re - Real.sqrt κ * x) * v.1.re +
            2 * Real.exp (2 * q.1.im) * v.1.im) / greenLogNormSq κ q x))) 0 := by
    convert hcalc.exp using 1 <;> try rfl
    simp only [Pi.sub_apply, Pi.add_apply, zero_smul, add_zero]
    simp only [powerLogDensity]
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => powerLogDensity κ p a r x) :=
    (powerLogDensity_contDiff κ p a).comp (contDiff_id.prodMk contDiff_const)
  have haff : HasDerivAt (fun t : ℝ => q + t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (fun r : ℂ × ℝ => powerLogDensity κ p a r x)
      (fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) q) (q + (0 : ℝ) • v) := by
    simpa using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hchain := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hchain.unique hline

lemma powerLogDensity_pair_directional (κ p a : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun zz : (ℂ × ℝ) × ℝ => powerLogDensity κ p a zz.1 zz.2) (q, x) (v, 0) =
      fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) q v := by
  have hd := ((powerLogDensity_contDiff κ p a).differentiable (by simp)) (q, x)
  have hp := (hasFDerivAt_id (𝕜 := ℝ) q).prodMk (hasFDerivAt_const (𝕜 := ℝ) (E := ℂ × ℝ) x q)
  have hc := (hd.hasFDerivAt.comp q hp).fderiv
  have he := congrArg (fun D : (ℂ × ℝ) →L[ℝ] ℝ => D v) hc
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, id_eq, zero_apply] using he.symm

 

lemma exists_compact_power_field (κ p a R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : (ℂ × ℝ) × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ q x, ‖(q, x)‖ ≤ R → φ (q, x) = powerLogDensity κ p a q x) ∧
      (∀ q x, ‖(q, x)‖ ≤ R →
        fderiv ℝ φ (q, x) = fderiv ℝ (fun zz : (ℂ × ℝ) × ℝ => powerLogDensity κ p a zz.1 zz.2) (q, x)) ∧
      (∀ q x, ‖(q, x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (q, y)) x =
        iteratedDeriv 2 (powerLogDensity κ p a q) x) := by
  let b : ContDiffBump (0 : (ℂ × ℝ) × ℝ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let φ (zz : (ℂ × ℝ) × ℝ) : ℝ := b zz * powerLogDensity κ p a zz.1 zz.2
  have hnear (zz : (ℂ × ℝ) × ℝ) (hp : ‖zz‖ ≤ R) :
      φ =ᶠ[𝓝 zz] (fun r : (ℂ × ℝ) × ℝ => powerLogDensity κ p a r.1 r.2) := by
    have hball : zz ∈ Metric.ball (0 : (ℂ × ℝ) × ℝ) b.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      change ‖zz‖ < R + 1
      linarith
    filter_upwards [b.eventuallyEq_one_of_mem_ball hball] with r hr
    simp only [φ, hr, Pi.one_apply, one_mul]
  refine ⟨φ, b.contDiff.mul (powerLogDensity_contDiff κ p a), b.hasCompactSupport.mul_right,
    (fun q x h => (hnear (q, x) h).eq_of_nhds), ?_, ?_⟩
  · intro q x h
    exact (hnear (q, x) h).fderiv_eq
  · intro q x h
    have he := (hnear (q, x) h).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)
    exact he.iteratedDeriv_eq 2

 
lemma power_physical_generator (κ p a : ℝ) (hκ : 0 ≤ κ)
    (q : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) q)
      (physicalLogLoewnerField (Real.sqrt κ * x) q) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (powerLogDensity κ p a q) x =
      powerLogDensity κ p a q x *
        ((-4 * a + κ * a * (a + 1) / 2) * (q.1.re - Real.sqrt κ * x) ^ 2 +
          (4 * p - κ * a / 2) * Real.exp (2 * q.1.im)) /
        (greenLogNormSq κ q x) ^ 2 := by
  rw [powerLogDensity_directional, powerLogDensity_spatial_second κ p a hκ]
  obtain ⟨hr, hi, hj⟩ := physicalLogLoewnerField_components κ q x
  rw [hr, hi, hj]
  have hn := (greenLogNormSq_pos κ q x).ne'
  field_simp
  dsimp only [greenLogNormSq]
  ring

lemma powerLogDensity_radius_angle (κ p a η₀ : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    powerLogDensity κ p a q x =
      Real.exp (p * (logRadiusClock η₀ q - Real.log 2 - η₀)) *
        (logAngleSq κ q x) ^ (a / 2) := by
  rw [Real.rpow_def_of_pos (logAngleSq_pos κ q x), ← Real.exp_add]
  unfold logAngleSq
  rw [Real.log_div (Real.exp_ne_zero _) (greenLogNormSq_pos κ q x).ne', Real.log_exp]
  unfold powerLogDensity logRadiusClock
  congr 1
  ring

 

lemma green_weighted_power_generator (κ b : ℝ) (hκ : 0 < κ)
    (q : ℂ × ℝ) (x : ℝ) :
    (fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ (codimension κ)
        (greenExponent κ - b) r x) q)
      (physicalLogLoewnerField (Real.sqrt κ * x) q) +
      (1 / 2 : ℝ) * iteratedDeriv 2
        (powerLogDensity κ (codimension κ) (greenExponent κ - b) q) x =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) q x *
        logClockRate κ q x * (κ * b / 8) *
          (1 - (greenExponent κ - b) * ((logAngleSq κ q x)⁻¹ - 1)) := by
  rw [power_physical_generator κ _ _ hκ.le]
  unfold logClockRate logAngleSq
  have hn := (greenLogNormSq_pos κ q x).ne'
  have hy := Real.exp_ne_zero (2 * q.1.im)
  dsimp only [greenExponent, codimension, dimension]
  field_simp
  dsimp only [greenLogNormSq]
  ring

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SwallowLyapunov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swallow Lyapunov for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma bounded_cumulative_grid_error
    {Ω : Type*} [MeasurableSpace Ω] (G : ℝ → Ω → ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ u ω, |G u ω| ≤ C) (τ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    |(∫ u in (0 : ℝ)..(stopGrid n (τ ω) : ℝ), G u ω) -
       (∫ u in (0 : ℝ)..(τ ω : ℝ), G u ω)| ≤ C * (1 / ((n : ℝ) + 1)) := by
  have hle : (τ ω : ℝ) ≤ stopGrid n (τ ω) := (stopGrid_bounds n (τ ω)).1
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (bounded_time_section_intervalIntegrable 0 (τ ω) (τ ω).coe_nonneg G hG C hb ω)
    (bounded_time_section_intervalIntegrable (τ ω) (stopGrid n (τ ω)) hle G hG C hb ω)
  rw [← hs, add_sub_cancel_left]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (τ ω : ℝ)) (b := (stopGrid n (τ ω) : ℝ)) (C := C) (f := fun u => G u ω)
    (fun u _ => by simpa only [Real.norm_eq_abs] using hb u ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] at hh
  refine hh.trans (mul_le_mul_of_nonneg_left ?_ hC)
  have hu : (stopGrid n (τ ω) : ℝ) ≤ (τ ω : ℝ) + 1 / ((n : ℝ) + 1) := by
    exact_mod_cast (stopGrid_bounds n (τ ω)).2
  linarith

 

theorem brownian_time_field_stopped_dynkin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (K : ℝ≥0) (F a : ℝ≥0 → Ω → ℝ → ℝ)
    (hF : SmoothTimeBrownianField B hm K F a)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) :
    (∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P) = (∫ ω, F 0 ω (B 0 ω) ∂P) +
      ∫ ω, (∫ u in (0 : ℝ)..(τ ω : ℝ), brownianFieldDrift B F a u ω) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hτm := stopping_time_measurable_nnreal hτ
  let V (n : ℕ) (ω : Ω) := F (stopGrid n (τ ω)) ω (B (stopGrid n (τ ω)) ω)
  let H (n : ℕ) (ω : Ω) := ∫ u in (0 : ℝ)..(stopGrid n (τ ω) : ℝ), brownianFieldDrift B F a u ω
  let H₀ (ω : Ω) := ∫ u in (0 : ℝ)..(τ ω : ℝ), brownianFieldDrift B F a u ω
  have hVm (n : ℕ) : Measurable (V n) :=
    measurable_discrete_eval (fun k ω => F (stopGridTime n k) ω (B (stopGridTime n k) ω))
      (fun k => hF.eval_measurable _ 0 (by decide) (hm _)) (stopGridIndex_measurable hτm n)
  have hVb (n : ℕ) (ω : Ω) : |V n ω| ≤ (K : ℝ) := hF.bound _ ω _ 0 (by decide)
  have hVi (n : ℕ) : Integrable (V n) P :=
    Integrable.of_bound (hVm n).aestronglyMeasurable (K : ℝ)
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hVb n ω)
  have hGm := hF.generator_measurable hBm
  have hHjoint := cumulative_integral_measurable _ hGm
  have hHm (n : ℕ) : Measurable (H n) :=
    measurable_discrete_eval (fun k ω => ∫ u in (0 : ℝ)..(stopGridTime n k : ℝ), brownianFieldDrift B F a u ω)
      (fun k => hHjoint.comp measurable_prodMk_left) (stopGridIndex_measurable hτm n)
  have hH₀m : Measurable H₀ := hHjoint.comp (hτm.prodMk measurable_id)
  have hH₀b (ω : Ω) : |H₀ ω| ≤ 2 * (K : ℝ) * T := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (τ ω : ℝ)) (C := 2 * (K : ℝ))
      (f := fun u => brownianFieldDrift B F a u ω)
      (fun u _ => by simpa only [Real.norm_eq_abs] using hF.generator_bound u ω)
    simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg (τ ω).coe_nonneg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hb ω) (by positivity))
  have hH₀i : Integrable H₀ P := Integrable.of_bound hH₀m.aestronglyMeasurable _
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hH₀b ω)
  have hdiff (n : ℕ) (ω : Ω) : |H n ω - H₀ ω| ≤ (2 * (K : ℝ)) * (1 / ((n : ℝ) + 1)) :=
    bounded_cumulative_grid_error _ hGm _ (by positivity) hF.generator_bound τ n ω
  have hHb (n : ℕ) (ω : Ω) : |H n ω| ≤ 2 * (K : ℝ) * (T + 1) := by
    have hr : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hd := (hdiff n ω).trans (mul_le_mul_of_nonneg_left hr (by positivity))
    have ht : |H n ω| ≤ |H n ω - H₀ ω| + |H₀ ω| := by
      calc _ = |(H n ω - H₀ ω) + H₀ ω| := by rw [sub_add_cancel]
           _ ≤ _ := abs_add_le _ _
    nlinarith [hH₀b ω]
  have hHi (n : ℕ) : Integrable (H n) P := Integrable.of_bound (hHm n).aestronglyMeasurable _
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hHb n ω)
  have hmean (n : ℕ) : (∫ ω, V n ω ∂P) = (∫ ω, F 0 ω (B 0 ω) ∂P) + ∫ ω, H n ω ∂P := by
    have hh := brownian_compensated_grid_integral hB hm hBm hF τ hτ T hb n
    change (∫ ω, V n ω - H n ω ∂P) = _ at hh
    rw [integral_sub (hVi n) (hHi n)] at hh
    linarith
  have hlimV : Tendsto (fun n => ∫ ω, V n ω ∂P) atTop
      (𝓝 (∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (K : ℝ))
      (fun n => (hVm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hVb n ω)
    exact Eventually.of_forall fun ω => (hF.path_continuous hBc ω).continuousAt.tendsto.comp (stopGrid_tendsto (τ ω))
  have hlimH : Tendsto (fun n => ∫ ω, H n ω ∂P) atTop (𝓝 (∫ ω, H₀ ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 2 * (K : ℝ) * (T + 1))
      (fun n => (hHm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hHb n ω)
    apply Eventually.of_forall
    intro ω
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg) (fun n => by simpa only [Real.dist_eq] using hdiff n ω)
    simpa only [mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (K : ℝ))
  have he := hlimH.const_add (∫ ω, F 0 ω (B 0 ω) ∂P)
  simp_rw [← hmean] at he
  exact tendsto_nhds_unique hlimV he

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StoppedPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopped Power for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma continuous_powerLogGenerator (κ p α : ℝ) :
    Continuous (fun q : (ℂ × ℝ) × ℝ => powerLogGenerator κ p α q.1 q.2) := by
  have hD := (powerLogDensity_contDiff κ p α).continuous
  have hN : Continuous (fun q : (ℂ × ℝ) × ℝ => greenLogNormSq κ q.1 q.2) := by
    unfold greenLogNormSq
    fun_prop
  unfold powerLogGenerator
  apply Continuous.div (hD.mul (by fun_prop)) (hN.pow 2)
  intro q
  exact pow_ne_zero 2 (greenLogNormSq_pos κ q.1 q.2).ne'

lemma measurable_powerLogGenerator_comp {X : Type*} [MeasurableSpace X]
    (κ p α : ℝ) (q : X → ℂ × ℝ) (b : X → ℝ)
    (hq : Measurable q) (hb : Measurable b) :
    Measurable (fun x => powerLogGenerator κ p α (q x) (b x)) := by
  have hh := (continuous_powerLogGenerator κ p α).measurable.comp (hq.prodMk hb)
  dsimp only [Function.comp_def] at hh
  with_reducible exact hh

lemma compact_power_drift
    (κ p α : ℝ) (hκ : 0 ≤ κ) (lo hi : ℝ) (hle : lo ≤ hi)
    (φ : (ℂ × ℝ) × ℝ → ℝ) (q : ℂ × ℝ) (x : ℝ)
    (hφD : fderiv ℝ φ (q, x) =
      fderiv ℝ (fun r : (ℂ × ℝ) × ℝ => powerLogDensity κ p α r.1 r.2) (q, x))
    (hφ2 : iteratedDeriv 2 (fun y => φ (q, y)) x =
      iteratedDeriv 2 (powerLogDensity κ p α q) x)
    (hq : q.1.im ∈ Icc lo hi) :
    fderiv ℝ φ (q, x)
        (clippedLogLoewnerField lo hi hle (Real.sqrt κ * x) q, 0) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (fun y => φ (q, y)) x =
        powerLogGenerator κ p α q x := by
  rw [hφD, hφ2, powerLogDensity_pair_directional,
    clippedLogLoewnerField_eq_physical lo hi hle _ _ hq]
  exact power_physical_generator κ p α hκ q x

 

theorem ClippedLogSolution.stopped_power_dynkin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 ≤ κ) (p α : ℝ)
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) :
    Integrable (fun ω => powerLogDensity κ p α (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, powerLogDensity κ p α (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
        powerLogDensity κ p α q₀ 0 +
        ∫ ω, (∫ t in (0 : ℝ)..(τ ω : ℝ),
          powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_power_field κ p α R hR
  obtain ⟨L₀, K₀, hL₀, _⟩ := clippedLogLoewnerField_bounds lo hi hle
  let V (t : ℝ) (ω : Ω) :=
    clippedLogLoewnerField lo hi hle (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)
  have hBr : Measurable (fun p : ℝ × Ω => Real.sqrt κ * B p.1.toNNReal p.2) :=
    (hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      measurable_snd)).const_mul _
  have hpair : Measurable (fun p : ℝ × Ω =>
      (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)) := hBr.prodMk c.measurable
  have hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2) := by
    change Measurable ((fun p : ℝ × (ℂ × ℝ) => clippedLogLoewnerField lo hi hle p.1 p.2) ∘
      (fun p : ℝ × Ω => (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)))
    exact (continuous_clippedLogLoewnerField lo hi hle).measurable.comp hpair
  have hVb (t : ℝ) (ω : Ω) : ‖V t ω‖ ≤ (max c.L L₀ : ℝ≥0) :=
    (hL₀ _ _).trans (by exact_mod_cast le_max_right c.L L₀)
  obtain ⟨K, hfield⟩ := compact_state_smooth_brownian_field B hm c.Q V (max c.L L₀)
    c.measurable c.adapted (fun ω => (c.lipschitz ω).weaken (le_max_left _ _)) hVm hVb
    (fun t ω ht => c.derivative ω t ht) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (c.Q t ω, x)
  let a (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (c.Q t ω, x) (V t ω, 0)
  have hgen (ω : Ω) (t : ℝ) (ht : t ∈ Icc 0 (τ ω : ℝ)) :
      brownianFieldDrift B F a t ω =
        powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω) := by
    have ht' : t.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr ht.2
    obtain ⟨hball, hlo, hhi⟩ := hinside ω t.toNNReal ht'
    have he : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.1
    change fderiv ℝ φ (c.Q (t.toNNReal : ℝ) ω, B t.toNNReal ω)
      (V (t.toNNReal : ℝ) ω, 0) + _ = _
    dsimp only [V]
    rw [Real.toNNReal_coe]
    have hh := compact_power_drift κ p α hκ lo hi hle φ _ _
      (hφD _ _ hball) (hφ2 _ _ hball) ⟨hlo, hhi⟩
    simpa only [F, he] using hh
  have hopt := brownian_time_field_stopped_dynkin hB hm hBm hBc K F a hfield τ hτ T hb
  have hτm := stopping_time_measurable_nnreal hτ
  have hBmτ : Measurable (fun ω => B (τ ω) ω) := hBm.comp (hτm.prodMk measurable_id)
  have hQmτ : Measurable (fun ω => c.Q (τ ω) ω) :=
    c.measurable.comp ((NNReal.continuous_coe.measurable.comp hτm).prodMk measurable_id)
  have hfm : Measurable (fun ω => F (τ ω) ω (B (τ ω) ω)) :=
    hφ.continuous.measurable.comp (hQmτ.prodMk hBmτ)
  have hfi : Integrable (fun ω => F (τ ω) ω (B (τ ω) ω)) P := by
    apply Integrable.of_bound hfm.aestronglyMeasurable (K : ℝ)
    exact Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, iteratedDeriv_zero] using
        hfield.bound (τ ω) ω (B (τ ω) ω) 0 (by decide)
  have hfeq (ω : Ω) : F (τ ω) ω (B (τ ω) ω) =
      powerLogDensity κ p α (c.Q (τ ω) ω) (B (τ ω) ω) :=
    hφeq _ _ (hinside ω (τ ω) le_rfl).1
  refine ⟨hfi.congr (Eventually.of_forall hfeq), ?_⟩
  calc
    _ = ∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (hfeq ω).symm)
    _ = (∫ ω, F 0 ω (B 0 ω) ∂P) +
        ∫ ω, (∫ t in (0 : ℝ)..(τ ω : ℝ), brownianFieldDrift B F a t ω) ∂P := hopt
    _ = _ := by
      congr 1
      · calc
          _ = ∫ _, powerLogDensity κ p α q₀ 0 ∂P := by
            apply integral_congr_ae
            filter_upwards [hB.eval_zero_ae_eq_zero] with ω hB0
            change φ (c.Q 0 ω, B 0 ω) = _
            have hh : ‖(c.Q 0 ω, B 0 ω)‖ ≤ R := by
              simpa only [NNReal.coe_zero] using (hinside ω 0 zero_le).1
            rw [hφeq _ _ hh, c.initial ω, hB0]
          _ = _ := by simp
      · apply integral_congr_ae
        exact Eventually.of_forall fun ω => intervalIntegral.integral_congr
          (fun t ht => hgen ω t (by simpa only [uIcc_of_le (τ ω).coe_nonneg] using ht))

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma stopping_paste_after
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : Filtration ℝ≥0 mΩ)
    {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime f (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime f (fun ω => (τ ω : WithTop ℝ≥0)))
    (hle : ∀ ω, σ ω ≤ τ ω) {A : Set Ω}
    (hA : MeasurableSet[hσ.measurableSpace] A) :
    IsStoppingTime f (fun ω => ((if ω ∈ A then τ ω else σ ω : ℝ≥0) : WithTop ℝ≥0)) := by
  classical
  intro t
  have he : {ω | ((if ω ∈ A then τ ω else σ ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
      (A ∩ {ω | (σ ω : WithTop ℝ≥0) ≤ t} ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ t}) ∪
        (Aᶜ ∩ {ω | (σ ω : WithTop ℝ≥0) ≤ t}) := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_union, mem_inter_iff, mem_compl_iff]
    split_ifs with h
    · simp only [h, true_and, not_true_eq_false, false_and, or_false]
      exact ⟨fun ht => ⟨(hle ω).trans ht, ht⟩, fun ht => ht.2⟩
    · simp [h]
  rw [he]
  exact ((hA.2 t).inter (hτ t)).union ((hA.compl).2 t)

 

theorem ClippedLogSolution.stopped_green_bounded_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (η₀ u : ℝ) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T)
    (hin : ∀ ω t, t ≤ σ ω → logRadiusClock η₀ (c.Q t ω) ≤ u ∧
      lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) :
    Integrable (fun ω => greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω) ∂P) =
        greenLogDensity κ q₀ 0 := by
  classical
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hex (n : ℕ) : ∃ β : Ω → ℝ≥0,
      IsStoppingTime f (fun ω => (β ω : WithTop ℝ≥0)) ∧
      (∀ ω, β ω ≤ T) ∧
      (∀ ω t, t ≤ β ω → |B t ω| ≤ (n : ℝ) + 1) ∧
      (∀ ω, β ω < T → |B (β ω) ω| = (n : ℝ) + 1) := by
    let D (t : ℝ≥0) (ω : Ω) := (n : ℝ) + 1 - |B t ω|
    obtain ⟨β, hβ, hbβ, hβin, _, hβbd⟩ := first_margin_stopping f D
      (fun t => by
        let : MeasurableSpace Ω := f t
        exact (hBa t).abs.const_sub ((n : ℝ) + 1))
      (fun ω => continuous_const.sub (hBc ω).abs)
      (fun ω => by simpa [D, hB0 ω] using (show 0 ≤ (n : ℝ) + 1 by positivity)) T
    refine ⟨β, hβ, hbβ, ?_, ?_⟩
    · intro ω t ht
      exact sub_nonneg.mp (hβin ω t ht)
    · intro ω ht
      exact (sub_eq_zero.mp (hβbd ω ht)).symm
  choose β hβ hbβ hβin hβbd using hex
  let σn (n : ℕ) (ω : Ω) := min (σ ω) (β n ω)
  have hsn (n : ℕ) : IsStoppingTime f (fun ω => (σn n ω : WithTop ℝ≥0)) := by
    simpa only [σn, WithTop.coe_min] using hσ.min (hβ n)
  have hsnb (n : ℕ) (ω : Ω) : σn n ω ≤ T := (min_le_left _ _).trans (hb ω)
  have hsin (n : ℕ) (ω : Ω) (t : ℝ≥0) (ht : t ≤ σn n ω) :
      logRadiusClock η₀ (c.Q t ω) ≤ u ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi :=
    hin ω t (ht.trans (min_le_left _ _))
  have hmean (n : ℕ) :
      Integrable (fun ω => greenLogDensity κ (c.Q (σn n ω) ω) (B (σn n ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (c.Q (σn n ω) ω) (B (σn n ω) ω) ∂P) = greenLogDensity κ q₀ 0 := by
    let R := max (‖q₀‖ + c.L * T) ((n : ℝ) + 1)
    have hR : 0 ≤ R := (by positivity : 0 ≤ (n : ℝ) + 1).trans (le_max_right _ _)
    apply c.stopped_green hB hBm hBc hκ hκ8 R hR (σn n) (hsn n) T (hsnb n)
    intro ω t ht
    refine ⟨?_, (hsin n ω t ht).2⟩
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    exact ⟨(c.norm_le ω t T (ht.trans (hsnb n ω))).trans (le_max_left _ _),
      (hβin n ω t (ht.trans (min_le_right _ _))).trans (le_max_right _ _)⟩
  have hstable (ω : Ω) : ∀ᶠ n : ℕ in atTop, σn n ω = σ ω := by
    obtain ⟨N, hN⟩ := continuous_path_bounded_by_nat (fun t => B t ω) (hBc ω) T
    filter_upwards [eventually_ge_atTop N] with n hn
    have hbn : β n ω = T := by
      apply le_antisymm (hbβ n ω)
      by_contra h
      have hlt : β n ω < T := lt_of_not_ge h
      have hh := hN (β n ω) (hbβ n ω)
      rw [hβbd n ω hlt] at hh
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    dsimp only [σn]
    rw [hbn, min_eq_left (hb ω)]
  let K := Real.exp (codimension κ * (u - Real.log 2 - η₀))
  have hbound (n : ℕ) (ω : Ω) :
      ‖greenLogDensity κ (c.Q (σn n ω) ω) (B (σn n ω) ω)‖ ≤ K := by
    rw [Real.norm_eq_abs, abs_of_nonneg (greenLogDensity_nonneg _ _ _)]
    exact greenLogDensity_le_radius κ η₀ u hκ hκ8 _ _ (hsin n ω _ le_rfl).1
  have hlim (ω : Ω) : Tendsto
      (fun n => greenLogDensity κ (c.Q (σn n ω) ω) (B (σn n ω) ω)) atTop
      (𝓝 (greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω))) :=
    tendsto_const_nhds.congr' ((hstable ω).mono fun n hn => by dsimp only; rw [hn])
  have hσm := stopping_time_measurable_nnreal hσ
  have hQm := c.measurable.comp ((measurable_coe_nnreal_real.comp hσm).prodMk measurable_id)
  have hbm := hBm.comp (hσm.prodMk measurable_id)
  have hmeas : Measurable (fun ω => greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω)) :=
    (greenLogDensity_contDiff κ).continuous.measurable.comp (hQm.prodMk hbm)
  have hi : Integrable (fun ω => greenLogDensity κ (c.Q (σ ω) ω) (B (σ ω) ω)) P := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable K
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (greenLogDensity_nonneg _ _ _)]
    exact greenLogDensity_le_radius κ η₀ u hκ hκ8 _ _ (hin ω _ le_rfl).1
  refine ⟨hi, ?_⟩
  apply tendsto_nhds_unique (tendsto_integral_of_dominated_convergence (fun _ => K)
    (fun n => (hmean n).1.aestronglyMeasurable) (integrable_const K)
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim))
  simpa only [(hmean _).2] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => greenLogDensity κ q₀ 0) atTop (𝓝 _))



end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma exists_brownian_compact_stops
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T) :
    ∃ σn : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (σn n ω : WithTop ℝ≥0))) ∧
      (∀ n ω, σn n ω ≤ σ ω) ∧
      (∀ n ω t, t ≤ σn n ω → |B t ω| ≤ (n : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ n : ℕ in atTop, σn n ω = σ ω) := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hex (n : ℕ) : ∃ β : Ω → ℝ≥0,
      IsStoppingTime f (fun ω => (β ω : WithTop ℝ≥0)) ∧
      (∀ ω, β ω ≤ T) ∧
      (∀ ω t, t ≤ β ω → |B t ω| ≤ (n : ℝ) + 1) ∧
      (∀ ω, β ω < T → |B (β ω) ω| = (n : ℝ) + 1) := by
    let D (t : ℝ≥0) (ω : Ω) := (n : ℝ) + 1 - |B t ω|
    obtain ⟨β, hβ, hbβ, hβin, _, hβbd⟩ := first_margin_stopping f D
      (fun t => by
        let : MeasurableSpace Ω := f t
        exact (hBa t).abs.const_sub ((n : ℝ) + 1))
      (fun ω => continuous_const.sub (hBc ω).abs)
      (fun ω => by simpa [D, hB0 ω] using (show 0 ≤ (n : ℝ) + 1 by positivity)) T
    refine ⟨β, hβ, hbβ, ?_, ?_⟩
    · intro ω t ht
      exact sub_nonneg.mp (hβin ω t ht)
    · intro ω ht
      exact (sub_eq_zero.mp (hβbd ω ht)).symm
  choose β hβ hbβ hβin hβbd using hex
  let σn (n : ℕ) (ω : Ω) := min (σ ω) (β n ω)
  refine ⟨σn, ?_, fun n ω => min_le_left _ _, ?_, ?_⟩
  · intro n
    simpa only [σn, WithTop.coe_min] using hσ.min (hβ n)
  · intro n ω t ht
    exact hβin n ω t (ht.trans (min_le_right _ _))
  · intro ω
    obtain ⟨N, hN⟩ := continuous_path_bounded_by_nat (fun t => B t ω) (hBc ω) T
    filter_upwards [eventually_ge_atTop N] with n hn
    have hbn : β n ω = T := by
      apply le_antisymm (hbβ n ω)
      by_contra h
      have hlt : β n ω < T := lt_of_not_ge h
      have hh := hN (β n ω) (hbβ n ω)
      rw [hβbd n ω hlt] at hh
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    dsimp only [σn]
    rw [hbn, min_eq_left (hb ω)]

lemma bounded_stopped_cumulative_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (G : ℝ → Ω → ℝ) (hGm : Measurable (Function.uncurry G))
    (σ τ : Ω → ℝ≥0) (hτm : Measurable τ) (hle : ∀ ω, τ ω ≤ σ ω)
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ ω t, 0 ≤ t → t ≤ (σ ω : ℝ) → |G t ω| ≤ C) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω) P ∧
      ∀ ω, |∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω| ≤ C * T := by
  have hm : Measurable (fun ω => ∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω) :=
    (cumulative_integral_measurable G hGm).comp (hτm.prodMk measurable_id)
  have hbnd (ω : Ω) : |∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω| ≤ C * T := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (τ ω : ℝ)) (C := C) (f := fun t => G t ω) (fun t ht => by
        have htt : t ∈ Ioc (0 : ℝ) (τ ω : ℝ) := by simpa only [uIoc_of_le (τ ω).coe_nonneg] using ht
        simpa only [Real.norm_eq_abs] using hG ω t htt.1.le (htt.2.trans (by exact_mod_cast hle ω)))
    simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg (τ ω).coe_nonneg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (hle ω).trans (hb ω)) hC)
  exact ⟨Integrable.of_bound hm.aestronglyMeasurable _
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbnd ω), hbnd⟩

lemma integral_tendsto_stopped_eval
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (F : ℝ≥0 → Ω → ℝ) (σn : ℕ → Ω → ℝ≥0) (σ : Ω → ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (fun ω => F (σn n ω) ω) P)
    (K : ℝ) (hb : ∀ n ω, |F (σn n ω) ω| ≤ K)
    (hstable : ∀ ω, ∀ᶠ n : ℕ in atTop, σn n ω = σ ω) :
    Tendsto (fun n => ∫ ω, F (σn n ω) ω ∂P) atTop (𝓝 (∫ ω, F (σ ω) ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => K) hm (integrable_const K)
    (fun n => Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb n ω)
  apply Eventually.of_forall
  intro ω
  exact tendsto_const_nhds.congr' ((hstable ω).mono fun n hn => by dsimp only; rw [hn])

lemma integral_identity_of_stable_stops
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (F H : ℝ≥0 → Ω → ℝ) (σn : ℕ → Ω → ℝ≥0) (σ : Ω → ℝ≥0)
    (hstable : ∀ ω, ∀ᶠ n : ℕ in atTop, σn n ω = σ ω)
    (A K C : ℝ)
    (hmean : ∀ n, Integrable (fun ω => F (σn n ω) ω) P ∧
      (∫ ω, F (σn n ω) ω ∂P) = A + ∫ ω, H (σn n ω) ω ∂P)
    (hFi : Integrable (fun ω => F (σ ω) ω) P)
    (hHim : AEStronglyMeasurable (fun ω => H (σ ω) ω) P)
    (hHnm : ∀ n, AEStronglyMeasurable (fun ω => H (σn n ω) ω) P)
    (hFb : ∀ n ω, |F (σn n ω) ω| ≤ K)
    (hHb : ∀ n ω, |H (σn n ω) ω| ≤ C)
    (hHbound : ∀ ω, |H (σ ω) ω| ≤ C) :
    Integrable (fun ω => F (σ ω) ω) P ∧
    Integrable (fun ω => H (σ ω) ω) P ∧
      (∫ ω, F (σ ω) ω ∂P) = A + ∫ ω, H (σ ω) ω ∂P := by
  refine ⟨hFi, Integrable.of_bound hHim C
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hHbound ω), ?_⟩
  have hlimF := integral_tendsto_stopped_eval F σn σ
    (fun n => (hmean n).1.aestronglyMeasurable) K hFb hstable
  have hlimH := integral_tendsto_stopped_eval H σn σ hHnm C hHb hstable
  have he := hlimH.const_add A
  simp_rw [← (hmean _).2] at he
  exact tendsto_nhds_unique hlimF he

lemma ClippedLogSolution.stopped_power_dynkin_compact_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 ≤ κ) (p α : ℝ) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T)
    (hin : ∀ ω t, t ≤ σ ω → (c.Q t ω).1.im ∈ Icc lo hi)
    (N : ℝ) (hN : 0 ≤ N) (hcap : ∀ ω t, t ≤ σ ω → |B t ω| ≤ N) :
    Integrable (fun ω => powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω)) P ∧
      (∫ ω, powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω) ∂P) =
        powerLogDensity κ p α q₀ 0 + ∫ ω, (∫ t in (0 : ℝ)..(σ ω : ℝ),
          powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) ∂P := by
  let R := max (‖q₀‖ + c.L * T) N
  have hR : 0 ≤ R := hN.trans (le_max_right _ _)
  apply c.stopped_power_dynkin hB hBm hBc hκ p α R hR σ hσ T hb
  intro ω t ht
  refine ⟨?_, hin ω t ht⟩
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
  exact ⟨(c.norm_le ω t T (ht.trans (hb ω))).trans (le_max_left _ _),
    (hcap ω t ht).trans (le_max_right _ _)⟩

lemma ClippedLogSolution.stopped_power_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (p α : ℝ) (σ : Ω → ℝ≥0) (hσm : Measurable σ) (K : ℝ)
    (hval : ∀ ω, |powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω)| ≤ K) :
    Integrable (fun ω => powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω)) P := by
  have hQm := c.measurable.comp ((measurable_coe_nnreal_real.comp hσm).prodMk measurable_id)
  have hbm := hBm.comp (hσm.prodMk measurable_id)
  have hWm := (powerLogDensity_contDiff κ p α).continuous.measurable.comp (hQm.prodMk hbm)
  exact Integrable.of_bound hWm.aestronglyMeasurable K
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hval ω)

lemma ClippedLogSolution.power_generator_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (p α : ℝ) :
    Measurable (fun q : ℝ × Ω => powerLogGenerator κ p α (c.Q q.1 q.2) (B q.1.toNNReal q.2)) := by
  have ht : Measurable (fun q : ℝ × Ω => q.1.toNNReal) :=
    continuous_real_toNNReal.measurable.comp measurable_fst
  have hb : Measurable (fun q : ℝ × Ω => B q.1.toNNReal q.2) :=
    hBm.comp (ht.prodMk measurable_snd)
  exact measurable_powerLogGenerator_comp κ p α
    (fun q : ℝ × Ω => c.Q q.1 q.2) (fun q : ℝ × Ω => B q.1.toNNReal q.2)
    c.measurable hb

lemma ClippedLogSolution.stopped_power_cumulative_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (p α : ℝ) (σ τ : Ω → ℝ≥0) (hτm : Measurable τ) (hleτ : ∀ ω, τ ω ≤ σ ω)
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hdrift : ∀ ω t, t ≤ σ ω → |powerLogGenerator κ p α (c.Q t ω) (B t ω)| ≤ C) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(τ ω : ℝ),
      powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) P ∧
      (∀ ω, |∫ t in (0 : ℝ)..(τ ω : ℝ),
        powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)| ≤ C * T) := by
  let G (t : ℝ) (ω : Ω) := powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)
  have hGm : Measurable (Function.uncurry G) := c.power_generator_measurable hBm p α
  have hGb (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (htσ : t ≤ (σ ω : ℝ)) : |G t ω| ≤ C := by
    have hh := hdrift ω t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr htσ)
    simpa only [G, Real.coe_toNNReal t ht] using hh
  exact bounded_stopped_cumulative_integrable G hGm σ τ hτm hleτ T hb C hC hGb

 

theorem ClippedLogSolution.stopped_power_dynkin_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hκ : 0 ≤ κ) (p α : ℝ) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, σ ω ≤ T)
    (hin : ∀ ω t, t ≤ σ ω → (c.Q t ω).1.im ∈ Icc lo hi)
    (K C : ℝ) (hC : 0 ≤ C)
    (hval : ∀ ω t, t ≤ σ ω → |powerLogDensity κ p α (c.Q t ω) (B t ω)| ≤ K)
    (hdrift : ∀ ω t, t ≤ σ ω → |powerLogGenerator κ p α (c.Q t ω) (B t ω)| ≤ C) :
    Integrable (fun ω => powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω)) P ∧
    Integrable (fun ω => ∫ t in (0 : ℝ)..(σ ω : ℝ),
      powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) P ∧
      (∫ ω, powerLogDensity κ p α (c.Q (σ ω) ω) (B (σ ω) ω) ∂P) =
        powerLogDensity κ p α q₀ 0 +
        ∫ ω, (∫ t in (0 : ℝ)..(σ ω : ℝ),
          powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨σn, hsn, hsle, hsB, hstable⟩ := exists_brownian_compact_stops B hm hBc hB0 σ hσ T hb
  have hsnb (n : ℕ) (ω : Ω) : σn n ω ≤ T := (hsle n ω).trans (hb ω)
  let W (τ : Ω → ℝ≥0) (ω : Ω) := powerLogDensity κ p α (c.Q (τ ω) ω) (B (τ ω) ω)
  let G (t : ℝ) (ω : Ω) := powerLogGenerator κ p α (c.Q t ω) (B t.toNNReal ω)
  let H (τ : Ω → ℝ≥0) (ω : Ω) := ∫ t in (0 : ℝ)..(τ ω : ℝ), G t ω
  have hmean (n : ℕ) : Integrable (W (σn n)) P ∧
      (∫ ω, W (σn n) ω ∂P) = powerLogDensity κ p α q₀ 0 + ∫ ω, H (σn n) ω ∂P := by
    exact c.stopped_power_dynkin_compact_cap hB hBm hBc hκ p α (σn n) (hsn n)
      T (hsnb n) (fun ω t ht => hin ω t (ht.trans (hsle n ω))) ((n : ℝ) + 1)
      (by positivity) (hsB n)
  have hH (τ : Ω → ℝ≥0) (hτm : Measurable τ) (hτ : ∀ ω, τ ω ≤ σ ω) :
      Integrable (H τ) P ∧ ∀ ω, |H τ ω| ≤ C * T :=
    c.stopped_power_cumulative_integrable hBm p α σ τ hτm hτ T hb C hC hdrift
  have hσm := stopping_time_measurable_nnreal hσ
  have hWi : Integrable (W σ) P := c.stopped_power_integrable hBm p α σ hσm K
    (fun ω => hval ω (σ ω) le_rfl)
  exact integral_identity_of_stable_stops
    (fun t ω => powerLogDensity κ p α (c.Q t ω) (B t ω))
    (fun t ω => ∫ u in (0 : ℝ)..(t : ℝ), G u ω) σn σ hstable
    (powerLogDensity κ p α q₀ 0) K (C * T) hmean hWi
    (hH σ hσm (fun _ => le_rfl)).1.aestronglyMeasurable
    (fun n => (hH (σn n) (stopping_time_measurable_nnreal (hsn n)) (hsle n)).1.aestronglyMeasurable)
    (fun n ω => hval ω (σn n ω) (hsle n ω))
    (fun n => (hH (σn n) (stopping_time_measurable_nnreal (hsn n)) (hsle n)).2)
    (hH σ hσm (fun _ => le_rfl)).2

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SwallowExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swallow Exit for chordal SLE. -/

section


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma logCoordinates_snd (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0) :
    (logLoewnerCoordinates G z t).2 = Real.log ‖deriv (G t) z‖ := by
  simp only [logLoewnerCoordinates, Real.toNNReal_coe]

lemma greenLogNormSq_logCoordinates (κ b : ℝ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0)
    (hy : 0 < (G t z).im) :
    greenLogNormSq κ (logLoewnerCoordinates G z t) b =
      Complex.normSq (G t z - ((Real.sqrt κ * b : ℝ) : ℂ)) := by
  have he : Real.exp (2 * Real.log (G t z).im) = (G t z).im ^ 2 := by
    rw [show 2 * Real.log (G t z).im = Real.log (G t z).im + Real.log (G t z).im by ring,
      Real.exp_add, Real.exp_log hy, pow_two]
  rw [greenLogNormSq, logCoordinates_re, logCoordinates_im, he]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, pow_two]

lemma logAngleSq_logCoordinates (κ b : ℝ) (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ≥0)
    (hy : 0 < (G t z).im) :
    logAngleSq κ (logLoewnerCoordinates G z t) b =
      (Real.sin (Complex.arg (G t z - ((Real.sqrt κ * b : ℝ) : ℂ)))) ^ 2 := by
  rw [logAngleSq, greenLogNormSq_logCoordinates κ b G z t hy, logCoordinates_im,
    Complex.sin_arg, Complex.normSq_eq_norm_sq, div_pow]
  congr 1
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [show 2 * Real.log (G t z).im = Real.log (G t z).im + Real.log (G t z).im by ring,
    Real.exp_add, Real.exp_log hy, pow_two]

lemma greenLogDensity_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (κ b : ℝ) (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t)
    (hUb : U t = Real.sqrt κ * b) :
    greenLogDensity κ (logLoewnerCoordinates G z t) b = greenDensity κ U γ G t z := by
  have hy := h.imag_positive t z hz
  have hj := h.derivative_norm_positive hU t z hz
  have hn : 0 < ‖G t z - ((Real.sqrt κ * b : ℝ) : ℂ)‖ := by
    apply norm_pos_iff.mpr
    simpa only [hUb] using h.centered_ne_zero t z hz
  have hs : 0 < Real.sin (Complex.arg (G t z - (U t : ℂ))) := by
    rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero, hUb]
    exact div_pos hy hn
  have hR := h.fullRadius_positive hU t z hz
  have hlogR : Real.log (fullRadius G t z) =
      Real.log 2 + Real.log (G t z).im - Real.log ‖deriv (G t) z‖ := by
    rw [fullRadius, Real.log_div (mul_ne_zero (by norm_num) hy.ne') hj.ne',
      Real.log_mul (by norm_num) hy.ne']
  have hlogS : Real.log (Real.sin (Complex.arg (G t z - (U t : ℂ)))) =
      Real.log (G t z).im - Real.log ‖G t z - ((Real.sqrt κ * b : ℝ) : ℂ)‖ := by
    rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero, hUb,
      Real.log_div hy.ne' hn.ne']
  rw [greenDensity, ite_eq_left hz, Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hs,
    ← Real.exp_add, hlogR, hlogS, greenLogDensity, logCoordinates_im, logCoordinates_snd,
    greenLogNormSq_logCoordinates κ b G z t hy, Complex.normSq_eq_norm_sq, Real.log_pow]
  congr 1
  push_cast
  ring

lemma greenLogDensity_initial (κ : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    greenLogDensity κ (initialLogCoordinates z) 0 = initialGreen κ z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by
    have hp : 0 < z.im := hz
    intro he; simp only [he, Complex.zero_im, lt_self_iff_false] at hp)
  have hs : 0 < Real.sin (Complex.arg z) := by rw [Complex.sin_arg]; exact div_pos hz hn
  have he : Real.exp (2 * Real.log z.im) = z.im ^ 2 := by
    rw [show 2 * Real.log z.im = Real.log z.im + Real.log z.im by ring,
      Real.exp_add, Real.exp_log hz, pow_two]
  have hN : greenLogNormSq κ (initialLogCoordinates z) 0 = Complex.normSq z := by
    simp only [greenLogNormSq, initialLogCoordinates, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_self, add_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, he,
      Complex.normSq_apply, pow_two]
  rw [initialGreen, Real.rpow_def_of_pos (mul_pos (by norm_num) hz), Real.rpow_def_of_pos hs,
    ← Real.exp_add, Real.log_mul (by norm_num) hz.ne', Complex.sin_arg, Real.log_div hz.ne' hn.ne']
  rw [greenLogDensity, hN, Complex.normSq_eq_norm_sq, Real.log_pow]
  simp only [initialLogCoordinates, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero,
    Nat.cast_ofNat]
  congr 1
  ring

end SLEExactGauge
end


section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
 
theorem exists_measurable_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (C t)) ∧ IsBrownianReal C P ∧
      (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) := by
  let b (n k : ℕ) : Ω → ℝ :=
    (hB.aemeasurable (stopGridTime n k)).mk (B (stopGridTime n k))
  have hb (n k : ℕ) : Measurable (b n k) := (hB.aemeasurable _).measurable_mk
  have heq : ∀ᵐ ω ∂P, ∀ n k, b n k ω = B (stopGridTime n k) ω := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact (hB.aemeasurable _).ae_eq_mk.symm
  let C (t : ℝ≥0) (ω : Ω) : ℝ :=
    limUnder atTop (fun n => b n (stopGridIndex n t) ω)
  have hm (t : ℝ≥0) : Measurable (C t) :=
    (StronglyMeasurable.limUnder (fun n => (hb n _).stronglyMeasurable)).measurable
  have hCB : ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω := by
    filter_upwards [hB.cont, heq] with ω hω heqω
    intro t
    change limUnder atTop (fun n => b n (stopGridIndex n t) ω) = B t ω
    simp_rw [heqω]
    exact (hω.continuousAt.tendsto.comp (stopGrid_tendsto t)).limUnder_eq
  refine ⟨C, hm, ⟨?_, ?_⟩, hCB⟩
  · exact hB.toIsPreBrownianReal.congr (fun t => hCB.mono fun ω hω => (hω t).symm)
  · filter_upwards [hB.cont, hCB] with ω hω heqω
    simpa only [heqω] using hω

 

theorem exists_continuous_measurable_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ,
      Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2) ∧
      (∀ ω, Continuous (fun t => C t ω)) ∧ IsBrownianReal C P ∧
      (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) := by
  classical
  obtain ⟨V, hVm, hV, hVB⟩ := exists_measurable_brownian_version hB
  let N := toMeasurable P {ω | ¬ Continuous (fun t => V t ω)}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN : P N = 0 := by
    rw [show N = toMeasurable P {ω | ¬ Continuous (fun t => V t ω)} from rfl,
      measure_toMeasurable]
    exact ae_iff.mp hV.cont
  let C (t : ℝ≥0) (ω : Ω) := if ω ∈ N then (0 : ℝ) else V t ω
  have hCm (t) : Measurable (C t) := measurable_const.piecewise hNm (hVm t)
  have hCc (ω) : Continuous (fun t => C t ω) := by
    by_cases hω : ω ∈ N
    · simpa only [C, ite_eq_left hω] using (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
    · have hv : Continuous (fun t => V t ω) := by
        by_contra hh
        exact hω (subset_toMeasurable P _ hh)
      simpa only [C, ite_eq_right hω] using hv
  have hCV : ∀ᵐ ω ∂P, ∀ t, C t ω = V t ω := by
    filter_upwards [show ∀ᵐ ω ∂P, ω ∉ N from (ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hN))] with ω hω
    intro t
    simp only [C, ite_eq_right hω]
  have hCB : ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω := by
    filter_upwards [hCV, hVB] with ω hω hω'
    exact fun t => (hω t).trans (hω' t)
  refine ⟨C, measurable_uncurry_of_continuous_of_measurable hCc hCm, hCc, ?_, hCB⟩
  exact ⟨hV.toIsPreBrownianReal.congr (fun t => hCV.mono fun ω hω => (hω t).symm),
    Eventually.of_forall hCc⟩

 

theorem exists_regular_brownian_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ C : ℝ≥0 → Ω → ℝ,
      Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2) ∧
      (∀ ω, Continuous (fun t => C t ω)) ∧ (∀ ω, C 0 ω = 0) ∧
      IsBrownianReal C P ∧ (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) := by
  obtain ⟨V, hVm, hVc, hV, hVB⟩ := exists_continuous_measurable_brownian_version hB
  let C (t : ℝ≥0) (ω : Ω) := V t ω - V 0 ω
  have hV0m : Measurable (V 0) := hVm.comp (measurable_const.prodMk measurable_id)
  have hCm : Measurable (fun q : ℝ≥0 × Ω => C q.1 q.2) :=
    hVm.sub (hV0m.comp measurable_snd)
  have hCc (ω : Ω) : Continuous (fun t => C t ω) := (hVc ω).sub continuous_const
  have hCV : ∀ᵐ ω ∂P, ∀ t, C t ω = V t ω := by
    filter_upwards [hV.eval_zero_ae_eq_zero] with ω h0
    intro t
    simp only [C, h0, sub_zero]
  refine ⟨C, hCm, hCc, fun ω => sub_self _, ?_, ?_⟩
  · exact ⟨hV.toIsPreBrownianReal.congr (fun t => hCV.mono fun ω hω => (hω t).symm),
      Eventually.of_forall hCc⟩
  · filter_upwards [hCV, hVB] with ω hω hω'
    exact fun t => (hω t).trans (hω' t)
end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_NearRealContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near Real Contraction for chordal SLE. -/

section


section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma upper_mobius_norm_lt_one {v w : ℂ} (hv : 0 < v.im) (hw : 0 < w.im) :
    ‖(v - w) / (v - star w)‖ < 1 := by
  have hd : v - star w ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hh
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have he : ‖v - w‖ ^ 2 < ‖v - star w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_pos hv hw]
  nlinarith [norm_nonneg (v - w), norm_nonneg (v - star w)]

 

lemma radius_of_halfplane_map {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball z r))
    (hm : MapsTo f (ball z r) upperHalfPlane) (hf : deriv f z ≠ 0) :
    r ≤ 2 * (f z).im / ‖deriv f z‖ := by
  have hz : z ∈ ball z r := mem_ball_self hr
  have hy : 0 < (f z).im := hm hz
  have hden (w : ℂ) (hw : w ∈ ball z r) : f w - star (f z) ≠ 0 := by
    intro he
    have hx := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hx
    have hwyo : 0 < (f w).im := hm hw
    linarith
  let g := fun w => (f w - f z) / (f w - star (f z))
  have hg0 : g z = 0 := by dsimp [g]; rw [sub_self, zero_div]
  have hgd : DifferentiableOn ℂ g (ball z r) :=
    (hd.sub_const _).div (hd.sub_const _) hden
  have hgm : MapsTo g (ball z r) (closedBall (g z) 1) := by
    intro w hw
    rw [hg0, mem_closedBall_zero_iff]
    exact (upper_mobius_norm_lt_one (hm hw) hy).le
  have hdz : HasDerivAt f (deriv f z) z := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hgg : deriv g z = deriv f z / (f z - star (f z)) := by
    calc
      deriv g z = (deriv f z * (f z - star (f z)) - (f z - f z) * deriv f z) /
          (f z - star (f z)) ^ 2 :=
        ((hdz.sub_const (f z)).div (hdz.sub_const (star (f z))) (hden z hz)).deriv
      _ = _ := by
        rw [sub_self, zero_mul, sub_zero, pow_two, mul_div_mul_right _ _ (hden z hz)]
  have hn : ‖f z - star (f z)‖ = 2 * (f z).im := by
    rw [Complex.star_def, Complex.sub_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hy), Complex.norm_I, mul_one]
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hgm hr
  rw [hgg, norm_div, hn] at hh
  have hn' := norm_pos_iff.mpr hf
  apply (le_div_iff₀ hn').mpr
  have hq := (div_le_div_iff₀ (mul_pos (by norm_num) hy) hr).mp hh
  nlinarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma ball_subset_survivingDomain {γ : ℝ≥0 → ℂ} {t : ℝ≥0} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : z ∈ survivingDomain γ t)
    (hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 t)) :
    ball z r ⊆ survivingDomain γ t := by
  have hcc := (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr) hfree
  intro w hw
  refine ⟨hfree hw, ?_⟩
  rw [← connectedComponentIn_eq (hcc hw)]
  exact hz.2

lemma ball_subset_upperHalfPlane {z : ℂ} {r : ℝ} (hr : r ≤ z.im) :
    ball z r ⊆ upperHalfPlane := by
  intro w hw
  have hh : ‖w - z‖ < r := mem_ball_iff_norm.mp hw
  have hi := Complex.abs_im_le_norm (w - z)
  simp only [Complex.sub_im] at hi
  change 0 < w.im
  have hx := neg_le_abs (w.im - z.im)
  linarith

 

lemma IsCapacityTwoWitness.trace_approach_of_radius_lt
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) (r : ℝ)
    (hr : 0 < r) (hy : r ≤ z.im) (hR : fullRadius G t z < r) :
    ∃ s ∈ Icc 0 t, dist (γ s) z < r := by
  by_contra hn
  have hn' (s : ℝ≥0) (hs : s ∈ Icc 0 t) : r ≤ dist (γ s) z :=
    le_of_not_gt (fun he => hn ⟨s, hs, he⟩)
  have hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 t) := by
    intro w hw
    refine ⟨ball_subset_upperHalfPlane hy hw, ?_⟩
    rintro ⟨s, hs, rfl⟩
    exact not_lt_of_ge (hn' s hs) (mem_ball.mp hw)
  have hb := ball_subset_survivingDomain hr hz hfree
  have hd : DifferentiableOn ℂ (G t) (ball z r) := (h.2.2.2.1 t).mono hb
  have hm : MapsTo (G t) (ball z r) upperHalfPlane := fun w hw => h.2.2.2.2.2.1 t (hb hw)
  have hf : deriv (G t) z ≠ 0 := norm_pos_iff.mp (h.derivative_norm_positive hU t z hz)
  exact not_lt_of_ge (radius_of_halfplane_map hr hd hm hf) hR

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.trace_mem_closure_surviving
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (s t : ℝ≥0) (hst : s ≤ t) :
    γ t ∈ closure (survivingDomain γ s) := by
  have hfmap := h.2.2.2.2.2.2.1 t
  have htip := h.2.2.2.2.2.2.2.2.2.2.2.2 t
  apply mem_closure_of_tendsto htip
  filter_upwards [self_mem_nhdsWithin] with y hy
  apply survivingDomain_antitone γ hst
  apply hfmap
  change 0 < (((U t : ℝ) : ℂ) + (y : ℂ) * Complex.I).im
  simpa using hy

lemma IsCapacityTwoWitness.surviving_of_free_ball_future_tip
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (s t : ℝ≥0) (hst : s ≤ t)
    (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 s))
    (htip : γ t ∈ ball z r) : z ∈ survivingDomain γ s := by
  obtain ⟨w, hwb, hw⟩ := mem_closure_iff.mp (h.trace_mem_closure_surviving s t hst)
    (ball z r) isOpen_ball htip
  have hcc := (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr) hfree
  refine ⟨hfree (mem_ball_self hr), ?_⟩
  rw [connectedComponentIn_eq (hcc hwb)]
  exact hw.2

end SLEExactGauge
end


section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 m} {τ : Ω → ℝ≥0}



omit m in
lemma grid_partition_union (A : Set Ω) (n : ℕ) :
    (⋃ k : ℕ, A ∩ {ω | stopGridIndex n (τ ω) = k}) = A := by
  ext ω
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

omit m in
lemma grid_partition_disjoint (A : Set Ω) (n : ℕ) :
    Pairwise (fun i j : ℕ => Disjoint (A ∩ {ω | stopGridIndex n (τ ω) = i}) (A ∩ {ω | stopGridIndex n (τ ω) = j})) := by
  intro i j hij
  apply disjoint_left.mpr
  intro ω hi hj
  exact hij (hi.2.symm.trans hj.2)



end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_BrownianStrongMarkov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Brownian Strong Markov for chordal SLE. -/

section


section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma derivative_close_of_cauchy {f : ℂ → ℂ} {U : Set ℂ} {b : ℂ} {r : ℝ}
    (hr : 0 < r) (hU : IsOpen U) (hd : DifferentiableOn ℂ f U)
    (hinc : closedBall b r ⊆ U)
    (hbound : ∀ w ∈ closedBall b r, ‖deriv f w‖ ≤ 2 * ‖deriv f b‖) :
    ∀ w ∈ closedBall b (r / 8), ‖deriv f w - deriv f b‖ ≤ ‖deriv f b‖ / 2 := by
  have hdr := hd.deriv hU
  have hsmall : closedBall b (r / 8) ⊆ closedBall b r := closedBall_subset_closedBall (by linarith)
  have hsecond (w : ℂ) (hw : w ∈ closedBall b (r / 8)) :
      ‖deriv (deriv f) w‖ ≤ 4 * ‖deriv f b‖ / r := by
    have hs : closedBall w (r / 2) ⊆ closedBall b r := by
      intro z hz
      apply mem_closedBall.mpr
      have hw' := mem_closedBall.mp hw
      have hz' := mem_closedBall.mp hz
      exact (dist_triangle z w b).trans (by linarith)
    have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < r / 2)
      (hdr.diffContOnCl_ball (hs.trans hinc))
      (fun z hz => hbound z (hs (sphere_subset_closedBall hz)))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  intro w hw
  have hh := (convex_closedBall b (r / 8)).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => hdr.differentiableAt (hU.mem_nhds (hinc (hsmall hz)))) hsecond
    (mem_closedBall_self (by positivity : 0 ≤ r / 8)) hw
  have hn : ‖w - b‖ ≤ r / 8 := mem_closedBall_iff_norm.mp hw
  calc
    ‖deriv f w - deriv f b‖ ≤ (4 * ‖deriv f b‖ / r) * ‖w - b‖ := hh
    _ ≤ (4 * ‖deriv f b‖ / r) * (r / 8) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ‖deriv f b‖ / 2 := by field_simp; ring

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma disk_image_of_deriv_close {f f' : ℂ → ℂ} {b a : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : a ≠ 0)
    (hd : ∀ z ∈ closedBall b r, HasDerivAt f (f' z) z)
    (hb : ∀ z ∈ closedBall b r, ‖f' z / a - 1‖ ≤ 1 / 2) :
    closedBall (f b) (‖a‖ * r / 2) ⊆ f '' closedBall b r := by
  let g : ℂ → ℂ := fun z => f z / a
  have hl : LipschitzOnWith (1 / 2 : ℝ≥0) (fun z => g z - z) (closedBall b r) := by
    apply (convex_closedBall b r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun z => f' z / a - 1)
    · intro z hz
      exact (((hd z hz).div_const a).sub (hasDerivAt_id z)).hasDerivWithinAt
    · intro z hz
      exact_mod_cast hb z hz
  have hl' : ApproximatesLinearOn g (ContinuousLinearMap.id ℂ ℂ) (closedBall b r) (1 / 2) := by
    apply LipschitzOnWith.approximatesLinearOn
    exact hl
  have hs := hl'.surjOn_closedBall_of_nonlinearRightInverse
    (ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse hr (Subset.refl _)
  have hs' : SurjOn g (closedBall b r) (closedBall (g b) (r / 2)) := by
    norm_num [ContinuousLinearEquiv.toNonlinearRightInverse] at hs
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ring_nf
  intro y hy
  have hy' : y / a ∈ closedBall (g b) (r / 2) := by
    rw [mem_closedBall_iff_norm] at hy ⊢
    change ‖y / a - f b / a‖ ≤ r / 2
    rw [← sub_div, norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr ha)).mpr
    nlinarith
  obtain ⟨z, hz, he⟩ := hs' hy'
  exact ⟨z, hz, (div_left_inj' ha).mp he⟩

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma bloch_disk {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1)) :
    ∃ b ∈ ball (0 : ℂ) 1,
      closedBall (f b) (‖deriv f 0‖ / 64) ⊆ f '' ball 0 1 := by
  have hzero : (0 : ℂ) ∈ closedBall 0 (1 / 2 : ℝ) := mem_closedBall_self (by norm_num)
  have hinc : closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  by_cases h0 : deriv f 0 = 0
  · refine ⟨0, mem_ball_self (by norm_num), ?_⟩
    simp only [h0, norm_zero, zero_div, closedBall_zero, singleton_subset_iff]
    exact mem_image_of_mem f (mem_ball_self (by norm_num))
  have hd0 : 0 < ‖deriv f 0‖ := norm_pos_iff.mpr h0
  let Φ : ℂ → ℝ := fun z => (1 / 2 - ‖z‖) * ‖deriv f z‖
  have hc : ContinuousOn Φ (closedBall 0 (1 / 2 : ℝ)) :=
    (continuousOn_const.sub continuous_norm.continuousOn).mul
      ((hd.deriv isOpen_ball).continuousOn.mono hinc).norm
  obtain ⟨b, hb, hmax⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2 : ℝ)).exists_isMaxOn
    ⟨0, hzero⟩ hc
  have hM : ‖deriv f 0‖ / 2 ≤ (1 / 2 - ‖b‖) * ‖deriv f b‖ := by
    have hh := hmax hzero
    simpa [Φ, norm_zero, mul_comm, div_eq_mul_inv] using hh
  have hb' : ‖b‖ ≤ 1 / 2 := mem_closedBall_zero_iff.mp hb
  have hab : 0 < ‖deriv f b‖ := by
    by_contra hn
    have hh : ‖deriv f b‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [hh, mul_zero] at hM
    linarith
  have hmargin : 0 < 1 / 2 - ‖b‖ := by
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hab.le
    linarith
  let r : ℝ := (1 / 2 - ‖b‖) / 2
  have hr : 0 < r := div_pos hmargin (by norm_num)
  have hsub : closedBall b r ⊆ closedBall 0 (1 / 2 : ℝ) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    have hw' : ‖w - b‖ ≤ r := mem_closedBall_iff_norm.mp hw
    have hnorm : ‖w‖ ≤ ‖w - b‖ + ‖b‖ := by simpa [norm_sub_rev, add_comm] using norm_le_insert b w
    dsimp [r] at hw'
    linarith
  have hbound (w : ℂ) (hw : w ∈ closedBall b r) : ‖deriv f w‖ ≤ 2 * ‖deriv f b‖ := by
    have hh := hmax (hsub hw)
    change (1 / 2 - ‖w‖) * ‖deriv f w‖ ≤ (1 / 2 - ‖b‖) * ‖deriv f b‖ at hh
    have hw' : ‖w - b‖ ≤ r := mem_closedBall_iff_norm.mp hw
    have hnorm : ‖w‖ ≤ ‖w - b‖ + ‖b‖ := by simpa [norm_sub_rev, add_comm] using norm_le_insert b w
    have hm : r ≤ 1 / 2 - ‖w‖ := by dsimp [r] at *; linarith
    have he : 1 / 2 - ‖b‖ = 2 * r := by dsimp [r]; ring
    have hprod := mul_le_mul_of_nonneg_right hm (norm_nonneg (deriv f w))
    rw [he] at hh
    nlinarith
  have hclose := derivative_close_of_cauchy hr isOpen_ball hd (hsub.trans hinc) hbound
  have hsmall : closedBall b (r / 8) ⊆ closedBall b r := closedBall_subset_closedBall (by linarith)
  have himage := disk_image_of_deriv_close (f := f) (f' := deriv f) (a := deriv f b)
    (by positivity : 0 ≤ r / 8) (norm_pos_iff.mp hab)
    (fun w hw => (hd.differentiableAt (isOpen_ball.mem_nhds (hinc (hsub (hsmall hw))))).hasDerivAt)
    (by
      intro w hw
      rw [← div_self (norm_pos_iff.mp hab), ← sub_div, norm_div]
      exact (div_le_iff₀ hab).mpr (by simpa [div_eq_mul_inv, mul_comm] using hclose w hw))
  refine ⟨b, hinc hb, ?_⟩
  have hlower : ‖deriv f 0‖ / 64 ≤ ‖deriv f b‖ * (r / 8) / 2 := by
    dsimp [r]
    nlinarith
  exact (closedBall_subset_closedBall hlower).trans
    (himage.trans (image_mono (hsmall.trans (hsub.trans hinc))))

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma hasDerivAt_log_lift {g h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hh : ContinuousOn h U)
    (he : EqOn (Complex.exp ∘ h) g U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt h (deriv g z / g z) z := by
  have hgz : g z ≠ 0 := by rw [← he hz]; exact Complex.exp_ne_zero _
  have hdz := (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hcx := hh.continuousAt (hU.mem_nhds hz)
  have hdisc : ∀ᶠ w in 𝓝 z, ‖h w - h z‖ < Real.pi := by
    have hc : ContinuousAt (fun w => ‖h w - h z‖) z := (hcx.sub continuousAt_const).norm
    exact hc (Iio_mem_nhds (by simpa using Real.pi_pos))
  have hlocal : (fun w => Complex.log (g w / g z) + h z) =ᶠ[𝓝 z] h := by
    filter_upwards [hU.mem_nhds hz, hdisc] with w hw hw'
    have him : |(h w - h z).im| < Real.pi := (Complex.abs_im_le_norm _).trans_lt hw'
    rw [← he hw, ← he hz]
    change Complex.log (Complex.exp (h w) / Complex.exp (h z)) + h z = h w
    rw [← Complex.exp_sub, Complex.log_exp (by linarith [(abs_lt.mp him).1])
      (le_of_lt (abs_lt.mp him).2)]
    ring
  have hlog := (hdz.div_const (g z)).clog (by simp [hgz])
  have hf : HasDerivAt (fun w => Complex.log (g w / g z) + h z) (deriv g z / g z) z := by
    simpa [hgz] using hlog.add_const (h z)
  exact hf.congr_of_eventuallyEq hlocal.symm

lemma differentiableOn_log_lift {g h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (hh : ContinuousOn h U)
    (he : EqOn (Complex.exp ∘ h) g U) : DifferentiableOn ℂ h U :=
  fun _ hz => (hasDerivAt_log_lift hU hg hh he hz).differentiableAt.differentiableWithinAt

lemma exists_holomorphic_log_on_ball {g : ℂ → ℂ} {b : ℂ} {r : ℝ}
    (hr : 0 < r) (hg : DifferentiableOn ℂ g (ball b r))
    (h0 : ∀ z ∈ ball b r, g z ≠ 0) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball b r) ∧
      EqOn (Complex.exp ∘ h) g (ball b r) ∧
      ∀ z ∈ ball b r, deriv h z = deriv g z / g z := by
  let := (convex_ball b r).contractibleSpace ⟨b, mem_ball_self hr⟩
  obtain ⟨h, hh, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (by change SimplyConnectedSpace (ball b r); infer_instance) isOpen_ball hg.continuousOn
    (by rintro ⟨z, hz, he⟩; exact h0 z hz he)
  exact ⟨h, differentiableOn_log_lift isOpen_ball hg hh he, he,
    fun z hz => (hasDerivAt_log_lift isOpen_ball hg hh he hz).deriv⟩

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma univalent_omitted_value_bound {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (a : ℂ) (ha : a ∉ f '' ball 0 1) :
    ‖deriv f 0‖ ≤ (128 * Real.pi) * ‖f 0 - a‖ := by
  have hnon (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : f z - a ≠ 0 := by
    intro he
    exact ha ⟨z, hz, sub_eq_zero.mp he⟩
  have hz0 : (0 : ℂ) ∈ ball 0 1 := mem_ball_self (by norm_num)
  obtain ⟨h, hhd, he, hhder⟩ := exists_holomorphic_log_on_ball (by norm_num : (0 : ℝ) < 1)
    (hd.sub_const a) hnon
  obtain ⟨b, hb, hball⟩ := bloch_disk hhd
  have hbound : ‖deriv h 0‖ < 128 * Real.pi := by
    by_contra hn
    have hn' : 128 * Real.pi ≤ ‖deriv h 0‖ := le_of_not_gt hn
    have hw : h b + 2 * Real.pi * Complex.I ∈ closedBall (h b) (‖deriv h 0‖ / 64) := by
      rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_mul, norm_mul,
        norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
      linarith
    obtain ⟨z, hz, hzh⟩ := hball hw
    have hfe : f z - a = f b - a := by
      calc
        f z - a = Complex.exp (h z) := (he hz).symm
        _ = Complex.exp (h b) := by rw [hzh]; exact Complex.exp_periodic (h b)
        _ = f b - a := he hb
    have hzb : z = b := hi hz hb (sub_left_inj.mp hfe)
    rw [hzb] at hzh
    have him := congrArg Complex.im hzh
    norm_num [Complex.add_im, Complex.mul_im, Complex.mul_re] at him
  have hd0 := (hd.differentiableAt (isOpen_ball.mem_nhds hz0)).hasDerivAt
  have hdsub : deriv (fun z => f z - a) 0 = deriv f 0 := (hd0.sub_const a).deriv
  rw [hhder 0 hz0, hdsub, norm_div] at hbound
  exact ((div_lt_iff₀ (norm_pos_iff.mpr (hnon 0 hz0))).mp hbound).le

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_DiskHalfPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk Half Plane for chordal SLE. -/

section
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma disk_denominator_ne {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) : 1 - ζ ≠ 0 := by
  intro he
  have hh := mem_ball_zero_iff.mp hζ
  rw [← sub_eq_zero.mp he] at hh
  simp at hh

lemma diskToHalfPlane_im (w ζ : ℂ) :
    (diskToHalfPlane w ζ).im = w.im * (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := by
  simp only [diskToHalfPlane, Complex.div_im, Complex.sub_im, Complex.sub_re, Complex.mul_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.one_im,
    Complex.one_re, Complex.normSq_apply]
  ring

lemma diskToHalfPlane_maps {w : ℂ} (hw : 0 < w.im) :
    MapsTo (diskToHalfPlane w) (ball 0 1) upperHalfPlane := by
  intro ζ hζ
  have hn : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have hn2 : Complex.normSq ζ < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
  have hp : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.mpr (disk_denominator_ne hζ)
  change 0 < (diskToHalfPlane w ζ).im
  rw [diskToHalfPlane_im]
  exact div_pos (mul_pos hw (sub_pos.mpr hn2)) hp

lemma diskToHalfPlane_differentiable (w : ℂ) :
    DifferentiableOn ℂ (diskToHalfPlane w) (ball 0 1) :=
  ((differentiableOn_id.const_mul (star w)).const_sub w).div
    (differentiableOn_id.const_sub 1) (fun _ hζ => disk_denominator_ne hζ)

lemma diskToHalfPlane_deriv_zero (w : ℂ) :
    HasDerivAt (diskToHalfPlane w) (w - star w) 0 := by
  have hh := ((hasDerivAt_const (0 : ℂ) w).sub ((hasDerivAt_id 0).const_mul (star w))).div
    ((hasDerivAt_const (0 : ℂ) 1).sub (hasDerivAt_id 0)) (by norm_num : (1 : ℂ) - 0 ≠ 0)
  convert hh using 1 <;> first | rfl | (dsimp; ring)

lemma diskToHalfPlane_injOn {w : ℂ} (hw : 0 < w.im) : InjOn (diskToHalfPlane w) (ball 0 1) := by
  intro ζ hζ ξ hξ he
  have hc := (div_eq_div_iff (disk_denominator_ne hζ) (disk_denominator_ne hξ)).mp he
  have hp : (w - star w) * (ζ - ξ) = 0 := by linear_combination hc
  have hn : w - star w ≠ 0 := by
    intro he
    have him := congrArg Complex.im he
    simp at him
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hn)

lemma norm_sub_conj_of_im_pos {w : ℂ} (hw : 0 < w.im) : ‖w - star w‖ = 2 * w.im := by
  rw [Complex.star_def, Complex.sub_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) hw), Complex.norm_I, mul_one]

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.radius_le_omitted_distance
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (_hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (a : ℂ) (ha : a ∉ survivingDomain γ t) :
    fullRadius G t z ≤ (128 * Real.pi) * dist z a := by
  have hγ := h.1
  rcases h with ⟨_, hγ0, hγim, hG, hF, hGmap, hFmap, hinv, hinv', h0, hode, hnorm, htip⟩
  have hy : 0 < (G t z).im := hGmap t hz
  have hg := ((hG t).differentiableAt ((isOpen_survivingDomain hγ t).mem_nhds hz)).hasDerivAt
  have hf := ((hF t).differentiableAt (isOpen_upperHalfPlane.mem_nhds (hGmap t hz))).hasDerivAt
  have hident : (fun v => F t (G t v)) =ᶠ[𝓝 z] (fun v => v) := by
    filter_upwards [(isOpen_survivingDomain hγ t).mem_nhds hz] with v hv
    exact hinv t v hv
  have hprod : deriv (F t) (G t z) * deriv (G t) z = 1 :=
    ((hf.comp z hg).congr_of_eventuallyEq hident.symm).unique (hasDerivAt_id z)
  have hnormprod : ‖deriv (F t) (G t z)‖ * ‖deriv (G t) z‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hgpos : 0 < ‖deriv (G t) z‖ := by
    by_contra hn
    have he : ‖deriv (G t) z‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [he, mul_zero] at hnormprod
    norm_num at hnormprod
  let f : ℂ → ℂ := F t ∘ diskToHalfPlane (G t z)
  have hfd : DifferentiableOn ℂ f (ball 0 1) :=
    (hF t).comp (diskToHalfPlane_differentiable _) (diskToHalfPlane_maps hy)
  have hfi : InjOn f (ball 0 1) := by
    intro v hv w hw he
    apply diskToHalfPlane_injOn hy hv hw
    have he' := congrArg (G t) he
    change G t (F t (diskToHalfPlane (G t z) v)) = G t (F t (diskToHalfPlane (G t z) w)) at he'
    rwa [hinv' t _ (diskToHalfPlane_maps hy hv), hinv' t _ (diskToHalfPlane_maps hy hw)] at he'
  have hfimage : f '' ball 0 1 ⊆ survivingDomain γ t := by
    rintro _ ⟨v, hv, rfl⟩
    exact hFmap t (diskToHalfPlane_maps hy hv)
  have hfv0 : f 0 = z := by simp only [f, Function.comp_apply, diskToHalfPlane_zero, hinv t z hz]
  have hfq : HasDerivAt (F t) (deriv (F t) (G t z)) (diskToHalfPlane (G t z) 0) := by simpa using hf
  have hfder : deriv f 0 = deriv (F t) (G t z) * (G t z - star (G t z)) :=
    (hfq.comp 0 (diskToHalfPlane_deriv_zero _)).deriv
  have hfrad : ‖deriv f 0‖ = fullRadius G t z := by
    rw [hfder, norm_mul, norm_sub_conj_of_im_pos hy, fullRadius]
    apply (eq_div_iff hgpos.ne').mpr
    nlinarith [hnormprod]
  have hh := univalent_omitted_value_bound hfd hfi a (fun ha' => ha (hfimage ha'))
  rwa [hfrad, hfv0, ← dist_eq_norm] at hh

lemma IsCapacityTwoWitness.radius_le_past_distance
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (s : ℝ≥0) (hs : s ≤ t) :
    fullRadius G t z ≤ (128 * Real.pi) * dist z (γ s) :=
  h.radius_le_omitted_distance hU t z hz (γ s)
    (fun hw => hw.1.2 ⟨s, ⟨zero_le, hs⟩, rfl⟩)

end SLEExactGauge
end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.radius_approach_of_trace_approach
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (T : ℝ≥0) (hT : dist (γ T) z < r) :
    ∃ s : ℝ≥0, s ≤ T ∧ z ∈ survivingDomain γ s ∧ fullRadius G s z < (128 * Real.pi) * r := by
  let ρ : ℝ := (r + dist (γ T) z) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith [(dist_nonneg : 0 ≤ dist (γ T) z)]
  have hρr : ρ < r := by dsimp [ρ]; linarith
  have hTρ : dist (γ T) z < ρ := by dsimp [ρ]; linarith
  have hγ : Continuous γ := h.1
  let S : Set ℝ≥0 := Icc 0 T ∩ {s | dist (γ s) z ≤ ρ}
  have hSc : IsCompact S := isCompact_Icc.inter_right (isClosed_le (hγ.dist continuous_const) continuous_const)
  have hSn : S.Nonempty := ⟨T, ⟨⟨zero_le, le_rfl⟩, hTρ.le⟩⟩
  obtain ⟨τ, hτ, hmin⟩ := hSc.exists_isMinOn hSn continuous_id.continuousOn
  have hτ0 : 0 < τ := by
    by_contra hn
    have he : τ = 0 := le_antisymm (le_of_not_gt hn) zero_le
    have hh := hτ.2
    change dist (γ τ) z ≤ ρ at hh
    rw [he, h.2.1, dist_zero_left] at hh
    have hz := Complex.im_le_norm z
    linarith
  have hprior (s : ℝ≥0) (hs : s < τ) : ρ < dist (γ s) z := by
    by_contra hn
    have hmem : s ∈ S := ⟨⟨zero_le, hs.le.trans hτ.1.2⟩, le_of_not_gt hn⟩
    exact not_le_of_gt hs (hmin hmem)
  have hτcl : τ ∈ closure (Ioo (0 : ℝ≥0) τ) := by
    rw [closure_Ioo (ne_of_lt hτ0)]
    exact ⟨hτ0.le, le_rfl⟩
  have hO : IsOpen {s : ℝ≥0 | dist (γ s) z < r} := isOpen_lt (hγ.dist continuous_const) continuous_const
  have hτO : τ ∈ {s : ℝ≥0 | dist (γ s) z < r} := lt_of_le_of_lt hτ.2 hρr
  obtain ⟨s, hsnear, hs⟩ := mem_closure_iff.mp hτcl _ hO hτO
  have hsT : s ≤ T := hs.2.le.trans hτ.1.2
  have hfree : ball z ρ ⊆ upperHalfPlane \ (γ '' Icc 0 s) := by
    intro w hw
    refine ⟨ball_subset_upperHalfPlane (hρr.le.trans hy) hw, ?_⟩
    rintro ⟨u, hu, rfl⟩
    exact not_lt_of_ge (hprior u (hu.2.trans_lt hs.2)).le (mem_ball.mp hw)
  have hsz := h.surviving_of_free_ball_future_tip s T hsT z ρ hρ hfree (mem_ball.mpr hTρ)
  refine ⟨s, hsT, hsz, ?_⟩
  have hh := h.radius_le_past_distance hU s z hsz s le_rfl
  rw [dist_comm z (γ s)] at hh
  exact hh.trans_lt (mul_lt_mul_of_pos_left hsnear (mul_pos (by norm_num) Real.pi_pos))

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma logRadiusClock_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t) :
    logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) =
      Real.log ((2 * z.im) / fullRadius G t z) := by
  have hy := h.imag_positive t z hz
  have hj := h.derivative_norm_positive hU t z hz
  have hR := h.fullRadius_positive hU t z hz
  rw [logRadiusClock, logCoordinates_im, logCoordinates_snd,
    Real.log_div (mul_ne_zero (by norm_num) hz.1.1.ne') hR.ne',
    Real.log_mul (by norm_num) hz.1.1.ne', fullRadius,
    Real.log_div (mul_ne_zero (by norm_num) hy.ne') hj.ne',
    Real.log_mul (by norm_num) hy.ne']
  ring

lemma fullRadius_eq_logClock
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t) :
    fullRadius G t z = (2 * z.im) *
      Real.exp (-logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t)) := by
  rw [logRadiusClock_logCoordinates hU h z t hz, Real.exp_neg,
    Real.exp_log (div_pos (mul_pos (by norm_num) hz.1.1) (h.fullRadius_positive hU t z hz))]
  field_simp [(show 0 < z.im from hz.1.1).ne']

lemma fullRadius_level_iff_logClock
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t) (u : ℝ) :
    fullRadius G t z = (2 * z.im) * Real.exp (-u) ↔
      logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) = u := by
  rw [fullRadius_eq_logClock hU h z t hz,
    mul_right_inj' (mul_ne_zero (by norm_num) hz.1.1.ne'), Real.exp_eq_exp, neg_inj]

lemma IsCapacityTwoWitness.radius_clock_strictMonoOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (T : ℝ≥0) (hz : z ∈ survivingDomain γ T) :
    StrictMonoOn (fun t : ℝ => Real.log ((2 * z.im) / fullRadius G t.toNNReal z))
      (Icc 0 (T : ℝ)) := by
  have hd := loewner_radius_clock_derivative hU h T z hz
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
  intro t ht
  have hy := h.imag_positive t.toNNReal z (h.live_at_real_time T z hz t (interior_subset ht).2)
  have hn := Complex.normSq_pos.mpr (h.centered_ne_zero t.toNNReal z
    (h.live_at_real_time T z hz t (interior_subset ht).2))
  positivity

lemma live_radius_unique
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (s t : ℝ≥0) (hs : z ∈ survivingDomain γ s)
    (ht : z ∈ survivingDomain γ t) (he : fullRadius G s z = fullRadius G t z) : s = t := by
  have hmax : z ∈ survivingDomain γ (max s t) := by
    rcases le_total s t with hh | hh
    · simpa only [max_eq_right hh] using ht
    · simpa only [max_eq_left hh] using hs
  have hi := h.radius_clock_strictMonoOn hU z (max s t) hmax
  apply NNReal.coe_injective
  apply hi.injOn
  · exact ⟨s.coe_nonneg, by exact_mod_cast le_max_left s t⟩
  · exact ⟨t.coe_nonneg, by exact_mod_cast le_max_right s t⟩
  · simp only [Real.toNNReal_coe, he]

lemma live_clock_le_time
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (s t : ℝ≥0) (hs : z ∈ survivingDomain γ s)
    (_ht : z ∈ survivingDomain γ t)
    (he : Real.log ((2 * z.im) / fullRadius G s z) ≤
      Real.log ((2 * z.im) / fullRadius G t z)) : s ≤ t := by
  by_contra hn
  have hts := not_le.mp hn
  have hi := h.radius_clock_strictMonoOn hU z s hs
  have hh := hi (show (t : ℝ) ∈ Icc 0 (s : ℝ) from ⟨t.coe_nonneg, by exact_mod_cast hts.le⟩)
    (show (s : ℝ) ∈ Icc 0 (s : ℝ) from ⟨s.coe_nonneg, le_rfl⟩) (by exact_mod_cast hts)
  simp only [Real.toNNReal_coe] at hh
  exact (not_lt_of_ge he) hh

lemma live_angleSq_lower_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (T : ℝ≥0) (hz : z ∈ survivingDomain γ T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, t ≤ T →
      δ ≤ (Real.sin (Complex.arg (G t z - (U t : ℂ)))) ^ 2 := by
  let A (t : ℝ) := (Real.sin (Complex.arg (G t.toNNReal z - (U t.toNNReal : ℂ)))) ^ 2
  have hn (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
      ‖G t.toNNReal z - (U t.toNNReal : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (h.centered_ne_zero _ z (h.live_at_real_time T z hz t ht.2))
  have hc : ContinuousOn A (Icc 0 (T : ℝ)) := by
    have hGc := h.time_continuousOn T z hz
    have hUc := Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)
    have hZc := hGc.sub hUc.continuousOn
    simp only [A, Complex.sin_arg]
    exact ((Complex.continuous_im.comp_continuousOn hZc).div hZc.norm hn).pow 2
  obtain ⟨t, ht, hmin⟩ := (isCompact_Icc : IsCompact (Icc 0 (T : ℝ))).exists_isMinOn
    ⟨0, le_rfl, T.coe_nonneg⟩ hc
  have hp : 0 < A t := by
    have hy := h.imag_positive t.toNNReal z (h.live_at_real_time T z hz t ht.2)
    dsimp only [A]
    rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact sq_pos_of_pos (div_pos hy (lt_of_le_of_ne (norm_nonneg _) (hn t ht).symm))
  refine ⟨A t, hp, fun s hs => ?_⟩
  have hh := hmin (show (s : ℝ) ∈ Icc 0 (T : ℝ) from ⟨s.coe_nonneg, by exact_mod_cast hs⟩)
  change A t ≤ A (s : ℝ) at hh
  simpa only [A, Real.toNNReal_coe] using hh

lemma radiusLevelTime_eq_of_live_level
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (t : ℝ≥0) (ht : z ∈ survivingDomain γ t)
    (hR : fullRadius G t z = (2 * z.im) * Real.exp (-u)) :
    radiusLevelTime γ G z u = (t : ℝ≥0∞) := by
  have he : {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
      fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)} = {(t : ℝ≥0∞)} := by
    ext s
    constructor
    · rintro ⟨hs, hsl, hsR⟩
      have hh : s.toNNReal = t := live_radius_unique hU h z s.toNNReal t hsl ht (hsR.trans hR.symm)
      have hse : (s.toNNReal : ℝ≥0∞) = s := ENNReal.coe_toNNReal hs.ne
      rw [Set.mem_singleton_iff, ← hse, hh]
    · intro hs
      rw [Set.mem_singleton_iff] at hs
      subst s
      simpa only [Set.mem_ofPred_eq, ENNReal.coe_lt_top, ENNReal.toNNReal_coe, true_and] using And.intro ht hR
  rw [radiusLevelTime, he, sInf_singleton]

lemma stoppedGreen_eq_of_live_level
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (κ : ℝ) (z : ℂ) (u : ℝ) (t : ℝ≥0) (ht : z ∈ survivingDomain γ t)
    (hR : fullRadius G t z = (2 * z.im) * Real.exp (-u)) :
    stoppedGreen κ U γ G z u = greenDensity κ U γ G t z := by
  rw [stoppedGreen, radiusLevelTime_eq_of_live_level hU h z u t ht hR]
  simp only [ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe]

lemma stoppedGreen_eq_zero_of_no_level
    (κ : ℝ) (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ)
    (hn : ¬ ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧
      fullRadius G t z = (2 * z.im) * Real.exp (-u)) :
    stoppedGreen κ U γ G z u = 0 := by
  have he : {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
      fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨_, hsl, hsR⟩
    exact hn ⟨s.toNNReal, hsl, hsR⟩
  simp only [stoppedGreen, radiusLevelTime, he, sInf_empty, lt_self_iff_false, ↓reduceIte]

end SLEExactGauge
end

 
section

open Set Filter
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsCapacityTwoWitness.fullRadius_initial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (hz : z ∈ survivingDomain γ 0) :
    fullRadius G 0 z = 2 * z.im := by
  rw [fullRadius, h.initial_value z hz.1.1,
    loewner_spatial_derivative hU h 0 z hz]
  simp

 

lemma radiusLevelTime_finite_of_live_radius_lt
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0)
    (ht : z ∈ survivingDomain γ t)
    (hR : fullRadius G t z < (2 * z.im) * Real.exp (-u)) :
    radiusLevelTime γ G z u < ∞ := by
  let L : ℝ → ℝ := fun s => Real.log ((2 * z.im) / fullRadius G s.toNNReal z)
  have hy : 0 < 2 * z.im := mul_pos (by norm_num) ht.1.1
  have hz0 : z ∈ survivingDomain γ 0 := survivingDomain_antitone γ zero_le ht
  have hL0 : L 0 = 0 := by
    simp only [L, Real.toNNReal_zero, h.fullRadius_initial hU z hz0,
      div_self hy.ne', Real.log_one]
  have hLt : u < L t := by
    have he := fullRadius_eq_logClock hU h z t ht
    rw [he] at hR
    have hc := (mul_lt_mul_iff_right₀ hy).mp hR
    rw [Real.exp_lt_exp] at hc
    dsimp only [L]
    rw [Real.toNNReal_coe, ← logRadiusClock_logCoordinates hU h z t ht]
    linarith
  have hLc : ContinuousOn L (Icc 0 (t : ℝ)) :=
    fun s hs => (loewner_radius_clock_derivative hU h t z ht s hs).continuousWithinAt
  obtain ⟨s, hs, hsu⟩ := intermediate_value_Icc t.coe_nonneg hLc
    (show u ∈ Icc (L 0) (L t) from ⟨by rwa [hL0], hLt.le⟩)
  have hsl : z ∈ survivingDomain γ s.toNNReal := h.live_at_real_time t z ht s hs.2
  have hsr : fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u) := by
    apply (fullRadius_level_iff_logClock hU h z s.toNNReal hsl u).mpr
    rw [logRadiusClock_logCoordinates hU h z s.toNNReal hsl]
    exact hsu
  rw [radiusLevelTime_eq_of_live_level hU h z u s.toNNReal hsl hsr]
  exact ENNReal.coe_lt_top

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



namespace FiniteIncreasingClock
variable {Ω : Type*} (c : FiniteIncreasingClock Ω)

lemma inverse_mem (s : ℝ) (ω : Ω) : c.inverse s ω ∈ Icc (0 : ℝ) (c.T ω : ℝ) :=
  ((c.iso ω).symm _).property

lemma clock_inverse (s : ℝ) (ω : Ω) :
    c.S (c.inverse s ω) ω = min (max s 0) (c.S (c.T ω) ω) := by
  exact congrArg Subtype.val ((c.iso ω).apply_symm_apply _)

lemma inverse_clock (ω : Ω) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (c.T ω : ℝ)) :
    c.inverse (c.S t ω) ω = t := by
  apply (c.strict ω).injOn (c.inverse_mem _ ω) ht
  dsimp only
  rw [c.clock_inverse]
  have h0 : 0 ≤ c.S t ω := by
    rw [← c.zero ω]
    exact (c.strict ω).monotoneOn ⟨le_rfl, (c.T ω).coe_nonneg⟩ ht ht.1
  have hT := (c.strict ω).monotoneOn ht ⟨(c.T ω).coe_nonneg, le_rfl⟩ ht.2
  rw [max_eq_left h0, min_eq_left hT]

lemma continuous_inverse (ω : Ω) : Continuous (fun s => c.inverse s ω) := by
  apply continuous_subtype_val.comp
  apply (c.iso ω).symm.continuous.comp
  exact Continuous.subtype_mk ((continuous_id.max continuous_const).min continuous_const) _

lemma inverse_le_iff (s : ℝ) (ω : Ω) (t : ℝ) (ht : 0 ≤ t) :
    c.inverse s ω ≤ t ↔ (c.T ω : ℝ) ≤ t ∨
      min (max s 0) (c.S (c.T ω) ω) ≤ c.S t ω := by
  by_cases hT : (c.T ω : ℝ) ≤ t
  · exact iff_of_true ((c.inverse_mem s ω).2.trans hT) (Or.inl hT)
  · have htm : t ∈ Icc (0 : ℝ) (c.T ω : ℝ) := ⟨ht, (lt_of_not_ge hT).le⟩
    rw [or_iff_right hT, ← c.clock_inverse]
    exact ((c.strict ω).le_iff_le (c.inverse_mem s ω) htm).symm

lemma measurable_inverse [MeasurableSpace Ω]
    (hS : Measurable (Function.uncurry c.S)) (hT : Measurable c.T) :
    Measurable (Function.uncurry c.inverse) := by
  apply measurable_of_Iic
  intro t
  by_cases ht : 0 ≤ t
  · have hterminal : Measurable (fun ω => c.S (c.T ω) ω) :=
      hS.comp ((measurable_coe_nnreal_real.comp hT).prodMk measurable_id)
    have he : (Function.uncurry c.inverse) ⁻¹' Iic t =
        {p : ℝ × Ω | (c.T p.2 : ℝ) ≤ t} ∪
        {p : ℝ × Ω | min (max p.1 0) (c.S (c.T p.2) p.2) ≤ c.S t p.2} := by
      ext p
      exact c.inverse_le_iff p.1 p.2 t ht
    rw [he]
    exact (measurableSet_le ((measurable_coe_nnreal_real.comp hT).comp measurable_snd) measurable_const).union
      (measurableSet_le ((measurable_fst.max measurable_const).min (hterminal.comp measurable_snd))
        (hS.comp (measurable_const.prodMk measurable_snd)))
  · have he : (Function.uncurry c.inverse) ⁻¹' Iic t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact ht ((c.inverse_mem p.1 p.2).1.trans hp)
    rw [he]
    exact MeasurableSet.empty

end FiniteIncreasingClock
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma powerLogDensity_pos (κ p α : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0 < powerLogDensity κ p α q x := Real.exp_pos _

lemma powerLogDensity_le_radius
    (κ p α η₀ u : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ α) (q : ℂ × ℝ) (x : ℝ)
    (hs : logRadiusClock η₀ q ≤ u) :
    powerLogDensity κ p α q x ≤ Real.exp (p * (u - Real.log 2 - η₀)) := by
  rw [powerLogDensity_radius_angle κ p α η₀ q x]
  have ha' : (logAngleSq κ q x) ^ (α / 2) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (logAngleSq_pos κ q x).le
      (logAngleSq_le_one κ q x) (div_nonneg ha (by norm_num))
  calc
    _ ≤ Real.exp (p * (logRadiusClock η₀ q - Real.log 2 - η₀)) * 1 :=
      mul_le_mul_of_nonneg_left ha' (Real.exp_pos _).le
    _ ≤ _ := by rw [mul_one]; apply Real.exp_le_exp.mpr; gcongr

lemma powerLogGenerator_abs_bound
    (κ p α lo : ℝ) (q : ℂ × ℝ) (x : ℝ) (hlo : lo ≤ q.1.im) :
    |powerLogGenerator κ p α q x| ≤
      powerLogDensity κ p α q x *
        (|(-4 * α + κ * α * (α + 1) / 2)| + |(4 * p - κ * α / 2)|) /
          Real.exp (2 * lo) := by
  let A := -4 * α + κ * α * (α + 1) / 2
  let D := 4 * p - κ * α / 2
  let X := q.1.re - Real.sqrt κ * x
  let Y := Real.exp (2 * q.1.im)
  let N := greenLogNormSq κ q x
  let φ := powerLogDensity κ p α q x
  have hN : 0 < N := greenLogNormSq_pos κ q x
  have hY : 0 < Y := Real.exp_pos _
  have hφ : 0 ≤ φ := (powerLogDensity_pos κ p α q x).le
  have hX : X ^ 2 ≤ N := le_add_of_nonneg_right hY.le
  have hYN : Y ≤ N := le_add_of_nonneg_left (sq_nonneg _)
  have hlow : Real.exp (2 * lo) ≤ N :=
    (Real.exp_le_exp.mpr (by linarith)).trans hYN
  have hnum : |A * X ^ 2 + D * Y| ≤ (|A| + |D|) * N := by
    calc
      _ ≤ |A * X ^ 2| + |D * Y| := abs_add_le _ _
      _ = |A| * X ^ 2 + |D| * Y := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg X), abs_of_pos hY]
      _ ≤ |A| * N + |D| * N := add_le_add
        (mul_le_mul_of_nonneg_left hX (abs_nonneg A))
        (mul_le_mul_of_nonneg_left hYN (abs_nonneg D))
      _ = _ := by ring
  change |φ * (A * X ^ 2 + D * Y) / N ^ 2| ≤ φ * (|A| + |D|) / _
  rw [abs_div, abs_mul, abs_of_nonneg hφ, abs_of_nonneg (sq_nonneg N)]
  calc
    _ ≤ φ * ((|A| + |D|) * N) / N ^ 2 := by gcongr
    _ = φ * (|A| + |D|) / N := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hlow

lemma powerLogGenerator_le_radius_height
    (κ p α η₀ u lo : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ α) (q : ℂ × ℝ) (x : ℝ)
    (hs : logRadiusClock η₀ q ≤ u) (hlo : lo ≤ q.1.im) :
    |powerLogGenerator κ p α q x| ≤
      Real.exp (p * (u - Real.log 2 - η₀)) *
        (|(-4 * α + κ * α * (α + 1) / 2)| + |(4 * p - κ * α / 2)|) /
          Real.exp (2 * lo) := by
  apply (powerLogGenerator_abs_bound κ p α lo q x hlo).trans
  apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (powerLogDensity_le_radius κ p α η₀ u hp ha q x hs)
    (add_nonneg (abs_nonneg _) (abs_nonneg _))

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem exists_finite_angular_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (ε : ℝ) (hε : 0 < ε) (hε0 : ε ≤ logAngleSq κ (initialLogCoordinates z) 0) :
    ∃ f : Ω → ℝ,
      Integrable f P ∧ (∫ ω, f ω ∂P) = initialGreen κ z ∧
      (∀ ω, 0 ≤ f ω ∧ f ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))) ∧
      ∀ (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
        IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F →
        ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧
          Real.log ((2 * z.im) / fullRadius G t z) ≤ u ∧
          (Real.log ((2 * z.im) / fullRadius G t z) = u ∨
            (Real.sin (Complex.arg (G t z - ((Real.sqrt κ * B t ω : ℝ) : ℂ)))) ^ 2 = ε) ∧
          f ω = greenDensity κ (fun t => Real.sqrt κ * B t ω) γ G t z ∧
          ((Real.sin (Complex.arg (G t z - ((Real.sqrt κ * B t ω : ℝ) : ℂ)))) ^ 2 = ε →
            f ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) *
              ε ^ (greenExponent κ / 2)) := by
  let η₀ := Real.log z.im
  let lo := η₀ - u / (2 * ε) - 1
  let hi := η₀ + 1
  have hule : 0 ≤ u / (2 * ε) := by positivity
  have hle : lo ≤ hi := by dsimp [lo, hi]; linarith
  let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨c⟩ := exists_clippedLogSolution B hm hBm hBc κ lo hi hle (initialLogCoordinates z)
  have hη : (initialLogCoordinates z).1.im = η₀ := by
    simp only [initialLogCoordinates, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
    rfl
  let a := 4 * ε ^ 2 / Real.exp (2 * η₀)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (u / a)
  have hT : u < (4 * ε ^ 2 / Real.exp (2 * (initialLogCoordinates z).1.im)) * ((N : ℝ≥0) : ℝ) := by
    rw [hη]
    have hh := (div_lt_iff₀ ha).mp hN
    simpa only [NNReal.coe_natCast, mul_comm (N : ℝ) a] using hh
  obtain ⟨τ, hτ, ht, hin, hpre, hbound, hfi, hfm⟩ := c.finite_angular_law
    hB hBm hBc hB0 hκ hκ8 rfl u ε hu hε hε0
    (by rw [hη]; dsimp [lo]; linarith) (by rw [hη]; dsimp [hi]; linarith) (N : ℝ≥0) hT
  let f (ω : Ω) := greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω)
  refine ⟨f, hfi, hfm.trans (greenLogDensity_initial κ z hz), ?_, ?_⟩
  · intro ω
    refine ⟨greenLogDensity_nonneg _ _ _, ?_⟩
    have hh := greenLogDensity_le_radius κ (initialLogCoordinates z).1.im u hκ hκ8 (c.Q (τ ω) ω) (B (τ ω) ω)
      (hin ω (τ ω) le_rfl).1
    simpa only [hη] using hh
  · intro ω γ G F hw
    have hU : Continuous (fun t => Real.sqrt κ * B t ω) := (hBc ω).const_mul _
    have hQd (s : ℝ) (hs : s ∈ Icc 0 (τ ω : ℝ)) := (c.derivative ω s hs.1).mono
      (show Icc (0 : ℝ) (τ ω : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
    have hQb (s : ℝ) (hs : s ∈ Icc 0 (τ ω : ℝ)) : (c.Q s ω).1.im ∈ Icc lo hi := by
      have hh := (hin ω s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)).2.2
      simpa only [Set.mem_Icc, Real.coe_toNNReal _ hs.1] using hh
    obtain ⟨hlive, heq⟩ := clipped_log_identification hU hw z hz (τ ω) lo hi hle
      (fun s => c.Q s ω) (c.initial ω) hQd hQb
    have he : c.Q (τ ω) ω = logLoewnerCoordinates G z (τ ω) :=
      heq ⟨(τ ω).coe_nonneg, le_rfl⟩
    have hr : logRadiusClock (initialLogCoordinates z).1.im (c.Q (τ ω) ω) =
        Real.log ((2 * z.im) / fullRadius G (τ ω) z) := by
      rw [he, hη]
      exact logRadiusClock_logCoordinates hU hw z (τ ω) hlive
    have ha' : logAngleSq κ (c.Q (τ ω) ω) (B (τ ω) ω) =
        (Real.sin (Complex.arg (G (τ ω) z - ((Real.sqrt κ * B (τ ω) ω : ℝ) : ℂ)))) ^ 2 := by
      rw [he]
      exact logAngleSq_logCoordinates κ _ G z _ (hw.imag_positive _ z hlive)
    refine ⟨τ ω, hlive, ?_, ?_, ?_, ?_⟩
    · simpa only [hr] using (hin ω (τ ω) le_rfl).1
    · simpa only [hr, ha'] using hbound ω
    · dsimp only [f]
      rw [he]
      exact greenLogDensity_logCoordinates hU hw κ _ z _ hlive rfl
    · intro hA
      have hh := greenLogDensity_le_at_angular_exit κ (initialLogCoordinates z).1.im u ε hκ hκ8
        (c.Q (τ ω) ω) (B (τ ω) ω) (hin ω (τ ω) le_rfl).1 (by rw [ha', hA])
      simpa only [hη] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma initialLogCoordinates_im (z : ℂ) :
    (initialLogCoordinates z).1.im = Real.log z.im := by
  simp [initialLogCoordinates]

lemma exists_angularLocalization
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε)
    (hε0 : ε ≤ logAngleSq κ (initialLogCoordinates z) 0) :
    Nonempty (AngularLocalization B hm κ z u ε) := by
  let η₀ := Real.log z.im
  let lo := η₀ - u / (2 * ε) - 1
  let hi := η₀ + 1
  have hule : 0 ≤ u / (2 * ε) := by positivity
  have hle : lo ≤ hi := by dsimp [lo, hi]; linarith
  obtain ⟨c⟩ := exists_clippedLogSolution B hm hBm hBc κ lo hi hle (initialLogCoordinates z)
  let a := 4 * ε ^ 2 / Real.exp (2 * η₀)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (u / a)
  have hT : u < (4 * ε ^ 2 / Real.exp (2 * (initialLogCoordinates z).1.im)) * ((N : ℝ≥0) : ℝ) := by
    rw [initialLogCoordinates_im]
    have hh := (div_lt_iff₀ ha).mp hN
    simpa only [NNReal.coe_natCast, mul_comm (N : ℝ) a] using hh
  obtain ⟨τ, hτ, ht, hin, hpre, hbound, _, _⟩ := c.finite_angular_law
    hB hBm hBc hB0 hκ hκ8 rfl u ε hu hε hε0
    (by rw [initialLogCoordinates_im]; dsimp [lo, η₀]; linarith)
    (by rw [initialLogCoordinates_im]; dsimp [hi, η₀]; linarith) (N : ℝ≥0) hT
  exact ⟨⟨lo, hi, hle, c, N, τ, hτ, fun ω => (ht ω).le,
    by simpa only [initialLogCoordinates_im] using hin,
    by simpa only [initialLogCoordinates_im] using hpre,
    by simpa only [initialLogCoordinates_im] using hbound⟩⟩

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma chart_identification
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    z ∈ survivingDomain γ (a.τ ω) ∧
      ∀ t : ℝ≥0, t ≤ a.τ ω → a.solution.Q t ω = logLoewnerCoordinates G z t := by
  have hQd (s : ℝ) (hs : s ∈ Icc 0 (a.τ ω : ℝ)) := (a.solution.derivative ω s hs.1).mono
    (show Icc (0 : ℝ) (a.τ ω : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
  have hQb (s : ℝ) (hs : s ∈ Icc 0 (a.τ ω : ℝ)) : (a.solution.Q s ω).1.im ∈ Icc a.lo a.hi := by
    have hh := (a.inside ω s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)).2.2
    simpa only [Set.mem_Icc, Real.coe_toNNReal _ hs.1] using hh
  obtain ⟨hlive, heq⟩ := clipped_log_identification ((hBc ω).const_mul _) hw z hz (a.τ ω)
    a.lo a.hi a.le (fun s => a.solution.Q s ω) (a.solution.initial ω) hQd hQb
  exact ⟨hlive, fun t ht => by simpa only [Real.toNNReal_coe] using heq ⟨t.coe_nonneg, ht⟩⟩

lemma clock_eq_chart
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (t : ℝ≥0) (ht : t ≤ a.τ ω) :
    logRadiusClock (Real.log z.im) (a.solution.Q t ω) =
      Real.log ((2 * z.im) / fullRadius G t z) := by
  obtain ⟨hl, he⟩ := a.chart_identification hBc hz ω γ G F hw
  rw [he t ht]
  exact logRadiusClock_logCoordinates ((hBc ω).const_mul _) hw z t (survivingDomain_antitone γ ht hl)

lemma mean_green
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane) :
    Integrable (fun ω => greenLogDensity κ (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)) P ∧
      (∫ ω, greenLogDensity κ (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) = initialGreen κ z := by
  obtain ⟨hi, he⟩ := a.solution.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    (Real.log z.im) u a.τ a.stopping a.T a.bounded
    (fun ω t ht => ⟨(a.inside ω t ht).1, (a.inside ω t ht).2.2⟩)
  exact ⟨hi, he.trans (greenLogDensity_initial κ z hz)⟩

end AngularLocalization
end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_AngularPowerDynkin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Power Dynkin for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma powerLogGenerator_lyapunov (κ b : ℝ) (hκ : 0 < κ)
    (q : ℂ × ℝ) (x : ℝ) :
    powerLogGenerator κ (codimension κ) (greenExponent κ - b) q x =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) q x *
        logClockRate κ q x * (κ * b / 8) *
          (1 - (greenExponent κ - b) * ((logAngleSq κ q x)⁻¹ - 1)) := by
  unfold powerLogGenerator
  rw [← power_physical_generator κ _ _ hκ.le]
  exact green_weighted_power_generator κ b hκ q x

lemma powerLogDensity_div_angle (κ p α : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    powerLogDensity κ p α q x / logAngleSq κ q x =
      powerLogDensity κ p (α - 2) q x := by
  rw [powerLogDensity_radius_angle κ p α 0, powerLogDensity_radius_angle κ p (α - 2) 0,
    mul_div_assoc]
  congr 1
  rw [show (α - 2) / 2 = α / 2 - 1 by ring,
    Real.rpow_sub (logAngleSq_pos κ q x), Real.rpow_one]

lemma powerLogGenerator_two_powers (κ b : ℝ) (hκ : 0 < κ)
    (q : ℂ × ℝ) (x : ℝ) :
    powerLogGenerator κ (codimension κ) (greenExponent κ - b) q x =
      logClockRate κ q x * (κ * b / 8) *
        ((1 + (greenExponent κ - b)) *
            powerLogDensity κ (codimension κ) (greenExponent κ - b) q x -
          (greenExponent κ - b) *
            powerLogDensity κ (codimension κ) (greenExponent κ - b - 2) q x) := by
  rw [powerLogGenerator_lyapunov κ b hκ,
    ← powerLogDensity_div_angle κ (codimension κ) (greenExponent κ - b)]
  ring

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

 

theorem mean_power
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 ≤ κ) (p α : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ α) :
    Integrable (fun ω => powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)) P ∧
    Integrable (fun ω => ∫ t in (0 : ℝ)..(a.τ ω : ℝ),
      powerLogGenerator κ p α (a.solution.Q t ω) (B t.toNNReal ω)) P ∧
      (∫ ω, powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) =
        powerLogDensity κ p α (initialLogCoordinates z) 0 +
        ∫ ω, (∫ t in (0 : ℝ)..(a.τ ω : ℝ),
          powerLogGenerator κ p α (a.solution.Q t ω) (B t.toNNReal ω)) ∂P := by
  let K := Real.exp (p * (u - Real.log 2 - Real.log z.im))
  let C := K * (|(-4 * α + κ * α * (α + 1) / 2)| + |(4 * p - κ * α / 2)|) /
    Real.exp (2 * a.lo)
  apply a.solution.stopped_power_dynkin_bounded hB hBm hBc hB0 hκ p α a.τ a.stopping
    a.T a.bounded (fun ω t ht => (a.inside ω t ht).2.2) K C (by dsimp [C, K]; positivity)
  · intro ω t ht
    rw [abs_of_pos (powerLogDensity_pos _ _ _ _ _)]
    exact powerLogDensity_le_radius κ p α (Real.log z.im) u hp ha _ _ (a.inside ω t ht).1
  · intro ω t ht
    exact powerLogGenerator_le_radius_height κ p α (Real.log z.im) u a.lo hp ha _ _
      (a.inside ω t ht).1 (a.inside ω t ht).2.2.1

end AngularLocalization
end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma continuous_logClockRate (κ : ℝ) :
    Continuous (fun p : (ℂ × ℝ) × ℝ => logClockRate κ p.1 p.2) := by
  have hN : Continuous (fun p : (ℂ × ℝ) × ℝ => greenLogNormSq κ p.1 p.2) := by
    unfold greenLogNormSq
    fun_prop
  unfold logClockRate
  exact (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).div (hN.pow 2)
    (fun p => pow_ne_zero 2 (greenLogNormSq_pos κ p.1 p.2).ne')

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma clock_measurable : Measurable (Function.uncurry a.clock.S) :=
  (continuous_logRadiusClock _).measurable.comp a.solution.measurable

lemma inverse_measurable : Measurable (Function.uncurry a.clock.inverse) :=
  a.clock.measurable_inverse a.clock_measurable (stopping_time_measurable_nnreal a.stopping)

lemma radiusValue_continuous
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (p α : ℝ) (ω : Ω) :
    Continuous (fun s => a.radiusValue p α s ω) := by
  exact (powerLogDensity_contDiff κ p α).continuous.comp
    (((a.solution.lipschitz ω).continuous.comp (a.clock.continuous_inverse ω)).prodMk
      ((hBc ω).comp (continuous_real_toNNReal.comp (a.clock.continuous_inverse ω))))

lemma radiusValue_measurable
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (p α : ℝ) :
    Measurable (Function.uncurry (a.radiusValue p α)) := by
  exact (powerLogDensity_contDiff κ p α).continuous.measurable.comp
    ((a.solution.measurable.comp (a.inverse_measurable.prodMk measurable_snd)).prodMk
      (hBm.comp ((continuous_real_toNNReal.measurable.comp a.inverse_measurable).prodMk measurable_snd)))

lemma radiusValue_at_clock (p α : ℝ) (ω : Ω) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (a.τ ω : ℝ)) :
    a.radiusValue p α (a.clock.S t ω) ω =
      powerLogDensity κ p α (a.solution.Q t ω) (B t.toNNReal ω) := by
  unfold radiusValue
  rw [a.clock.inverse_clock ω t ht]

lemma radius_integral_substitution
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (p α : ℝ) (ω : Ω) :
    (∫ t in (0 : ℝ)..(a.τ ω : ℝ),
      powerLogDensity κ p α (a.solution.Q t ω) (B t.toNNReal ω) *
        logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω)) =
      ∫ s in (0 : ℝ)..(a.clock.S (a.τ ω) ω), a.radiusValue p α s ω := by
  have hh := intervalIntegral.integral_comp_mul_deriv''
    (a.clock.continuous ω).continuousOn
    (f' := fun t => logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω))
    (a := (0 : ℝ)) (b := (a.τ ω : ℝ)) (g := fun s => a.radiusValue p α s ω)
    (fun t ht => by
      have ht' : t ∈ Ioo (0 : ℝ) (a.τ ω : ℝ) := by
        simpa only [min_eq_left (a.τ ω).coe_nonneg, max_eq_right (a.τ ω).coe_nonneg] using ht
      exact ((a.radius_clock_derivative ω t ⟨ht'.1.le, ht'.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)).hasDerivWithinAt)
    ((continuous_logClockRate κ).comp
      ((a.solution.lipschitz ω).continuous.prodMk ((hBc ω).comp continuous_real_toNNReal))).continuousOn
    (a.radiusValue_continuous hBc p α ω).continuousOn
  rw [a.clock.zero ω] at hh
  rw [← hh]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) (a.τ ω : ℝ) := by
    simpa only [uIcc_of_le (a.τ ω).coe_nonneg] using ht
  dsimp only [Function.comp_def]
  rw [a.radiusValue_at_clock p α ω t ht']

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma powerLogDensity_le_radius_angle
    (κ p α η₀ u ε : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (q : ℂ × ℝ) (x : ℝ)
    (hs : logRadiusClock η₀ q ≤ u) (ha : ε ≤ logAngleSq κ q x) :
    powerLogDensity κ p α q x ≤
      Real.exp (p * (u - Real.log 2 - η₀)) * max 1 (ε ^ (α / 2)) := by
  rw [powerLogDensity_radius_angle κ p α η₀ q x]
  have hpow : (logAngleSq κ q x) ^ (α / 2) ≤ max 1 (ε ^ (α / 2)) := by
    by_cases hp' : 0 ≤ α / 2
    · have hh : (logAngleSq κ q x) ^ (α / 2) ≤ 1 := by
        simpa only [Real.one_rpow] using
          (Real.rpow_le_rpow (logAngleSq_pos κ q x).le (logAngleSq_le_one κ q x) hp')
      exact hh.trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hε ha (le_of_not_ge hp')).trans (le_max_right _ _)
  exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hp))
    hpow (Real.rpow_nonneg (logAngleSq_pos κ q x).le _) (Real.exp_pos _).le

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε v δ : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma radiusKernel_nonneg (p α s : ℝ) (ω : Ω) : 0 ≤ a.radiusKernel p α s ω := by
  unfold radiusKernel
  split_ifs
  · exact (powerLogDensity_pos _ _ _ _ _).le
  · rfl

lemma radiusKernel_le (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (s : ℝ) (ω : Ω) :
    a.radiusKernel p α s ω ≤
      Real.exp (p * (u - Real.log 2 - Real.log z.im)) * max 1 (ε ^ (α / 2)) := by
  have ht := a.clock.inverse_mem s ω
  have htn := Real.toNNReal_le_iff_le_coe.mpr ht.2
  have hh := a.inside ω (a.clock.inverse s ω).toNNReal htn
  rw [Real.coe_toNNReal _ ht.1] at hh
  unfold radiusKernel
  split_ifs
  · exact powerLogDensity_le_radius_angle κ p α (Real.log z.im) u ε hp hε _ _ hh.1 hh.2.1
  · exact mul_nonneg (Real.exp_pos _).le ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _))

lemma radiusKernel_measurable
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (p α : ℝ) :
    Measurable (Function.uncurry (a.radiusKernel p α)) := by
  have ht : Measurable (fun q : ℝ × Ω => a.clock.S (a.τ q.2) q.2) :=
    a.clock_measurable.comp (((measurable_coe_nnreal_real.comp
      (stopping_time_measurable_nnreal a.stopping)).comp measurable_snd).prodMk measurable_snd)
  exact Measurable.ite (measurableSet_le measurable_fst ht) (a.radiusValue_measurable hBm p α) measurable_const

lemma radiusKernel_integral (p α : ℝ) (ω : Ω) :
    (∫ s in (0 : ℝ)..u, a.radiusKernel p α s ω) =
      ∫ s in (0 : ℝ)..(a.clock.S (a.τ ω) ω), a.radiusValue p α s ω := by
  change (∫ s in (0 : ℝ)..u,
    Set.indicator {s | s ≤ a.clock.S (a.τ ω) ω} (fun s => a.radiusValue p α s ω) s) = _
  exact intervalIntegral.integral_indicator ⟨a.clock.terminal_nonneg ω, a.clock_upper ω⟩

lemma synchronize_real (b : AngularLocalization B hm κ z v δ)
    (ω : Ω) (t : ℝ) (h0 : 0 ≤ t) (ha : t ≤ (a.τ ω : ℝ)) (hb : t ≤ (b.τ ω : ℝ)) :
    a.solution.Q t ω = b.solution.Q t ω := by
  simpa only [Real.coe_toNNReal t h0] using a.synchronize b ω t.toNNReal
    (Real.toNNReal_le_iff_le_coe.mpr ha) (Real.toNNReal_le_iff_le_coe.mpr hb)

lemma inverse_synchronize (b : AngularLocalization B hm κ z v δ)
    (huv : u ≤ v) (hδε : δ ≤ ε) (ω : Ω) (s : ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ a.clock.S (a.τ ω) ω) :
    a.clock.inverse s ω = b.clock.inverse s ω := by
  let t := a.clock.inverse s ω
  have htm := a.clock.inverse_mem s ω
  have hab : (a.τ ω : ℝ) ≤ (b.τ ω : ℝ) := by exact_mod_cast a.stopping_le b huv hδε ω
  have he : b.clock.S t ω = s := by
    change logRadiusClock _ (b.solution.Q t ω) = s
    rw [← a.synchronize_real b ω t htm.1 htm.2 (htm.2.trans hab)]
    change a.clock.S (a.clock.inverse s ω) ω = s
    rw [a.clock.clock_inverse, max_eq_left hs0]
    exact min_eq_left hs
  exact (b.clock.inverse_clock ω t ⟨htm.1, htm.2.trans hab⟩).symm.trans (by rw [he])

lemma radiusKernel_mono (b : AngularLocalization B hm κ z v δ)
    (huv : u ≤ v) (hδε : δ ≤ ε) (p α s : ℝ) (hs0 : 0 ≤ s) (ω : Ω) :
    a.radiusKernel p α s ω ≤ b.radiusKernel p α s ω := by
  by_cases hs : s ≤ a.clock.S (a.τ ω) ω
  · have hsb := hs.trans (a.terminal_clock_le b huv hδε ω)
    rw [radiusKernel, ite_eq_left hs, radiusKernel, ite_eq_left hsb]
    have he := a.inverse_synchronize b huv hδε ω s hs0 hs
    have htm := a.clock.inverse_mem s ω
    have hab : (a.τ ω : ℝ) ≤ (b.τ ω : ℝ) := by exact_mod_cast a.stopping_le b huv hδε ω
    unfold radiusValue
    rw [← he, a.synchronize_real b ω _ htm.1 htm.2 (htm.2.trans hab)]
  · rw [radiusKernel, ite_eq_right hs]
    exact b.radiusKernel_nonneg p α s ω

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma physical_power_continuous
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (p α : ℝ) (ω : Ω) :
    Continuous (fun t : ℝ =>
      powerLogDensity κ p α (a.solution.Q t ω) (B t.toNNReal ω) *
        logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω)) := by
  have hq := (a.solution.lipschitz ω).continuous.prodMk ((hBc ω).comp continuous_real_toNNReal)
  exact ((powerLogDensity_contDiff κ p α).continuous.comp hq).mul
    ((continuous_logClockRate κ).comp hq)

lemma generator_radial_integral
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ) (b : ℝ) (ω : Ω) :
    (∫ t in (0 : ℝ)..(a.τ ω : ℝ),
      powerLogGenerator κ (codimension κ) (greenExponent κ - b)
        (a.solution.Q t ω) (B t.toNNReal ω)) =
      (κ * b / 8) * ((1 + (greenExponent κ - b)) *
          (∫ s in (0 : ℝ)..u, a.radiusKernel (codimension κ) (greenExponent κ - b) s ω) -
        (greenExponent κ - b) *
          (∫ s in (0 : ℝ)..u, a.radiusKernel (codimension κ) (greenExponent κ - b - 2) s ω)) := by
  let f (α : ℝ) (t : ℝ) :=
    powerLogDensity κ (codimension κ) α (a.solution.Q t ω) (B t.toNNReal ω) *
      logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω)
  have hfi (α : ℝ) : IntervalIntegrable (f α) volume (0 : ℝ) (a.τ ω : ℝ) :=
    (a.physical_power_continuous hBc (codimension κ) α ω).intervalIntegrable _ _
  have he (t : ℝ) : powerLogGenerator κ (codimension κ) (greenExponent κ - b)
      (a.solution.Q t ω) (B t.toNNReal ω) =
        (κ * b / 8) * ((1 + (greenExponent κ - b)) * f (greenExponent κ - b) t -
          (greenExponent κ - b) * f (greenExponent κ - b - 2) t) := by
    rw [powerLogGenerator_two_powers κ b hκ]
    dsimp only [f]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((hfi _).const_mul _) ((hfi _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [a.radiusKernel_integral, a.radiusKernel_integral,
    ← a.radius_integral_substitution hBc, ← a.radius_integral_substitution hBc]

lemma radiusKernel_cumulative_integrable
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (hu : 0 ≤ u) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..u, a.radiusKernel p α s ω) P := by
  let C := Real.exp (p * (u - Real.log 2 - Real.log z.im)) * max 1 (ε ^ (α / 2))
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le
    ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _))
  have hh := bounded_stopped_cumulative_integrable (P := P) (a.radiusKernel p α)
    (a.radiusKernel_measurable hBm p α) (fun _ => u.toNNReal) (fun _ => u.toNNReal)
    measurable_const (fun _ => le_rfl) u.toNNReal (fun _ => le_rfl) C hC
    (fun ω s _ _ => by
      rw [abs_of_nonneg (a.radiusKernel_nonneg p α s ω)]
      exact a.radiusKernel_le p α hp hε s ω)
  simpa only [Real.coe_toNNReal u hu] using hh.1



theorem power_balance
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb : b ≤ greenExponent κ) (hε : 0 < ε) (hu : 0 ≤ u) :
    (∫ ω, powerLogDensity κ (codimension κ) (greenExponent κ - b)
      (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) +
      (κ * b / 8) * (greenExponent κ - b) *
        (∫ ω, (∫ s in (0 : ℝ)..u,
          a.radiusKernel (codimension κ) (greenExponent κ - b - 2) s ω) ∂P) =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) (initialLogCoordinates z) 0 +
        (κ * b / 8) * (1 + (greenExponent κ - b)) *
          (∫ ω, (∫ s in (0 : ℝ)..u,
            a.radiusKernel (codimension κ) (greenExponent κ - b) s ω) ∂P) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨_, _, he⟩ := a.mean_power hB hBm hBc hB0 hκ.le (codimension κ)
    (greenExponent κ - b) (codimension_pos κ hκ8).le (sub_nonneg.mpr hb)
  simp_rw [a.generator_radial_integral hBc hκ b] at he
  rw [integral_const_mul,
    integral_sub ((a.radiusKernel_cumulative_integrable hBm _ _ (codimension_pos κ hκ8).le hε hu).const_mul _)
      ((a.radiusKernel_cumulative_integrable hBm _ _ (codimension_pos κ hκ8).le hε hu).const_mul _),
    integral_const_mul, integral_const_mul] at he
  linarith

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε δ : ℝ}

lemma radiusKernel_eq_of_live (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v δ) (huv : u ≤ v) (hδε : δ ≤ ε)
    (p α s : ℝ) (hs0 : 0 ≤ s) (ω : Ω) (hs : s ≤ a.clock.S (a.τ ω) ω) :
    a.radiusKernel p α s ω = b.radiusKernel p α s ω := by
  have hsb := hs.trans (a.terminal_clock_le b huv hδε ω)
  rw [radiusKernel, ite_eq_left hs, radiusKernel, ite_eq_left hsb]
  have he := a.inverse_synchronize b huv hδε ω s hs0 hs
  have htm := a.clock.inverse_mem s ω
  have hab : (a.τ ω : ℝ) ≤ (b.τ ω : ℝ) := by exact_mod_cast a.stopping_le b huv hδε ω
  unfold radiusValue
  rw [← he, a.synchronize_real b ω _ htm.1 htm.2 (htm.2.trans hab)]

lemma radiusKernel_eq_below (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v ε) (huv : u ≤ v)
    (p α s : ℝ) (hs0 : 0 ≤ s) (hsu : s ≤ u) (ω : Ω) :
    a.radiusKernel p α s ω = b.radiusKernel p α s ω := by
  by_cases hs : s ≤ a.clock.S (a.τ ω) ω
  · exact a.radiusKernel_eq_of_live b huv le_rfl p α s hs0 ω hs
  · have hsb : ¬ s ≤ b.clock.S (b.τ ω) ω := by
      intro h
      exact hs (by rw [a.terminal_clock_min b huv ω]; exact le_min hsu h)
    rw [radiusKernel, ite_eq_right hs, radiusKernel, ite_eq_right hsb]

lemma radiusKernel_uniform_bound (a : AngularLocalization B hm κ z u ε)
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (s : ℝ) (ω : Ω) :
    a.radiusKernel p α s ω ≤ Real.exp (p * (u - Real.log 2 - Real.log z.im)) := by
  unfold radiusKernel
  split_ifs
  · have ht := a.clock.inverse_mem s ω
    have hh := a.inside ω (a.clock.inverse s ω).toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2)
    rw [Real.coe_toNNReal _ ht.1] at hh
    exact powerLogDensity_le_radius κ p α (Real.log z.im) u hp hα _ _ hh.1
  · exact (Real.exp_pos _).le

end AngularLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}



lemma radiusKernel_eventually_limit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (p α s : ℝ) (ω : Ω) :
    ∀ᶠ n in atTop, (a n).radiusKernel p α (max s 0) ω = limitRadiusKernel a p α s ω := by
  unfold limitRadiusKernel
  split_ifs with hh
  · filter_upwards [eventually_ge_atTop (Nat.find hh)] with n hn
    exact ((a (Nat.find hh)).radiusKernel_eq_of_live (a n) le_rfl (hε hn)
      p α _ (le_max_right _ _) ω (Nat.find_spec hh)).symm
  · apply Eventually.of_forall
    intro n
    have hn : ¬ max s 0 ≤ (a n).clock.S ((a n).τ ω) ω := fun h => hh ⟨n, h⟩
    rw [AngularLocalization.radiusKernel, ite_eq_right hn]

lemma limitRadiusKernel_nonneg
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (p α s : ℝ) (ω : Ω) :
    0 ≤ limitRadiusKernel a p α s ω := by
  unfold limitRadiusKernel
  split_ifs
  · exact AngularLocalization.radiusKernel_nonneg _ _ _ _ _
  · rfl

lemma limitRadiusKernel_measurable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (p α : ℝ) :
    Measurable (Function.uncurry (limitRadiusKernel a p α)) := by
  apply measurable_of_tendsto_metrizable
    (fun n => ((a n).radiusKernel_measurable hBm p α).comp
      ((measurable_fst.max measurable_const).prodMk measurable_snd))
  apply tendsto_pi_nhds.mpr
  intro q
  apply tendsto_const_nhds.congr'
  filter_upwards [radiusKernel_eventually_limit a hε p α q.1 q.2] with n hn
  exact hn.symm

lemma limitRadiusKernel_uniform_bound
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (s : ℝ) (ω : Ω) :
    limitRadiusKernel a p α s ω ≤ Real.exp (p * (u - Real.log 2 - Real.log z.im)) := by
  unfold limitRadiusKernel
  split_ifs
  · exact AngularLocalization.radiusKernel_uniform_bound _ _ _ hp hα _ _
  · exact (Real.exp_pos _).le

end SLEExactGauge
end


section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

 

lemma integrable_monotone_limit_of_integral_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℕ → Ω → ℝ} {F : Ω → ℝ}
    (hf : ∀ n, Integrable (f n) P)
    (hF : AEStronglyMeasurable F P)
    (hn : ∀ n ω, 0 ≤ f n ω) (hFn : ∀ ω, 0 ≤ F ω)
    (hmono : ∀ ω, Monotone (fun n => f n ω))
    (hlim : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (F ω)))
    (C : ℝ) (hbound : ∀ n, (∫ ω, f n ω ∂P) ≤ C) :
    Integrable F P ∧
      Tendsto (fun n => ∫ ω, f n ω ∂P) atTop (𝓝 (∫ ω, F ω ∂P)) := by
  have hl : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (F ω) ∂P)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hf n).aemeasurable.ennreal_ofReal)
    · exact Eventually.of_forall fun ω n m hnm => ENNReal.ofReal_le_ofReal (hmono ω hnm)
    · exact Eventually.of_forall fun ω => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim ω)
  have hle : (∫⁻ ω, ENNReal.ofReal (F ω) ∂P) ≤ ENNReal.ofReal C := by
    apply le_of_tendsto hl
    apply Eventually.of_forall
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (Eventually.of_forall (hn n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hFi : Integrable F P := by
    refine ⟨hF, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have he : (fun ω => ‖F ω‖ₑ) = fun ω => ENNReal.ofReal (F ω) := by
      funext ω
      simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hFn ω)]
    rw [he]
    exact hle.trans_lt ENNReal.ofReal_lt_top
  exact ⟨hFi, integral_tendsto_of_tendsto_of_monotone hf hFi
    (Eventually.of_forall hmono) (Eventually.of_forall hlim)⟩
end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_KernelExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Expectation for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε : ℝ}

lemma stopped_power_eq_kernel_of_hit (a : AngularLocalization B hm κ z u ε)
    (p α : ℝ) (ω : Ω) (hh : ω ∈ a.hit) :
    powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) =
      a.radiusKernel p α u ω := by
  have hc : a.clock.S (a.τ ω) ω = u := hh
  rw [radiusKernel, ite_eq_left hc.ge]
  simpa only [hc, Real.toNNReal_coe] using
    (a.radiusValue_at_clock p α ω _ ⟨(a.τ ω).coe_nonneg, le_rfl⟩).symm

lemma stopped_power_kernel_gap (a : AngularLocalization B hm κ z u ε)
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 ≤ ε) (ω : Ω) :
    0 ≤ powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) -
      a.radiusKernel p α u ω ∧
    powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) -
      a.radiusKernel p α u ω ≤
        Real.exp (p * (u - Real.log 2 - Real.log z.im)) * ε ^ (α / 2) := by
  by_cases hh : ω ∈ a.hit
  · rw [a.stopped_power_eq_kernel_of_hit p α ω hh, sub_self]
    exact ⟨le_rfl, mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hε _)⟩
  · have hc : ¬ u ≤ a.clock.S (a.τ ω) ω := by
      intro h
      exact hh (le_antisymm (a.clock_upper ω) h)
    rw [radiusKernel, ite_eq_right hc, sub_zero]
    refine ⟨(powerLogDensity_pos _ _ _ _ _).le, ?_⟩
    have ha := (a.boundary ω).resolve_left hh
    rw [powerLogDensity_radius_angle κ p α (Real.log z.im), ha]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by
      rw [← ha]; exact (logAngleSq_pos _ _ _).le) _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [(a.inside ω _ le_rfl).1]) hp

lemma radiusKernel_region_integrable
    (a : AngularLocalization B hm κ z u ε) {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (v : ℝ) :
    Integrable (fun q : ℝ × Ω => a.radiusKernel p α (max q.1 0) q.2)
      ((volume.restrict (Ioc 0 v)).prod P) := by
  apply Integrable.of_bound
    (((a.radiusKernel_measurable hBm p α).comp
      ((measurable_fst.max measurable_const).prodMk measurable_snd)).aestronglyMeasurable)
    (Real.exp (p * (u - Real.log 2 - Real.log z.im)) * max 1 (ε ^ (α / 2)))
  exact Eventually.of_forall fun q => by
    change ‖a.radiusKernel p α (max q.1 0) q.2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (a.radiusKernel_nonneg p α _ _)]
    exact a.radiusKernel_le p α hp hε _ _

lemma radiusKernel_region_integral
    (a : AngularLocalization B hm κ z u ε) {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (v : ℝ) (hv : 0 ≤ v) :
    (∫ q : ℝ × Ω, a.radiusKernel p α (max q.1 0) q.2
      ∂((volume.restrict (Ioc 0 v)).prod P)) =
      ∫ ω, (∫ s in (0 : ℝ)..v, a.radiusKernel p α s ω) ∂P := by
  rw [integral_prod_symm _ (a.radiusKernel_region_integrable hBm p α hp hε v)]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    dsimp only
    rw [intervalIntegral.integral_of_le hv]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [max_eq_left hs.1.le]

end AngularLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (s : ℝ) :
    Integrable (limitRadiusKernel a p α s) P := by
  apply Integrable.of_bound
    (((limitRadiusKernel_measurable a hε hBm p α).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (Real.exp (p * (u - Real.log 2 - Real.log z.im)))
  exact Eventually.of_forall fun ω => by
    change ‖limitRadiusKernel a p α s ω‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (limitRadiusKernel_nonneg a p α s ω)]
    exact limitRadiusKernel_uniform_bound a p α hp hα s ω

lemma limitRadiusKernel_region_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (v : ℝ) :
    Integrable (Function.uncurry (limitRadiusKernel a p α))
      ((volume.restrict (Ioc 0 v)).prod P) := by
  apply Integrable.of_bound (limitRadiusKernel_measurable a hε hBm p α).aestronglyMeasurable
    (Real.exp (p * (u - Real.log 2 - Real.log z.im)))
  exact Eventually.of_forall fun q => by
    change ‖limitRadiusKernel a p α q.1 q.2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (limitRadiusKernel_nonneg a p α q.1 q.2)]
    exact limitRadiusKernel_uniform_bound a p α hp hα q.1 q.2

lemma radiusKernel_region_integral_tendsto
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) (v : ℝ) :
    Tendsto (fun n => ∫ q : ℝ × Ω, (a n).radiusKernel p α (max q.1 0) q.2
        ∂((volume.restrict (Ioc 0 v)).prod P)) atTop
      (𝓝 (∫ q : ℝ × Ω, limitRadiusKernel a p α q.1 q.2
        ∂((volume.restrict (Ioc 0 v)).prod P))) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => Real.exp (p * (u - Real.log 2 - Real.log z.im)))
    (fun n => (((a n).radiusKernel_measurable hBm p α).comp
      ((measurable_fst.max measurable_const).prodMk measurable_snd)).aestronglyMeasurable)
    (integrable_const _)
  · intro n
    exact Eventually.of_forall fun q => by
      change ‖(a n).radiusKernel p α (max q.1 0) q.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg ((a n).radiusKernel_nonneg p α _ _)]
      exact (a n).radiusKernel_uniform_bound p α hp hα _ _
  · apply Eventually.of_forall
    intro q
    apply tendsto_const_nhds.congr'
    filter_upwards [radiusKernel_eventually_limit a hε p α q.1 q.2] with n hn
    exact hn.symm

lemma stopped_power_tendsto_limitRadiusKernel
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    (hu : 0 ≤ u) (huv : u ≤ v) (p α : ℝ) (hp : 0 ≤ p) (hα : 0 < α) (ω : Ω) :
    Tendsto (fun n => powerLogDensity κ p α ((a n).solution.Q ((a n).τ ω) ω)
      (B ((a n).τ ω) ω)) atTop (𝓝 (limitRadiusKernel b p α u ω)) := by
  have hk : Tendsto (fun n => (a n).radiusKernel p α u ω) atTop
      (𝓝 (limitRadiusKernel b p α u ω)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [radiusKernel_eventually_limit b hε p α u ω] with n hn
    rw [max_eq_left hu] at hn
    exact (hn.symm.trans ((a n).radiusKernel_eq_below (b n) huv p α u hu le_rfl ω).symm)
  have ht : Tendsto (fun n => Real.exp (p * (u - Real.log 2 - Real.log z.im)) *
      ε n ^ (α / 2)) atTop (𝓝 0) := by
    have hh := ((Real.continuousAt_rpow_const 0 (α / 2) (Or.inr (by positivity))).tendsto.comp hεlim).const_mul
      (Real.exp (p * (u - Real.log 2 - Real.log z.im)))
    simpa only [Real.zero_rpow (by positivity : α / 2 ≠ 0), mul_zero, Function.comp_def] using hh
  have hg := squeeze_zero (fun n => ((a n).stopped_power_kernel_gap p α hp (hε0 n) ω).1)
    (fun n => ((a n).stopped_power_kernel_gap p α hp (hε0 n) ω).2) ht
  have hh := hg.add hk
  simpa only [sub_add_cancel, zero_add] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε : ℝ}

lemma stopped_power_uniform_integrable
    (a : AngularLocalization B hm κ z u ε) {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hα : 0 ≤ α) :
    Integrable (fun ω => powerLogDensity κ p α (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω)) P := by
  apply a.solution.stopped_power_integrable hBm p α a.τ
    (stopping_time_measurable_nnreal a.stopping)
    (Real.exp (p * (u - Real.log 2 - Real.log z.im)))
  intro ω
  rw [abs_of_pos (powerLogDensity_pos _ _ _ _ _)]
  exact powerLogDensity_le_radius κ p α (Real.log z.im) u hp hα _ _ (a.inside ω _ le_rfl).1

lemma radiusKernel_region_integral_eq_below
    (a : AngularLocalization B hm κ z u ε) (b : AngularLocalization B hm κ z v ε)
    (huv : u ≤ v) {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p α : ℝ) (hp : 0 ≤ p) (hε : 0 < ε) (hu : 0 ≤ u) :
    (∫ q : ℝ × Ω, b.radiusKernel p α (max q.1 0) q.2
        ∂((volume.restrict (Ioc 0 u)).prod P)) =
      ∫ ω, (∫ s in (0 : ℝ)..u, a.radiusKernel p α s ω) ∂P := by
  rw [b.radiusKernel_region_integral hBm p α hp hε u hu]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 u := by simpa only [uIcc_of_le hu] using hs
  exact (a.radiusKernel_eq_below b huv p α s hs'.1 hs'.2 ω).symm

lemma power_balance_below
    (a : AngularLocalization B hm κ z u ε) (c : AngularLocalization B hm κ z v ε)
    (huv : u ≤ v) {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb : b ≤ greenExponent κ)
    (hε : 0 < ε) (hu : 0 ≤ u) :
    (∫ ω, powerLogDensity κ (codimension κ) (greenExponent κ - b)
        (a.solution.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) +
      (κ * b / 8) * (greenExponent κ - b) *
        (∫ q : ℝ × Ω, c.radiusKernel (codimension κ) (greenExponent κ - b - 2) (max q.1 0) q.2
          ∂((volume.restrict (Ioc 0 u)).prod P)) =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) (initialLogCoordinates z) 0 +
        (κ * b / 8) * (1 + (greenExponent κ - b)) *
          (∫ q : ℝ × Ω, c.radiusKernel (codimension κ) (greenExponent κ - b) (max q.1 0) q.2
            ∂((volume.restrict (Ioc 0 u)).prod P)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [a.radiusKernel_region_integral_eq_below c huv hBm _ _ (codimension_pos κ hκ8).le hε hu,
    a.radiusKernel_region_integral_eq_below c huv hBm _ _ (codimension_pos κ hκ8).le hε hu]
  exact a.power_balance hB hBm hBc hB0 hκ hκ8 b hb hε hu

end AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v : ℝ} {ε : ℕ → ℝ}

lemma stopped_power_integral_tendsto_limitRadiusKernel
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hu : 0 ≤ u) (huv : u ≤ v) (p α : ℝ) (hp : 0 ≤ p) (hα : 0 < α) :
    Tendsto (fun n => ∫ ω, powerLogDensity κ p α ((a n).solution.Q ((a n).τ ω) ω)
      (B ((a n).τ ω) ω) ∂P) atTop (𝓝 (∫ ω, limitRadiusKernel b p α u ω ∂P)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => Real.exp (p * (u - Real.log 2 - Real.log z.im)))
    (fun n => ((a n).stopped_power_uniform_integrable hBm p α hp hα.le).aestronglyMeasurable)
    (integrable_const _)
  · intro n
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (powerLogDensity_pos _ _ _ _ _)]
      exact powerLogDensity_le_radius κ p α (Real.log z.im) u hp hα.le _ _ ((a n).inside ω _ le_rfl).1
  · exact Eventually.of_forall fun ω => stopped_power_tendsto_limitRadiusKernel a b hε hεlim hε0
      hu huv p α hp hα ω

 

theorem limit_power_balance
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (c : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    Integrable (Function.uncurry (limitRadiusKernel c (codimension κ) (greenExponent κ - b - 2)))
        ((volume.restrict (Ioc 0 u)).prod P) ∧
    (∫ ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b) u ω ∂P) +
      (κ * b / 8) * (greenExponent κ - b) *
        (∫ q : ℝ × Ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b - 2) q.1 q.2
          ∂((volume.restrict (Ioc 0 u)).prod P)) =
      powerLogDensity κ (codimension κ) (greenExponent κ - b) (initialLogCoordinates z) 0 +
        (κ * b / 8) * (1 + (greenExponent κ - b)) *
          (∫ q : ℝ × Ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b) q.1 q.2
            ∂((volume.restrict (Ioc 0 u)).prod P)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let p := codimension κ
  let α := greenExponent κ - b
  let lam := κ * b / 8
  have hp : 0 ≤ p := (codimension_pos κ hκ8).le
  have hα : 0 < α := sub_pos.mpr hb
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hla : 0 < lam * α := mul_pos hlam hα
  have he (n : ℕ) := (a n).power_balance_below (c n) huv hB hBm hBc hB0 hκ hκ8 b hb.le (hε0 n) hu
  have hl := radiusKernel_region_integral_tendsto (P := P) c hε hBm p α hp hα.le u
  obtain ⟨C, hC⟩ := hl.bddAbove_range
  let D := (powerLogDensity κ p α (initialLogCoordinates z) 0 + lam * (1 + α) * C) / (lam * α)
  have hbound (n : ℕ) : (∫ q : ℝ × Ω, (c n).radiusKernel p (α - 2) (max q.1 0) q.2
      ∂((volume.restrict (Ioc 0 u)).prod P)) ≤ D := by
    apply (le_div_iff₀ hla).mpr
    have hnon : 0 ≤ (∫ ω, powerLogDensity κ p α
        ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) ∂P) :=
      integral_nonneg fun ω => (powerLogDensity_pos κ p α
        ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω)).le
    have hlow := mul_le_mul_of_nonneg_left (hC (mem_range_self n)) (mul_nonneg hlam.le (by linarith : 0 ≤ 1 + α))
    dsimp only [p, α, lam] at hnon hlow ⊢
    nlinarith [he n]
  obtain ⟨hhigh, hhighlim⟩ := integrable_monotone_limit_of_integral_le
    (fun n => (c n).radiusKernel_region_integrable hBm p (α - 2) hp (hε0 n) u)
    (limitRadiusKernel_measurable c hε hBm p (α - 2)).aestronglyMeasurable
    (fun n q => (c n).radiusKernel_nonneg p (α - 2) _ _)
    (fun q => limitRadiusKernel_nonneg c p (α - 2) q.1 q.2)
    (fun q n m hnm => (c n).radiusKernel_mono (c m) le_rfl (hε hnm) p (α - 2) _ (le_max_right _ _) _)
    (fun q => by
      apply tendsto_const_nhds.congr'
      filter_upwards [radiusKernel_eventually_limit c hε p (α - 2) q.1 q.2] with n hn
      exact hn.symm) D hbound
  refine ⟨hhigh, ?_⟩
  have hs := stopped_power_integral_tendsto_limitRadiusKernel (P := P) a c hε hεlim (fun n => (hε0 n).le)
    hBm hu huv p α hp hα
  have hleft := hs.add (hhighlim.const_mul (lam * α))
  have hright := (hl.const_mul (lam * (1 + α))).const_add (powerLogDensity κ p α (initialLogCoordinates z) 0)
  exact tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun n => (he n).symm))

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}
  (a : AngularLocalization B hm κ z u ε)

lemma radiusValue_factor (p α s : ℝ) (hs : 0 ≤ s) (ω : Ω)
    (hl : s ≤ a.clock.S (a.τ ω) ω) :
    a.radiusValue p α s ω =
      Real.exp (p * (s - Real.log 2 - Real.log z.im)) *
        (a.radiusValue 0 2 s ω) ^ (α / 2) := by
  have hc : a.clock.S (a.clock.inverse s ω) ω = s := by
    rw [a.clock.clock_inverse, max_eq_left hs]
    exact min_eq_left hl
  have he : a.radiusValue 0 2 s ω =
      logAngleSq κ (a.solution.Q (a.clock.inverse s ω) ω) (B (a.clock.inverse s ω).toNNReal ω) := by
    rw [radiusValue, powerLogDensity_radius_angle κ 0 2 (Real.log z.im)]
    norm_num
  rw [he, radiusValue, powerLogDensity_radius_angle κ p α (Real.log z.im)]
  change Real.exp (p * (a.clock.S (a.clock.inverse s ω) ω - _ - _)) * _ = _
  rw [hc]

lemma radiusKernel_zero (p s : ℝ) (hs : 0 ≤ s) (ω : Ω) :
    a.radiusKernel p 0 s ω = if s ≤ a.clock.S (a.τ ω) ω then
      Real.exp (p * (s - Real.log 2 - Real.log z.im)) else 0 := by
  unfold radiusKernel
  split_ifs with h
  · rw [a.radiusValue_factor p 0 s hs ω h, zero_div, Real.rpow_zero, mul_one]
  · rfl

lemma radiusKernel_power_factor (p α β s : ℝ) (hs : 0 ≤ s) (ω : Ω) :
    a.radiusKernel p (α + β) s ω = a.radiusKernel p α s ω *
      (a.radiusKernel 0 2 s ω) ^ (β / 2) := by
  unfold radiusKernel
  split_ifs with hl
  · rw [a.radiusValue_factor p (α + β) s hs ω hl,
      a.radiusValue_factor p α s hs ω hl]
    have hpos : 0 < a.radiusValue 0 2 s ω := powerLogDensity_pos _ _ _ _ _
    rw [add_div, Real.rpow_add hpos]
    ring
  · simp

end AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_zero
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (p s : ℝ) (ω : Ω) :
    limitRadiusKernel a p 0 s ω =
      if ∃ n, max s 0 ≤ (a n).clock.S ((a n).τ ω) ω then
        Real.exp (p * (max s 0 - Real.log 2 - Real.log z.im)) else 0 := by
  unfold limitRadiusKernel
  split_ifs with hh
  · rw [(a (Nat.find hh)).radiusKernel_zero p (max s 0) (le_max_right _ _) ω,
      ite_eq_left (Nat.find_spec hh)]
  · rfl

lemma limitRadiusKernel_zero_growth
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (p s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    limitRadiusKernel a p 0 t ω ≤ Real.exp (p * (t - s)) * limitRadiusKernel a p 0 s ω := by
  by_cases hh : ∃ n, t ≤ (a n).clock.S ((a n).τ ω) ω
  · have hh' : ∃ n, s ≤ (a n).clock.S ((a n).τ ω) ω := by
      obtain ⟨n, hn⟩ := hh
      exact ⟨n, hst.trans hn⟩
    rw [limitRadiusKernel_zero, max_eq_left (hs.trans hst), ite_eq_left hh,
      limitRadiusKernel_zero, max_eq_left hs, ite_eq_left hh', ← Real.exp_add]
    apply le_of_eq
    congr 1
    ring
  · rw [limitRadiusKernel_zero a p t ω, max_eq_left (hs.trans hst), ite_eq_right hh]
    exact mul_nonneg (Real.exp_pos _).le (limitRadiusKernel_nonneg a p 0 s ω)

lemma limitRadiusKernel_power_factor
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (p α β s : ℝ) (ω : Ω) :
    limitRadiusKernel a p (α + β) s ω = limitRadiusKernel a p α s ω *
      (limitRadiusKernel a 0 2 s ω) ^ (β / 2) := by
  obtain ⟨n, h1, h2, h3⟩ := ((radiusKernel_eventually_limit a hε p (α + β) s ω).and
    ((radiusKernel_eventually_limit a hε p α s ω).and
      (radiusKernel_eventually_limit a hε 0 2 s ω))).exists
  rw [← h1, ← h2, ← h3]
  exact (a n).radiusKernel_power_factor p α β _ (le_max_right _ _) ω

lemma limitRadiusKernel_angle_le_one
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (s : ℝ) (ω : Ω) :
    limitRadiusKernel a 0 2 s ω ≤ 1 := by
  simpa only [zero_mul, Real.exp_zero] using
    limitRadiusKernel_uniform_bound a 0 2 le_rfl (by norm_num) s ω

lemma integral_limitRadiusKernel_zero_growth
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p s t : ℝ) (hp : 0 ≤ p) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ ω, limitRadiusKernel a p 0 t ω ∂P) ≤
      Real.exp (p * (t - s)) * (∫ ω, limitRadiusKernel a p 0 s ω ∂P) := by
  rw [← integral_const_mul]
  exact integral_mono (limitRadiusKernel_integrable a hε hBm p 0 hp le_rfl t)
    ((limitRadiusKernel_integrable a hε hBm p 0 hp le_rfl s).const_mul _)
    (fun ω => limitRadiusKernel_zero_growth a p s t hs hst ω)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

 

lemma weighted_rpow_jensen {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {w f : Ω → ℝ} {I q : ℝ} (hI : 0 < I)
    (hw : Integrable w P) (hw0 : ∀ ω, 0 ≤ w ω) (hmean : (∫ ω, w ω ∂P) = I)
    (hf0 : ∀ ω, 0 ≤ f ω) (hq : 1 ≤ q)
    (hfi : Integrable (fun ω => w ω * f ω) P)
    (hfqi : Integrable (fun ω => w ω * (f ω) ^ q) P) :
    ((∫ ω, w ω * f ω ∂P) / I) ^ q ≤ (∫ ω, w ω * (f ω) ^ q ∂P) / I := by
  let d (ω : Ω) : ℝ≥0∞ := ENNReal.ofReal (w ω / I)
  have hd : AEMeasurable d P := (hw.div_const I).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hd0 (ω : Ω) : (d ω).toReal = w ω / I := ENNReal.toReal_ofReal (div_nonneg (hw0 ω) hI.le)
  let Q := P.withDensity d
  have hprob : IsProbabilityMeasure Q := by
    constructor
    rw [show Q = P.withDensity d from rfl, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    change (∫⁻ ω, ENNReal.ofReal (w ω / I) ∂P) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal (hw.div_const I)
      (Eventually.of_forall fun ω => div_nonneg (hw0 ω) hI.le), integral_div,
      hmean, div_self hI.ne', ENNReal.ofReal_one]
  let := hprob
  have he (g : Ω → ℝ) : (fun ω => (d ω).toReal • g ω) = (fun ω => (w ω * g ω) / I) := by
    funext ω
    rw [hd0, smul_eq_mul]
    ring
  have hi : Integrable f Q := by
    apply (integrable_withDensity_iff_integrable_smul₀' hd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    rw [he]
    exact hfi.div_const I
  have hqi : Integrable (fun ω => (f ω) ^ q) Q := by
    apply (integrable_withDensity_iff_integrable_smul₀' hd (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    rw [he]
    exact hfqi.div_const I
  have hj := (convexOn_rpow hq).map_integral_le
    (Real.continuous_rpow_const (by positivity : 0 ≤ q)).continuousOn isClosed_Ici
    (Eventually.of_forall hf0) hi hqi
  have hint (g : Ω → ℝ) : (∫ ω, g ω ∂Q) = (∫ ω, w ω * g ω ∂P) / I := by
    rw [show Q = P.withDensity d from rfl, integral_withDensity_eq_integral_toReal_smul₀ hd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), he, integral_div]
  simpa only [hint] using hj

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_green_mean
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (c : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 ≤ ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    (∫ ω, limitRadiusKernel c (codimension κ) (greenExponent κ) u ω ∂P) = initialGreen κ z := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have ht := stopped_power_integral_tendsto_limitRadiusKernel (P := P) a c hε hεlim hε0 hBm hu huv
    (codimension κ) (greenExponent κ) (codimension_pos κ hκ8).le (greenExponent_pos κ hκ hκ8)
  have he (n : ℕ) : (∫ ω, powerLogDensity κ (codimension κ) (greenExponent κ)
      ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) ∂P) = initialGreen κ z :=
    ((a n).mean_green hB hBm hBc hB0 hκ hκ8 hz).2
  exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (he n).symm))

lemma limitRadiusKernel_inverse_factor
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    (p a b s : ℝ) (ω : Ω) :
    limitRadiusKernel c p (a - b) s ω = limitRadiusKernel c p a s ω *
      (limitRadiusKernel c 0 2 s ω) ^ (-b / 2) := by
  simpa only [sub_eq_add_neg] using limitRadiusKernel_power_factor c hε p a (-b) s ω

lemma limitRadiusKernel_inverse_moment_jensen
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (p a b s I : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (hab : b ≤ a)
    (hI : 0 < I) (hmean : (∫ ω, limitRadiusKernel c p a s ω ∂P) = I)
    (hi : Integrable (limitRadiusKernel c p (a - b - 2) s) P) :
    ((∫ ω, limitRadiusKernel c p (a - b) s ω ∂P) / I) ^ (1 + 2 / b) ≤
      (∫ ω, limitRadiusKernel c p (a - b - 2) s ω ∂P) / I := by
  let w := limitRadiusKernel c p a s
  let f (ω : Ω) := (limitRadiusKernel c 0 2 s ω) ^ (-b / 2)
  have he (ω : Ω) : w ω * f ω = limitRadiusKernel c p (a - b) s ω :=
    (limitRadiusKernel_inverse_factor c hε p a b s ω).symm
  have heq (ω : Ω) : w ω * (f ω) ^ (1 + 2 / b) = limitRadiusKernel c p (a - b - 2) s ω := by
    dsimp only [f, w]
    rw [← Real.rpow_mul (limitRadiusKernel_nonneg c 0 2 s ω)]
    have hexp : -b / 2 * (1 + 2 / b) = -(b + 2) / 2 := by field_simp
    rw [hexp, ← limitRadiusKernel_inverse_factor c hε p a (b + 2) s ω]
    rw [show a - (b + 2) = a - b - 2 by ring]
  have hfi : Integrable (fun ω => w ω * f ω) P := by
    simpa only [he] using limitRadiusKernel_integrable c hε hBm p (a - b) hp (sub_nonneg.mpr hab) s
  have hfqi : Integrable (fun ω => w ω * (f ω) ^ (1 + 2 / b)) P := by simpa only [heq] using hi
  have hj := weighted_rpow_jensen (w := w) (f := f) hI (limitRadiusKernel_integrable c hε hBm p a hp ha s)
    (limitRadiusKernel_nonneg c p a s) hmean
    (fun ω => Real.rpow_nonneg (limitRadiusKernel_nonneg c 0 2 s ω) _)
    (le_add_of_nonneg_right (div_nonneg (by norm_num) hb.le) : 1 ≤ 1 + 2 / b) hfi hfqi
  simpa only [he, heq] using hj

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}

lemma weight_bound (a : AngularLocalization B hm κ z u ε)
    (hκ : 0 < κ) (hκ8 : κ < 8) (ω : Ω) :
    0 ≤ a.weight ω ∧ a.weight ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) :=
  ⟨greenLogDensity_nonneg _ _ _, greenLogDensity_le_radius κ _ u hκ hκ8 _ _ (a.inside ω _ le_rfl).1⟩

lemma radius_at_hit (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (hh : ω ∈ a.hit) :
    z ∈ survivingDomain γ (a.τ ω) ∧ fullRadius G (a.τ ω) z = (2 * z.im) * Real.exp (-u) := by
  have hU : Continuous (fun t => Real.sqrt κ * B t ω) := (hBc ω).const_mul _
  have hl := (a.chart_identification hBc hz ω γ G F hw).1
  refine ⟨hl, (fullRadius_level_iff_logClock hU hw z _ hl u).mpr ?_⟩
  rw [logRadiusClock_logCoordinates hU hw z _ hl, ← a.clock_eq_chart hBc hz ω γ G F hw _ le_rfl]
  exact hh

lemma weight_eq_source (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    a.weight ω = greenDensity κ (fun t => Real.sqrt κ * B t ω) γ G (a.τ ω) z := by
  obtain ⟨hl, he⟩ := a.chart_identification hBc hz ω γ G F hw
  rw [weight, he _ le_rfl]
  exact greenLogDensity_logCoordinates ((hBc ω).const_mul _) hw κ _ z _ hl rfl

lemma weight_eq_stoppedGreen_of_hit (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (hh : ω ∈ a.hit) :
    a.weight ω = stoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G z u := by
  obtain ⟨hl, hR⟩ := a.radius_at_hit hBc hz ω γ G F hw hh
  rw [stoppedGreen_eq_of_live_level ((hBc ω).const_mul _) hw κ z u _ hl hR]
  exact a.weight_eq_source hBc hz ω γ G F hw

lemma weight_small_of_not_hit (a : AngularLocalization B hm κ z u ε)
    (hκ : 0 < κ) (hκ8 : κ < 8) (ω : Ω) (hn : ω ∉ a.hit) :
    a.weight ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) *
      ε ^ (greenExponent κ / 2) := by
  exact greenLogDensity_le_at_angular_exit κ _ u ε hκ hκ8 _ _ (a.inside ω _ le_rfl).1
    ((a.boundary ω).resolve_left hn).le

end AngularLocalization

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma eventually_hit_of_live_level
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (T : ℝ≥0) (hT : z ∈ survivingDomain γ T)
    (hR : fullRadius G T z = (2 * z.im) * Real.exp (-u)) :
    ∀ᶠ n in atTop, ω ∈ (a n).hit ∧ (a n).τ ω = T := by
  have hU : Continuous (fun t => Real.sqrt κ * B t ω) := (hBc ω).const_mul _
  obtain ⟨δ, hδ, hδb⟩ := live_angleSq_lower_bound hU hw z T hT
  have hTc : Real.log ((2 * z.im) / fullRadius G T z) = u := by
    rw [← logRadiusClock_logCoordinates hU hw z T hT]
    exact (fullRadius_level_iff_logClock hU hw z T hT u).mp hR
  filter_upwards [(tendsto_order.mp hε).2 δ hδ] with n hn
  obtain ⟨hl, he⟩ := (a n).chart_identification hBc hz ω γ G F hw
  have hr := (a n).clock_eq_chart hBc hz ω γ G F hw ((a n).τ ω) le_rfl
  have htT : (a n).τ ω ≤ T := live_clock_le_time hU hw z _ T hl hT (by
    rw [hTc, ← hr]; exact ((a n).inside ω _ le_rfl).1)
  have ha : ε n < logAngleSq κ ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) := by
    rw [he _ le_rfl, logAngleSq_logCoordinates κ _ G z _ (hw.imag_positive _ z hl)]
    exact hn.trans_le (hδb _ htT)
  have hh : ω ∈ (a n).hit := ((a n).boundary ω).resolve_right (ne_of_gt ha)
  refine ⟨hh, ?_⟩
  exact live_radius_unique hU hw z _ T hl hT (((a n).radius_at_hit hBc hz ω γ G F hw hh).2.trans hR.symm)

lemma localizedRadiusStop_eq_source
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    localizedRadiusStop a ω = radiusLevelTime γ G z u := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    obtain ⟨n, hn, he⟩ := (eventually_hit_of_live_level a hε hBc hz ω γ G F hw T hT hR).exists
    rw [localizedRadiusStop_eq_hit a ω n hn, he,
      radiusLevelTime_eq_of_live_level ((hBc ω).const_mul _) hw z u T hT hR]
    rfl
  · rw [localizedRadiusStop_eq_top a ω (fun n hn => hh
      ⟨(a n).τ ω, (a n).radius_at_hit hBc hz ω γ G F hw hn⟩)]
    have he : {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
        fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro s ⟨_, hsl, hsR⟩
      exact hh ⟨s.toNNReal, hsl, hsR⟩
    rw [radiusLevelTime, he, sInf_empty]
    rfl

lemma localization_weight_tendsto
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    Tendsto (fun n => (a n).weight ω) atTop
      (𝓝 (stoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G z u)) := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_hit_of_live_level a hε hBc hz ω γ G F hw T hT hR] with n hn
    exact ((a n).weight_eq_stoppedGreen_of_hit hBc hz ω γ G F hw hn.1).symm
  · rw [stoppedGreen_eq_zero_of_no_level κ _ _ _ z u hh]
    have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
    have ht : Tendsto (fun n => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) *
        ε n ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
      have hx := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hε).const_mul
        (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      simpa only [Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using hx
    apply squeeze_zero (fun n => ((a n).weight_bound hκ hκ8 ω).1) _ ht
    intro n
    exact (a n).weight_small_of_not_hit hκ hκ8 ω
      (fun hn => hh ⟨(a n).τ ω, (a n).radius_at_hit hBc hz ω γ G F hw hn⟩)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma radiusLevelTime_eq_top_of_no_level (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ) (hn : ¬ ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧
      fullRadius G t z = (2 * z.im) * Real.exp (-u)) : radiusLevelTime γ G z u = ∞ := by
  have he : {s : ℝ≥0∞ | s < ∞ ∧ z ∈ survivingDomain γ s.toNNReal ∧
      fullRadius G s.toNNReal z = (2 * z.im) * Real.exp (-u)} = ∅ := by
    exact Set.eq_empty_iff_forall_notMem.mpr fun s hs => hn ⟨s.toNNReal, hs.2⟩
  rw [radiusLevelTime, he, sInf_empty]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_eq_zero_of_no_level
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (p α : ℝ) (hn : ¬ ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧
      fullRadius G T z = (2 * z.im) * Real.exp (-u)) :
    limitRadiusKernel a p α u ω = 0 := by
  unfold limitRadiusKernel
  apply dite_eq_right
  rintro ⟨n, hn'⟩
  have hh : ω ∈ (a n).hit := le_antisymm ((a n).clock_upper ω) ((le_max_left u 0).trans hn')
  exact hn ⟨(a n).τ ω, (a n).radius_at_hit hBc hz ω γ G F hw hh⟩

lemma limitRadiusKernel_eq_stopped_of_live_level
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (T : ℝ≥0) (hT : z ∈ survivingDomain γ T)
    (hR : fullRadius G T z = (2 * z.im) * Real.exp (-u)) (p α : ℝ) :
    limitRadiusKernel a p α u ω = powerLogDensity κ p α (logLoewnerCoordinates G z T) (B T ω) := by
  obtain ⟨n, hn, hhit, htime⟩ := ((radiusKernel_eventually_limit a hε p α u ω).and
    (eventually_hit_of_live_level a hεlim hBc hz ω γ G F hw T hT hR)).exists
  rw [max_eq_left hu] at hn
  rw [← hn, ← (a n).stopped_power_eq_kernel_of_hit p α ω hhit]
  obtain ⟨_, he⟩ := (a n).chart_identification hBc hz ω γ G F hw
  rw [he _ le_rfl, htime]

lemma limitRadiusKernel_eq_stoppedGreen
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    limitRadiusKernel a (codimension κ) (greenExponent κ) u ω =
      stoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G z u := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    rw [limitRadiusKernel_eq_stopped_of_live_level a hε hεlim hBc hz hu ω γ G F hw T hT hR]
    rw [stoppedGreen_eq_of_live_level ((hBc ω).const_mul _) hw κ z u T hT hR]
    exact greenLogDensity_logCoordinates ((hBc ω).const_mul _) hw κ _ z T hT rfl
  · rw [limitRadiusKernel_eq_zero_of_no_level a hBc hz ω γ G F hw _ _ hh,
      stoppedGreen_eq_zero_of_no_level κ _ γ G z u hh]

lemma limitRadiusKernel_eq_stoppedAngleSq
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    limitRadiusKernel a 0 2 u ω = stoppedAngleSq κ (fun t => B t ω) γ G z u := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    rw [limitRadiusKernel_eq_stopped_of_live_level a hε hεlim hBc hz hu ω γ G F hw T hT hR]
    rw [stoppedAngleSq, radiusLevelTime_eq_of_live_level ((hBc ω).const_mul _) hw z u T hT hR]
    simp only [ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe]
    rw [powerLogDensity_radius_angle κ 0 2 (Real.log z.im)]
    norm_num only [zero_mul, Real.exp_zero, one_mul, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
    exact logAngleSq_logCoordinates κ _ G z T (hw.imag_positive T z hT)
  · rw [limitRadiusKernel_eq_zero_of_no_level a hBc hz ω γ G F hw _ _ hh,
      stoppedAngleSq, radiusLevelTime_eq_top_of_no_level γ G z u hh]
    simp
end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_FiniteStoppedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Stopped Law for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem finite_stopped_green_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    Integrable (fun ω => stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u) P ∧
    (∫ ω, stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u ∂P) = initialGreen κ z := by
  let A := logAngleSq κ (initialLogCoordinates z) 0
  have hA : 0 < A := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεA (n : ℕ) : ε n ≤ A := div_le_self hA.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A
    simpa only [mul_one_div, mul_zero] using hh
  choose f hfi hfm hfb hfw using fun n => exists_finite_angular_kernel
    hB hBm hBc hB0 κ hκ hκ8 z hz u hu (ε n) (hε n) (hεA n)
  let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
  let g (ω : Ω) := stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u
  have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hw] with ω hω
    have hU : Continuous (fun t => Real.sqrt κ * B t ω) := (hBc ω).const_mul _
    by_cases hlevel : ∃ T : ℝ≥0, z ∈ survivingDomain (γ ω) T ∧
        fullRadius (G ω) T z = (2 * z.im) * Real.exp (-u)
    · obtain ⟨T, hT, hTR⟩ := hlevel
      obtain ⟨δ, hδ, hδb⟩ := live_angleSq_lower_bound hU hω z T hT
      have hev : ∀ᶠ n in atTop, ε n < δ := (tendsto_order.mp hεlim).2 δ hδ
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with n hn
      obtain ⟨t, ht, htu, hb, he, _⟩ := hfw n ω (γ ω) (G ω) (F ω) hω
      have hTc : Real.log ((2 * z.im) / fullRadius (G ω) T z) = u := by
        rw [← logRadiusClock_logCoordinates hU hω z T hT]
        exact (fullRadius_level_iff_logClock hU hω z T hT u).mp hTR
      have htT : t ≤ T := live_clock_le_time hU hω z t T ht hT (by simpa only [hTc] using htu)
      have htb : δ ≤ (Real.sin (Complex.arg (G ω t z - ((Real.sqrt κ * B t ω : ℝ) : ℂ)))) ^ 2 :=
        hδb t htT
      have htc : Real.log ((2 * z.im) / fullRadius (G ω) t z) = u := hb.resolve_right (by linarith)
      have htR : fullRadius (G ω) t z = (2 * z.im) * Real.exp (-u) := by
        apply (fullRadius_level_iff_logClock hU hω z t ht u).mpr
        rwa [logRadiusClock_logCoordinates hU hω z t ht]
      exact (stoppedGreen_eq_of_live_level hU hω κ z u t ht htR).trans he.symm
    · have hg : g ω = 0 := stoppedGreen_eq_zero_of_no_level κ _ _ _ z u hlevel
      rw [hg]
      have hb (n : ℕ) : f n ω ≤ K * (ε n) ^ (greenExponent κ / 2) := by
        obtain ⟨t, ht, _, htb, _, hbe⟩ := hfw n ω (γ ω) (G ω) (F ω) hω
        apply hbe
        apply htb.resolve_left
        intro he
        apply hlevel
        refine ⟨t, ht, (fullRadius_level_iff_logClock hU hω z t ht u).mpr ?_⟩
        rwa [logRadiusClock_logCoordinates hU hω z t ht]
      have hupp : Tendsto (fun n => K * (ε n) ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
        have hh := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hεlim).const_mul K
        simpa only [Function.comp_apply, Real.zero_rpow hp.ne', mul_zero] using hh
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupp
        (fun n => (hfb n ω).1) hb
  have hbound (n : ℕ) : ∀ᵐ ω ∂P, ‖f n ω‖ ≤ K := by
    apply Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hfb n ω).1] using (hfb n ω).2
  have hgm : AEStronglyMeasurable g P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hfi n).aestronglyMeasurable) hlim
  have hgi : Integrable g P := ⟨hgm,
    hasFiniteIntegral_of_dominated_convergence (integrable_const K).hasFiniteIntegral hbound hlim⟩
  have hc := tendsto_integral_of_dominated_convergence (fun _ : Ω => K)
    (fun n => (hfi n).aestronglyMeasurable) (integrable_const K) hbound hlim
  refine ⟨hgi, ?_⟩
  apply tendsto_nhds_unique hc
  simpa only [hfm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => initialGreen κ z) atTop (𝓝 (initialGreen κ z)))

 

theorem finite_stopped_green_of_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    Integrable (fun ω => stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u) P ∧
    (∫ ω, stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u ∂P) = initialGreen κ z := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw, hCB] with ω hω hω'
    simpa only [hω'] using hω
  have heq : (fun ω => stoppedGreen κ (fun t => Real.sqrt κ * C t ω)
      (γ ω) (G ω) z u) =ᵐ[P] (fun ω => stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u) := by
    filter_upwards [hCB] with ω hω
    simp only [hω]
  obtain ⟨hfi, hfm⟩ := finite_stopped_green_regular hC hCm hCc hC0 κ hκ hκ8 γ G F hwC z hz u hu
  exact ⟨hfi.congr heq, (integral_congr_ae heq).symm.trans hfm⟩

universe uLevel

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma initialGreen_pos (κ : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    0 < initialGreen κ z := by
  have hz0 : z ≠ 0 := by intro he; simp only [he, upperHalfPlane, Set.mem_ofPred_eq, Complex.zero_im, lt_self_iff_false] at hz
  have hsin : 0 < Real.sin (Complex.arg z) := by
    rw [Complex.sin_arg]
    exact div_pos hz (norm_pos_iff.mpr hz0)
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hz) _) (Real.rpow_pos_of_pos hsin _)

lemma greenDensity_nonneg
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (κ : ℝ) (t : ℝ≥0) (z : ℂ) :
    0 ≤ greenDensity κ U γ G t z := by
  classical
  by_cases hz : z ∈ survivingDomain γ t
  · rw [greenDensity, ite_eq_left hz]
    have hy := h.imag_positive t z hz
    apply mul_nonneg
    · exact Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) hy.le) (norm_nonneg _)) _
    · apply Real.rpow_nonneg
      rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact div_nonneg hy.le (norm_nonneg _)
  · simp only [greenDensity, ite_eq_right hz, le_refl]

lemma stoppedGreen_nonneg
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (κ : ℝ) (z : ℂ) (u : ℝ) :
    0 ≤ stoppedGreen κ U γ G z u := by
  unfold stoppedGreen
  split_ifs
  · exact greenDensity_nonneg h κ _ z
  · exact le_rfl



end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

lemma continuousOn_of_integral_balance {F H : ℝ → ℝ} {v A C L : ℝ}
    (hv : 0 ≤ v) (hFi : IntervalIntegrable F volume 0 v) (hHi : IntervalIntegrable H volume 0 v)
    (hbal : ∀ u ∈ Icc 0 v, F u + C * (∫ s in (0 : ℝ)..u, H s) =
      L + A * (∫ s in (0 : ℝ)..u, F s)) : ContinuousOn F (Icc 0 v) := by
  have hcF : ContinuousOn (fun u => ∫ s in (0 : ℝ)..u, F s) (Icc 0 v) := by
    simpa only [uIcc_of_le hv] using intervalIntegral.continuousOn_primitive_interval (f := F) (a := 0) (b := v) (μ := volume)
      (by simpa only [uIcc_of_le hv] using (intervalIntegrable_iff_integrableOn_Icc_of_le hv).mp hFi)
  have hcH : ContinuousOn (fun u => ∫ s in (0 : ℝ)..u, H s) (Icc 0 v) := by
    simpa only [uIcc_of_le hv] using intervalIntegral.continuousOn_primitive_interval (f := H) (a := 0) (b := v) (μ := volume)
      (by simpa only [uIcc_of_le hv] using (intervalIntegrable_iff_integrableOn_Icc_of_le hv).mp hHi)
  have hc : ContinuousOn (fun u => L + A * (∫ s in (0 : ℝ)..u, F s) - C * (∫ s in (0 : ℝ)..u, H s)) (Icc 0 v) :=
    (continuousOn_const.add (continuousOn_const.mul hcF)).sub (continuousOn_const.mul hcH)
  apply hc.congr
  intro u hu
  dsimp only
  linarith [hbal u hu]

lemma integral_drift_of_balance {F H : ℝ → ℝ} {v A C L q : ℝ}
    (hv : 0 ≤ v) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hFi : IntervalIntegrable F volume 0 v) (hHi : IntervalIntegrable H volume 0 v)
    (hbal : ∀ u ∈ Icc 0 v, F u + C * (∫ s in (0 : ℝ)..u, H s) =
      L + A * (∫ s in (0 : ℝ)..u, F s))
    (hpow : ∀ᵐ s ∂volume.restrict (Ioc 0 v), (F s) ^ q ≤ H s) :
    ContinuousOn F (Icc 0 v) ∧
      ∀ s ∈ Icc 0 v, ∀ t ∈ Icc 0 v, s ≤ t →
        F t - F s ≤ ∫ u in s..t, A * F u - C * (F u) ^ q := by
  have hc := continuousOn_of_integral_balance hv hFi hHi hbal
  refine ⟨hc, ?_⟩
  intro s hs t ht hst
  have hsub : uIcc s t ⊆ uIcc 0 v := by
    simp only [uIcc_of_le hst, uIcc_of_le hv]
    exact Icc_subset_Icc hs.1 ht.2
  have hsub0 (x : ℝ) (hx : x ∈ Icc 0 v) : uIcc 0 x ⊆ uIcc 0 v := by
    simp only [uIcc_of_le hx.1, uIcc_of_le hv]
    exact Icc_subset_Icc le_rfl hx.2
  have hFi' := hFi.mono_set hsub
  have hHi' := hHi.mono_set hsub
  have hpI : IntervalIntegrable (fun u => F u ^ q) volume s t := by
    apply ContinuousOn.intervalIntegrable
    apply (Real.continuous_rpow_const hq).comp_continuousOn
    exact hc.mono (by simpa only [uIcc_of_le hst] using Icc_subset_Icc hs.1 ht.2)
  have hpw : (∫ u in s..t, (F u) ^ q) ≤ ∫ u in s..t, H u := by
    apply intervalIntegral.integral_mono_ae_restrict hst hpI hHi'
    rw [restrict_Ioc_eq_restrict_Icc] at hpow
    exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hs.1 ht.2) hpow
  have hdiff : F t - F s = A * (∫ u in s..t, F u) - C * (∫ u in s..t, H u) := by
    rw [← intervalIntegral.integral_interval_sub_left (hFi.mono_set (hsub0 t ht)) (hFi.mono_set (hsub0 s hs)),
      ← intervalIntegral.integral_interval_sub_left (hHi.mono_set (hsub0 t ht)) (hHi.mono_set (hsub0 s hs))]
    linarith [hbal s hs, hbal t ht]
  rw [intervalIntegral.integral_sub (hFi'.const_mul A) (hpI.const_mul C),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hdiff]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hpw hC) _

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ≥0} {ε : ℕ → ℝ}

lemma radiusMoment_nonneg {P : Measure Ω}
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hI : 0 ≤ initialGreen κ z) (b s : ℝ) :
    0 ≤ radiusMoment P c b s :=
  div_nonneg (integral_nonneg fun ω => limitRadiusKernel_nonneg c _ _ s ω) hI

lemma radiusMoment_intervalIntegrable {P : Measure Ω} [IsFiniteMeasure P]
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) {b u : ℝ} (hu : 0 ≤ u)
    (hi : Integrable (Function.uncurry (limitRadiusKernel c (codimension κ) (greenExponent κ - b)))
      ((volume.restrict (Ioc 0 u)).prod P)) : IntervalIntegrable (radiusMoment P c b) volume 0 u := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu]
  exact hi.integral_prod_left.div_const _

lemma radiusMoment_intervalIntegral {P : Measure Ω} [IsFiniteMeasure P]
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) {b u : ℝ} (hu : 0 ≤ u)
    (hi : Integrable (Function.uncurry (limitRadiusKernel c (codimension κ) (greenExponent κ - b)))
      ((volume.restrict (Ioc 0 u)).prod P)) :
    (∫ s in (0 : ℝ)..u, radiusMoment P c b s) =
      (∫ q : ℝ × Ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b) q.1 q.2
        ∂((volume.restrict (Ioc 0 u)).prod P)) / initialGreen κ z := by
  simp only [intervalIntegral.integral_of_le hu, radiusMoment, integral_div]
  congr 1
  exact (integral_prod _ hi).symm

lemma balance_divide {X H Y F A C : ℝ} (he : X + C * H = Y + A * F) (I : ℝ) :
    X / I + C * (H / I) = Y / I + A * (F / I) := by
  linear_combination (1 / I) * he

lemma radiusMoment_balance
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ)
    (u : ℝ) (hu : u ∈ Icc 0 (v : ℝ)) :
    radiusMoment P (a v) b u + (κ * b / 8) * (greenExponent κ - b) *
      (∫ s in (0 : ℝ)..u, radiusMoment P (a v) (b + 2) s) =
    powerLogDensity κ (codimension κ) (greenExponent κ - b) (initialLogCoordinates z) 0 / initialGreen κ z +
      (κ * b / 8) * (1 + (greenExponent κ - b)) *
        (∫ s in (0 : ℝ)..u, radiusMoment P (a v) b s) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨hi, he⟩ := limit_power_balance (a ⟨u, hu.1⟩) (a v) hε hεlim hε0 hB hBm hBc hB0
    hκ hκ8 b hb0 hb hu.1 hu.2
  dsimp only [NNReal.toReal] at hi he
  have hi' : Integrable (Function.uncurry (limitRadiusKernel (a v) (codimension κ) (greenExponent κ - (b + 2))))
      ((volume.restrict (Ioc 0 u)).prod P) := by
    rw [show greenExponent κ - (b + 2) = greenExponent κ - b - 2 by ring]
    convert hi using 1; rfl
  have hl := limitRadiusKernel_region_integrable (P := P) (a v) hε hBm (codimension κ)
    (greenExponent κ - b) (codimension_pos κ hκ8).le (sub_pos.mpr hb).le u
  rw [radiusMoment_intervalIntegral _ hu.1 hi', radiusMoment_intervalIntegral _ hu.1 hl]
  dsimp only [radiusMoment]
  rw [sub_add_eq_sub_sub]
  convert balance_divide he (initialGreen κ z) using 1 <;> rfl

 

theorem radiusMoment_drift
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ) :
    ContinuousOn (radiusMoment P (a v) b) (Icc 0 v) ∧
      ∀ s ∈ Icc 0 (v : ℝ), ∀ t ∈ Icc 0 (v : ℝ), s ≤ t →
        radiusMoment P (a v) b t - radiusMoment P (a v) b s ≤
          ∫ u in s..t, (κ * b / 8) * (1 + (greenExponent κ - b)) * radiusMoment P (a v) b u -
            (κ * b / 8) * (greenExponent κ - b) * (radiusMoment P (a v) b u) ^ (1 + 2 / b) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hI : 0 < initialGreen κ z := initialGreen_pos κ z hz
  have hh := (limit_power_balance (a v) (a v) hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb v.coe_nonneg le_rfl).1
  have hhigh : IntervalIntegrable (radiusMoment P (a v) (b + 2)) volume 0 v := by
    apply radiusMoment_intervalIntegrable _ v.coe_nonneg
    simpa only [sub_add_eq_sub_sub] using hh
  have hlow := radiusMoment_intervalIntegrable (P := P) (a v) v.coe_nonneg
    (limitRadiusKernel_region_integrable (a v) hε hBm (codimension κ) (greenExponent κ - b)
      (codimension_pos κ hκ8).le (sub_pos.mpr hb).le v)
  apply integral_drift_of_balance v.coe_nonneg (by positivity) (by positivity) hlow hhigh
    (radiusMoment_balance a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb)
  filter_upwards [hh.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with s hsi hs
  have hm := limitRadiusKernel_green_mean (a ⟨s, hs.1.le⟩) (a v) hε hεlim (fun n => (hε0 n).le)
    hB hBm hBc hB0 hκ hκ8 hz hs.1.le hs.2
  have hj := limitRadiusKernel_inverse_moment_jensen (a v) hε hBm (codimension κ)
    (greenExponent κ) b s (initialGreen κ z) (codimension_pos κ hκ8).le
    (greenExponent_pos κ hκ hκ8).le hb0 hb.le hI hm hsi
  simpa only [radiusMoment, sub_add_eq_sub_sub] using hj

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge


lemma finiteCenteredLaw_inverseAngle_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ≥0) (hu : 0 ≤ (u : ℝ))
    {ε : ℕ → ℝ} (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (b : ℝ) (hb : b ≤ greenExponent κ) :
    Integrable (fun ω => stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z u b)
      (finiteCenteredLaw P κ B γ G z u) ∧
    (∫ ω, stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z u b
      ∂finiteCenteredLaw P κ B γ G z u) = radiusMoment P a b u := by
  let w (ω : Ω) := stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u
  let f (ω : Ω) := stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z u b
  let d (ω : Ω) := ENNReal.ofReal (w ω / initialGreen κ z)
  have hwi := (finite_stopped_green_of_witness hB κ hκ hκ8 γ G F hw z hz u hu).1
  have hd : AEMeasurable d P := (hwi.div_const _).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hid : Integrable (limitRadiusKernel a (codimension κ) (greenExponent κ - b) u) P :=
    limitRadiusKernel_integrable a hε hBm _ _ (codimension_pos κ hκ8).le (sub_nonneg.mpr hb) u
  have he : (fun ω => (d ω).toReal • f ω) =ᵐ[P]
      (fun ω => limitRadiusKernel a (codimension κ) (greenExponent κ - b) u ω / initialGreen κ z) := by
    filter_upwards [hw] with ω hω
    have hw0 := stoppedGreen_nonneg hω κ z u
    rw [show (d ω).toReal = w ω / initialGreen κ z from
      ENNReal.toReal_ofReal (div_nonneg hw0 (initialGreen_pos κ z hz).le), smul_eq_mul]
    rw [limitRadiusKernel_inverse_factor,
      limitRadiusKernel_eq_stoppedGreen a hε hεlim hBc hz hu ω (γ ω) (G ω) (F ω) hω,
      limitRadiusKernel_eq_stoppedAngleSq a hε hεlim hBc hz hu ω (γ ω) (G ω) (F ω) hω]
    · change w ω / initialGreen κ z * f ω = w ω * f ω / initialGreen κ z
      ring
    · exact hε
  constructor
  · apply (integrable_withDensity_iff_integrable_smul₀' hd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    exact (hid.div_const _).congr he.symm
  · change (∫ ω, f ω ∂P.withDensity d) = _
    rw [integral_withDensity_eq_integral_toReal_smul₀ hd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), integral_congr_ae he, integral_div]
    rfl

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_zero_eq_indicator_level
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) (p : ℝ) :
    limitRadiusKernel a p 0 u ω =
      if radiusLevelTime γ G z u < ∞ then Real.exp (p * (u - Real.log 2 - Real.log z.im)) else 0 := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    rw [limitRadiusKernel_eq_stopped_of_live_level a hε hεlim hBc hz hu ω γ G F hw T hT hR,
      radiusLevelTime_eq_of_live_level ((hBc ω).const_mul _) hw z u T hT hR, ite_eq_left ENNReal.coe_lt_top,
      powerLogDensity_radius_angle κ p 0 (Real.log z.im), zero_div, Real.rpow_zero, mul_one,
      (fullRadius_level_iff_logClock ((hBc ω).const_mul _) hw z T hT u).mp hR]
  · rw [limitRadiusKernel_eq_zero_of_no_level a hBc hz ω γ G F hw _ _ hh,
      radiusLevelTime_eq_top_of_no_level γ G z u hh, ite_eq_right (lt_irrefl _)]

lemma integral_limitRadiusKernel_zero_eq_probability
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) (p : ℝ) :
    (∫ ω, limitRadiusKernel a p 0 u ω ∂P) =
      Real.exp (p * (u - Real.log 2 - Real.log z.im)) *
        (P {ω | radiusLevelTime (γ ω) (G ω) z u < ∞}).toReal := by
  let K := Real.exp (p * (u - Real.log 2 - Real.log z.im))
  let A := {ω | limitRadiusKernel a p 0 u ω ≠ 0}
  have hAm : MeasurableSet A := (measurableSet_eq_fun
    ((limitRadiusKernel_measurable a hε hBm p 0).comp (measurable_const.prodMk measurable_id)) measurable_const).compl
  have hA : A =ᵐ[P] {ω | radiusLevelTime (γ ω) (G ω) z u < ∞} := by
    filter_upwards [hw] with ω hω
    change (limitRadiusKernel a p 0 u ω ≠ 0) = (radiusLevelTime (γ ω) (G ω) z u < ∞)
    rw [limitRadiusKernel_zero_eq_indicator_level a hε hεlim hBc hz hu ω (γ ω) (G ω) (F ω) hω p]
    split_ifs with h <;> simp [h, Real.exp_ne_zero]
  have he : limitRadiusKernel a p 0 u = A.indicator (fun _ => K) := by
    funext ω
    rw [Set.indicator_apply]
    change limitRadiusKernel a p 0 u ω = if limitRadiusKernel a p 0 u ω ≠ 0 then K else 0
    simp only [limitRadiusKernel_zero, max_eq_left hu]
    split_ifs <;> simp_all [Real.exp_ne_zero, K]
  rw [he, integral_indicator hAm, setIntegral_const, smul_eq_mul, mul_comm]
  change K * (P A).toReal = _
  rw [measure_congr hA]

lemma initialGreen_div_zeroKernel (κ u : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    initialGreen κ z / Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) =
      Real.exp (-codimension κ * u) * (Real.sin (Complex.arg z)) ^ greenExponent κ := by
  have hr : 0 < 2 * z.im := mul_pos (by norm_num) hz
  rw [initialGreen, Real.rpow_def_of_pos hr, Real.log_mul (by norm_num) (ne_of_gt hz)]
  rw [mul_comm (Real.exp _) ((Real.sin (Complex.arg z)) ^ greenExponent κ),
    mul_div_assoc, ← Real.exp_sub]
  rw [show (Real.log 2 + Real.log z.im) * -codimension κ -
    codimension κ * (u - Real.log 2 - Real.log z.im) = -codimension κ * u by ring]
  ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

 

lemma liminf_slope_of_integral_bound {F G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hG : ContinuousOn G (Icc a b))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      F t - F s ≤ ∫ u in s..t, G u) :
    ∀ x ∈ Ico a b, ∀ r, G x < r → ∃ᶠ z in 𝓝[>] x, slope F x z < r := by
  let g (t : ℝ) := G (projIcc a b hab t)
  have hgc : Continuous g := hG.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc a b hab t).property)
  have he (t : ℝ) (ht : t ∈ Icc a b) : g t = G t := by
    simp only [g, projIcc_of_mem hab ht]
  intro x hx r hr
  have hd : HasDerivAt (fun z => ∫ u in a..z, g u) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      hgc.stronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).1
    (hd.hasDerivWithinAt : HasDerivWithinAt (fun z => ∫ u in a..z, g u) (g x) (Ioi x) x)
  have hsl : ∀ᶠ z in 𝓝[>] x, slope (fun y => ∫ u in a..y, g u) x z < r :=
    hs (Iio_mem_nhds (by rw [he x ⟨hx.1, hx.2.le⟩]; exact hr))
  apply Filter.Eventually.frequently
  filter_upwards [hsl, Ioc_mem_nhdsGT hx.2] with z hz hzI
  apply lt_of_le_of_lt _ hz
  rw [slope_def_field, slope_def_field,
    intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable a z) (hgc.intervalIntegrable a x)]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hzI.1).le
  rw [intervalIntegral.integral_congr (fun t ht => he t (by
    have ht' : t ∈ Icc x z := by simpa only [uIcc_of_le hzI.1.le] using ht
    exact ⟨hx.1.trans ht'.1, ht'.2.trans hzI.2⟩))]
  exact hinc x ⟨hx.1, hx.2.le⟩ z ⟨hx.1.trans hzI.1.le, hzI.2⟩ hzI.1.le

lemma image_le_of_integral_drift {F G H H' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → F t - F s ≤ ∫ u in s..t, G u)
    (ha : F a ≤ H a) (hH : ContinuousOn H (Icc a b))
    (hH' : ∀ x ∈ Ico a b, HasDerivWithinAt H (H' x) (Ici x) x)
    (hbound : ∀ x ∈ Ico a b, F x = H x → G x < H' x) :
    ∀ x ∈ Icc a b, F x ≤ H x := by
  exact fun x hx => image_le_of_liminf_slope_right_lt_deriv_boundary' hF
    (liminf_slope_of_integral_bound hab hG hinc) ha hH hH' hbound hx

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

lemma lyapunovBarrier_pos {r K δ t : ℝ} (hK : 0 < K) (ht : 0 < t + δ) :
    0 < lyapunovBarrier r K δ t := mul_pos (Real.rpow_pos_of_pos hK _) (Real.rpow_pos_of_pos ht _)

lemma lyapunovBarrier_deriv {r K δ t : ℝ} (ht : 0 < t + δ) :
    HasDerivAt (lyapunovBarrier r K δ) (-r * lyapunovBarrier r K δ t / (t + δ)) t := by
  have hd := (((hasDerivAt_id t).add_const δ).rpow_const (p := -r) (Or.inl ht.ne')).const_mul (K ^ r)
  convert hd using 1 <;> try rfl
  dsimp only [lyapunovBarrier, id_eq]
  rw [Real.rpow_sub ht, Real.rpow_one]
  ring

lemma lyapunovBarrier_power {r K δ t : ℝ} (hr : 0 < r) (hK : 0 < K) (ht : 0 < t + δ) :
    (lyapunovBarrier r K δ t) ^ (1 + 1 / r) =
      lyapunovBarrier r K δ t * K / (t + δ) := by
  have he : lyapunovBarrier r K δ t = (K / (t + δ)) ^ r := by
    rw [Real.div_rpow hK.le ht.le, lyapunovBarrier, Real.rpow_neg ht.le]
    rfl
  rw [he, ← Real.rpow_mul (div_pos hK ht).le]
  have hf : r * (1 + 1 / r) = r + 1 := by field_simp
  rw [hf, Real.rpow_add (div_pos hK ht), Real.rpow_one]
  ring

lemma exists_small_barrier {r K C : ℝ} (hr : 0 < r) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ C ≤ lyapunovBarrier r K δ 0 := by
  have ht : Tendsto (fun δ : ℝ => K ^ r * δ ^ (-r)) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hr)).const_mul_atTop (Real.rpow_pos_of_pos hK r)
  have he := (ht.eventually_ge_atTop C).and (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
  obtain ⟨δ, hd, hδ⟩ := he.exists
  exact ⟨δ, hδ.1, hδ.2, by simpa only [lyapunovBarrier, zero_add] using hd⟩

 

theorem comingDown_one_window {F : ℝ → ℝ} {v A C r : ℝ}
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hA : 0 ≤ A) (hC : 0 < C) (hr : 0 < r)
    (hF : ContinuousOn F (Icc 0 v))
    (hinc : ∀ s ∈ Icc 0 v, ∀ t ∈ Icc 0 v, s ≤ t →
      F t - F s ≤ ∫ u in s..t, A * F u - C * (F u) ^ (1 + 1 / r)) :
    ∀ t ∈ Ioc 0 v, F t ≤ ((2 * A + r + 1) / C / t) ^ r := by
  let K := (2 * A + r + 1) / C
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨δ, hδ, hδ1, hinit⟩ := exists_small_barrier (C := F 0) hr hK
  have hcont : ContinuousOn (lyapunovBarrier r K δ) (Icc 0 v) := by
    intro t ht
    exact (lyapunovBarrier_deriv (r := r) (K := K) (by linarith [ht.1] : 0 < t + δ)).continuousAt.continuousWithinAt
  have hq : 0 ≤ 1 + 1 / r := by positivity
  have hgc : ContinuousOn (fun u => A * F u - C * (F u) ^ (1 + 1 / r)) (Icc 0 v) :=
    (continuousOn_const.mul hF).sub (continuousOn_const.mul ((Real.continuous_rpow_const hq).comp_continuousOn hF))
  have hfence : ∀ t ∈ Icc 0 v, F t ≤ lyapunovBarrier r K δ t := by
    apply image_le_of_integral_drift hv hF hgc hinc hinit hcont
      (fun t ht => (lyapunovBarrier_deriv (r := r) (K := K) (by linarith [ht.1] : 0 < t + δ)).hasDerivWithinAt)
    intro t ht he
    have htδ : 0 < t + δ := by linarith [ht.1]
    have hH : 0 < lyapunovBarrier r K δ t := lyapunovBarrier_pos hK htδ
    rw [he, lyapunovBarrier_power hr hK htδ]
    apply (lt_div_iff₀ htδ).mpr
    have ht2 : t + δ ≤ 2 := by linarith [ht.2]
    have hk : C * K = 2 * A + r + 1 := by dsimp [K]; field_simp
    have htA : A * (t + δ) ≤ 2 * A := by nlinarith
    have hx : A * (t + δ) - C * K < -r := by linarith
    have hm := mul_lt_mul_of_pos_left hx hH
    field_simp at *
    nlinarith
  intro t ht
  apply (hfence t ⟨ht.1.le, ht.2⟩).trans
  have htδ : 0 < t + δ := by linarith [ht.1]
  have he : lyapunovBarrier r K δ t = (K / (t + δ)) ^ r := by
    rw [Real.div_rpow hK.le htδ.le, lyapunovBarrier, Real.rpow_neg htδ.le]
    rfl
  rw [he]
  exact Real.rpow_le_rpow (div_nonneg hK.le htδ.le)
    (div_le_div_of_nonneg_left hK.le ht.1 (by linarith)) hr.le

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

lemma comingDown_shifted {F : ℝ → ℝ} {v A C r : ℝ}
    (_hv : 0 ≤ v) (hA : 0 ≤ A) (hC : 0 < C) (hr : 0 < r)
    (hF : ContinuousOn F (Icc 0 v))
    (hinc : ∀ s ∈ Icc 0 v, ∀ t ∈ Icc 0 v, s ≤ t →
      F t - F s ≤ ∫ u in s..t, A * F u - C * (F u) ^ (1 + 1 / r))
    {x ℓ : ℝ} (hx : 0 ≤ x) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hxℓ : x + ℓ ≤ v) :
    F (x + ℓ) ≤ ((2 * A + r + 1) / C / ℓ) ^ r := by
  have hmap : MapsTo (fun s : ℝ => x + s) (Icc 0 ℓ) (Icc 0 v) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hcont : ContinuousOn (fun s => F (x + s)) (Icc 0 ℓ) :=
    hF.comp (continuous_const.add continuous_id).continuousOn hmap
  apply comingDown_one_window hℓ.le hℓ1 hA hC hr hcont ?_ ℓ ⟨hℓ, le_rfl⟩
  intro s hs t ht hst
  rw [intervalIntegral.integral_comp_add_left (fun u => A * F u - C * F u ^ (1 + 1 / r)) x]
  exact hinc _ (hmap hs) _ (hmap ht) (by linarith)

 

theorem comingDown_uniform {F : ℝ → ℝ} {v A C r η : ℝ}
    (hv : 0 ≤ v) (hA : 0 ≤ A) (hC : 0 < C) (hr : 0 < r)
    (hF : ContinuousOn F (Icc 0 v))
    (hinc : ∀ s ∈ Icc 0 v, ∀ t ∈ Icc 0 v, s ≤ t →
      F t - F s ≤ ∫ u in s..t, A * F u - C * (F u) ^ (1 + 1 / r))
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ t ∈ Icc η v, F t ≤ ((2 * A + r + 1) / C / η) ^ r := by
  intro t ht
  have hh := comingDown_shifted hv hA hC hr hF hinc (x := t - η) (sub_nonneg.mpr ht.1) hη hη1
    (by linarith [ht.2] : t - η + η ≤ v)
  simpa only [sub_add_cancel] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma lyapunovA_nonneg {κ b : ℝ} (hκ : 0 < κ) (hb0 : 0 < b) (hb : b < greenExponent κ) :
    0 ≤ lyapunovA κ b := by dsimp [lyapunovA]; positivity
lemma lyapunovC_pos {κ b : ℝ} (hκ : 0 < κ) (hb0 : 0 < b) (hb : b < greenExponent κ) :
    0 < lyapunovC κ b := by dsimp [lyapunovC]; positivity
lemma angularMomentBound_pos {κ b η : ℝ} (hκ : 0 < κ) (hb0 : 0 < b)
    (hb : b < greenExponent κ) (hη : 0 < η) : 0 < angularMomentBound κ b η := by
  have hA := lyapunovA_nonneg hκ hb0 hb
  have hC := lyapunovC_pos hκ hb0 hb
  dsimp only [angularMomentBound]
  apply Real.rpow_pos_of_pos
  positivity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ≥0} {ε : ℕ → ℝ}

 

theorem radiusMoment_bound
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ t ∈ Icc η (v : ℝ), radiusMoment P (a v) b t ≤ angularMomentBound κ b η := by
  obtain ⟨hc, hd⟩ := radiusMoment_drift a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 hz b hb0 hb (v := v)
  have he : 1 + 1 / (b / 2) = 1 + 2 / b := by field_simp
  apply comingDown_uniform v.coe_nonneg (lyapunovA_nonneg hκ hb0 hb) (lyapunovC_pos hκ hb0 hb)
    (by positivity : 0 < b / 2) hc ?_ hη hη1
  simpa only [he, lyapunovA, lyapunovC] using hd

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_antitone_power
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    (p α β s : ℝ) (hαβ : α ≤ β) (ω : Ω) :
    limitRadiusKernel c p β s ω ≤ limitRadiusKernel c p α s ω := by
  have he := limitRadiusKernel_power_factor c hε p α (β - α) s ω
  rw [show α + (β - α) = β by ring] at he
  rw [he]
  apply mul_le_of_le_one_right (limitRadiusKernel_nonneg c p α s ω)
  exact Real.rpow_le_one (limitRadiusKernel_nonneg c 0 2 s ω)
    (limitRadiusKernel_angle_le_one c s ω) (by linarith)

lemma integral_limitRadiusKernel_antitone_power
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    {P : Measure Ω} (p α β s : ℝ) (hαβ : α ≤ β)
    (hiα : Integrable (limitRadiusKernel c p α s) P)
    (hiβ : Integrable (limitRadiusKernel c p β s) P) :
    (∫ ω, limitRadiusKernel c p β s ω ∂P) ≤ ∫ ω, limitRadiusKernel c p α s ω ∂P :=
  integral_mono hiβ hiα (limitRadiusKernel_antitone_power c hε p α β s hαβ)

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RadiusClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radius Clocks for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge



theorem continuous_zero_hit_stopping
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (X : ℝ≥0 → Ω → ℝ) (hXa : Adapted ℱ X)
    (hXc : ∀ ω, Continuous (fun t => X t ω)) (n : ℝ≥0) :
    IsStoppingTime ℱ (hittingAfter X {0} n) := by
  intro T
  have he : {ω | hittingAfter X {0} n ω ≤ (T : WithTop ℝ≥0)} =
      {ω | ∃ t : Icc n T, X t ω = 0} := by
    ext ω
    simp only [mem_ofPred_eq, hittingAfter_zero_le_iff X hXc, Subtype.exists, exists_prop]
  rw [he]
  by_cases hnT : n ≤ T
  · let : Nonempty (Icc n T) := ⟨⟨n, le_rfl, hnT⟩⟩
    have hm (t : Icc n T) : @Measurable Ω ℝ (ℱ T) (borel ℝ) (X t) :=
      (hXa t).mono (ℱ.mono t.property.2) le_rfl
    let : MeasurableSpace Ω := ℱ T
    exact measurableSet_exists_zero_compact (fun t : Icc n T => X t) hm
      (fun ω => (hXc ω).comp continuous_subtype_val)
  · have hnil : IsEmpty (Icc n T) := ⟨fun t => hnT (t.property.1.trans t.property.2)⟩
    have : {ω | ∃ t : Icc n T, X t ω = 0} = ∅ := by ext ω; simp
    rw [this]
    exact @MeasurableSet.empty Ω (ℱ T)

end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StoppedKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopped Kernels for chordal SLE. -/

section
section


section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

lemma layerExponent_pos : 0 < layerExponent := by unfold layerExponent; positivity

end SLEExactGauge

end


section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

lemma layerGreenConstant_pos : 0 < layerGreenConstant := by
  unfold layerGreenConstant
  exact mul_pos (div_pos (by positivity) layerExponent_pos) (sq_pos_of_pos (by positivity))

end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_KernelConsistency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Consistency for chordal SLE. -/

section
section


section

open Set Filter Metric MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}



lemma IsCapacityTwoWitness.radius_ge_of_no_trace_approach
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    {r : ℝ} (hr : 0 < r) (hy : r ≤ z.im)
    (havoid : ∀ a ∈ Icc 0 t, r ≤ dist (γ a) z) : r ≤ fullRadius G t z := by
  by_contra hlt
  obtain ⟨a, ha, hd⟩ := h.trace_approach_of_radius_lt hU t z hz r hr hy (lt_of_not_ge hlt)
  exact (not_lt_of_ge (havoid a ha)) hd

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}

lemma physicalWeight_bound (a : AngularLocalization B hm κ z u ε)
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) (ω : Ω) :
    0 ≤ a.physicalWeight t ω ∧ a.physicalWeight t ω ≤
      Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) :=
  ⟨greenLogDensity_nonneg _ _ _, greenLogDensity_le_radius κ _ u hκ hκ8 _ _
    (a.inside ω _ (min_le_right _ _)).1⟩

lemma physicalWeight_adapted (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    StronglyAdapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) a.physicalWeight := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hQa : StronglyAdapted f (fun t : ℝ≥0 => a.solution.Q t) :=
    fun t => (a.solution.adapted t).stronglyMeasurable
  have hBa : StronglyAdapted f B := Filtration.stronglyAdapted_natural _
  have hg : StronglyAdapted f (fun t ω => greenLogDensity κ (a.solution.Q t ω) (B t ω)) := by
    intro t
    exact (greenLogDensity_contDiff κ).continuous.comp_stronglyMeasurable ((hQa t).prodMk (hBa t))
  have hc (ω : Ω) : Continuous (fun t : ℝ≥0 => greenLogDensity κ (a.solution.Q t ω) (B t ω)) :=
    (greenLogDensity_contDiff κ).continuous.comp
      (((a.solution.lipschitz ω).continuous.comp NNReal.continuous_coe).prodMk (hBc ω))
  have hs := hg.stoppedProcess hc a.stopping
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext t ω
  simp only [physicalWeight, stoppedProcess, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, NNReal.coe_min]

lemma physicalWeight_integrable (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) : Integrable (a.physicalWeight t) P := by
  apply Integrable.of_bound ((a.physicalWeight_adapted hBc t).mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le t)).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (a.physicalWeight_bound hκ hκ8 t ω).1]
  exact (a.physicalWeight_bound hκ hκ8 t ω).2

 

theorem physicalWeight_martingale (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    Martingale a.physicalWeight (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hmA := a.physicalWeight_adapted hBc
  have hi := a.physicalWeight_integrable (P := P) hBc hκ hκ8
  refine ⟨hmA, fun s t hst => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (f.le s) (hi t)
    (fun _ _ _ => (hi s).integrableOn) _ (hmA s).aestronglyMeasurable
  intro A hA _
  let σ (ω : Ω) : ℝ≥0 := if ω ∈ A then t else s
  have hσ : IsStoppingTime f (fun ω => (σ ω : WithTop ℝ≥0)) := by
    apply stopping_paste_after f (isStoppingTime_const f s) (isStoppingTime_const f t)
      (fun _ => hst)
    change MeasurableSet[(isStoppingTime_const f s).measurableSpace] A
    rw [IsStoppingTime.measurableSpace_const]
    exact hA
  let ρ (ω : Ω) : ℝ≥0 := min (σ ω) (a.τ ω)
  have hρ : IsStoppingTime f (fun ω => (ρ ω : WithTop ℝ≥0)) := by
    simpa only [ρ, WithTop.coe_min] using hσ.min a.stopping
  have hs : IsStoppingTime f (fun ω => (min s (a.τ ω) : WithTop ℝ≥0)) := by
    simpa only [WithTop.coe_min] using (isStoppingTime_const f s).min a.stopping
  have hin (ω : Ω) (v : ℝ≥0) (hv : v ≤ a.τ ω) :
      logRadiusClock (Real.log z.im) (a.solution.Q v ω) ≤ u ∧
        a.lo ≤ (a.solution.Q v ω).1.im ∧ (a.solution.Q v ω).1.im ≤ a.hi :=
    ⟨(a.inside ω v hv).1, (a.inside ω v hv).2.2⟩
  obtain ⟨hri, hre⟩ := a.solution.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    (Real.log z.im) u ρ hρ a.T (fun ω => (min_le_right _ _).trans (a.bounded ω))
    (fun ω v hv => hin ω v (hv.trans (min_le_right _ _)))
  obtain ⟨hsi, hse⟩ := a.solution.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    (Real.log z.im) u (fun ω => min s (a.τ ω)) hs a.T
    (fun ω => (min_le_right _ _).trans (a.bounded ω))
    (fun ω v hv => hin ω v (hv.trans (min_le_right _ _)))
  have he (ω : Ω) :
      greenLogDensity κ (a.solution.Q (ρ ω) ω) (B (ρ ω) ω) - a.physicalWeight s ω =
        A.indicator (fun ω => a.physicalWeight t ω - a.physicalWeight s ω) ω := by
    by_cases hω : ω ∈ A <;> simp [physicalWeight, ρ, σ, hω]
  have heI : (∫ ω, A.indicator (fun ω => a.physicalWeight t ω - a.physicalWeight s ω) ω ∂P) = 0 := by
    simp_rw [← he]
    rw [integral_sub hri (hi s)]
    change (∫ ω, greenLogDensity κ (a.solution.Q (ρ ω) ω) (B (ρ ω) ω) ∂P) -
      (∫ ω, greenLogDensity κ (a.solution.Q (min s (a.τ ω)) ω) (B (min s (a.τ ω)) ω) ∂P) = 0
    have hse' : (∫ ω, greenLogDensity κ (a.solution.Q (min (s : ℝ) (a.τ ω)) ω)
        (B (min s (a.τ ω)) ω) ∂P) = greenLogDensity κ (initialLogCoordinates z) 0 := by
      simpa only [NNReal.coe_min] using hse
    rw [hre, hse', sub_self]
  rw [integral_indicator (f.le s _ hA), integral_sub (hi t).integrableOn (hi s).integrableOn] at heI
  exact (sub_eq_zero.mp heI).symm

end AngularLocalization
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u v ε δ : ℝ}

lemma stopping_le_of_hit (a : AngularLocalization B hm κ z u ε)
    (b : AngularLocalization B hm κ z v δ) (huv : u ≤ v) (ω : Ω)
    (hb : ω ∈ b.hit) : a.τ ω ≤ b.τ ω := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have he := a.synchronize b ω (b.τ ω) hlt.le le_rfl
  have hh := (a.before ω _ hlt).1
  rw [he, show logRadiusClock (Real.log z.im) (b.solution.Q (b.τ ω) ω) = v from hb] at hh
  exact (not_lt_of_ge huv) hh

end AngularLocalization

end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_AngularMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Moments for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma physicalWeight_exists_limit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) (ω : Ω) :
    ∃ l : ℝ, Tendsto (fun n => (a n).physicalWeight t ω) atTop (𝓝 l) := by
  by_cases ht : ∃ n, t ≤ (a n).τ ω
  · obtain ⟨n, hn⟩ := ht
    refine ⟨(a n).physicalWeight t ω, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop n] with m hnm
    have hm' := hn.trans ((a n).stopping_le (a m) le_rfl (hε hnm) ω)
    simp only [AngularLocalization.physicalWeight, ← NNReal.coe_min, min_eq_left hn, min_eq_left hm']
    rw [(a n).synchronize (a m) ω t hn hm']
  · by_cases hh : ∃ n, ω ∈ (a n).hit
    · obtain ⟨n, hn⟩ := hh
      refine ⟨(a n).physicalWeight t ω, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [eventually_ge_atTop n] with m hnm
      have heτ : (a n).τ ω = (a m).τ ω := le_antisymm
        ((a n).stopping_le (a m) le_rfl (hε hnm) ω)
        ((a m).stopping_le_of_hit (a n) le_rfl ω hn)
      have hnt : (a n).τ ω ≤ t := (lt_of_not_ge (fun h => ht ⟨n, h⟩)).le
      have hmt : (a m).τ ω ≤ t := heτ ▸ hnt
      simp only [AngularLocalization.physicalWeight, ← NNReal.coe_min, min_eq_right hnt, min_eq_right hmt]
      rw [(a n).synchronize (a m) ω ((a n).τ ω) le_rfl heτ.le, heτ]
    · refine ⟨0, ?_⟩
      have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
      let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
      have hpow : Tendsto (fun n => K * ε n ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
        have hx := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hεlim).const_mul K
        simpa only [Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using hx
      apply squeeze_zero (fun n => ((a n).physicalWeight_bound hκ hκ8 t ω).1) _ hpow
      intro n
      have hnt : (a n).τ ω ≤ t := (lt_of_not_ge (fun h => ht ⟨n, h⟩)).le
      change greenLogDensity κ _ _ ≤ _
      rw [← NNReal.coe_min, min_eq_right hnt]
      exact (a n).weight_small_of_not_hit hκ hκ8 ω (fun hn => hh ⟨n, hn⟩)

lemma physicalWeight_tendsto_limit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => (a n).physicalWeight t ω) atTop (𝓝 (physicalGreenLimit a t ω)) := by
  obtain ⟨l, hl⟩ := physicalWeight_exists_limit a hε hεlim hκ hκ8 t ω
  simpa only [physicalGreenLimit, hl.limUnder_eq] using hl

lemma physicalGreenLimit_bound
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) (ω : Ω) :
    0 ≤ physicalGreenLimit a t ω ∧ physicalGreenLimit a t ω ≤
      Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) := by
  have ht := physicalWeight_tendsto_limit a hε hεlim hκ hκ8 t ω
  exact ⟨ge_of_tendsto ht (Eventually.of_forall fun n => ((a n).physicalWeight_bound hκ hκ8 t ω).1),
    le_of_tendsto ht (Eventually.of_forall fun n => ((a n).physicalWeight_bound hκ hκ8 t ω).2)⟩

lemma physicalGreenLimit_adapted
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    StronglyAdapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) (physicalGreenLimit a) := by
  intro t
  have hs (n : ℕ) := (a n).physicalWeight_adapted hBc t
  let : MeasurableSpace Ω := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) t
  exact StronglyMeasurable.limUnder hs

lemma physicalGreenLimit_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} [IsFiniteMeasure P] (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) : Integrable (physicalGreenLimit a t) P := by
  apply Integrable.of_bound ((physicalGreenLimit_adapted a hBc t).mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le t)).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (physicalGreenLimit_bound a hε hεlim hκ hκ8 t ω).1]
  exact (physicalGreenLimit_bound a hε hεlim hκ hκ8 t ω).2

 

theorem physicalGreenLimit_martingale
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    Martingale (physicalGreenLimit a) (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) P := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have had := physicalGreenLimit_adapted a hBc
  have hi := physicalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8
  have hmar (n : ℕ) := (a n).physicalWeight_martingale hB hBm hBc hB0 hκ hκ8
  refine ⟨had, fun s t hst => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (f.le s) (hi t)
    (fun _ _ _ => (hi s).integrableOn) _ (had s).aestronglyMeasurable
  intro A hA _
  have hlim (v : ℝ≥0) : Tendsto (fun n => ∫ ω in A, (a n).physicalWeight v ω ∂P) atTop
      (𝓝 (∫ ω in A, physicalGreenLimit a v ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => ((a n).physicalWeight_integrable (P := P) hBc hκ hκ8 v).integrableOn.aestronglyMeasurable)
      (integrable_const _) _ (Eventually.of_forall (physicalWeight_tendsto_limit a hε hεlim hκ hκ8 v))
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).physicalWeight_bound hκ hκ8 v ω).1]
    exact ((a n).physicalWeight_bound hκ hκ8 v ω).2
  apply tendsto_nhds_unique (hlim s)
  convert hlim t using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact (hmar n).setIntegral_eq hst hA

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma physicalWeight_tendsto_source
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) γ G F) (t : ℝ≥0) :
    Tendsto (fun n => (a n).physicalWeight t ω) atTop
      (𝓝 (physicalStoppedGreen κ (fun s => Real.sqrt κ * B s ω) γ G z u t)) := by
  have hU := (hBc ω).const_mul (Real.sqrt κ)
  have hρ := localizedRadiusStop_eq_source a hεlim hBc hz ω γ G F hw
  by_cases hrt : radiusLevelTime γ G z u ≤ (t : ℝ≥0∞)
  · rw [physicalStoppedGreen, ite_eq_left hrt]
    have hρt : localizedRadiusStop a ω ≤ (t : WithTop ℝ≥0) := by
      rw [hρ]
      exact hrt
    obtain ⟨n, hn, hnt⟩ := (localizedRadiusStop_le_iff a ω t).mp hρt
    obtain ⟨hl, hR⟩ := (a n).radius_at_hit hBc hz ω γ G F hw hn
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_hit_of_live_level a hεlim hBc hz ω γ G F hw ((a n).τ ω) hl hR]
      with m hm'
    have ht' : (a m).τ ω ≤ t := hm'.2.le.trans hnt
    simpa only [AngularLocalization.physicalWeight, ← NNReal.coe_min, min_eq_right ht', AngularLocalization.weight]
      using ((a m).weight_eq_stoppedGreen_of_hit hBc hz ω γ G F hw hm'.1).symm
  · rw [physicalStoppedGreen, ite_eq_right hrt]
    have hno (n : ℕ) (hnt : (a n).τ ω ≤ t) : ω ∉ (a n).hit := by
      intro hn
      apply hrt
      have hcan := (localizedRadiusStop_le_iff a ω t).mpr ⟨n, hn, hnt⟩
      rw [hρ] at hcan
      exact hcan
    by_cases hl : z ∈ survivingDomain γ t
    · obtain ⟨δ, hδ, hδb⟩ := live_angleSq_lower_bound hU hw z t hl
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_order.mp hεlim).2 δ hδ] with n hn
      have hbefore : t ≤ (a n).τ ω := by
        by_contra hnt
        have hnt' := lt_of_not_ge hnt
        have hexit := ((a n).boundary ω).resolve_left (hno n hnt'.le)
        obtain ⟨hla, heq⟩ := (a n).chart_identification hBc hz ω γ G F hw
        have ha : logAngleSq κ ((a n).solution.Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) =
          (Real.sin (Complex.arg (G ((a n).τ ω) z - ((Real.sqrt κ * B ((a n).τ ω) ω : ℝ) : ℂ)))) ^ 2 := by
          rw [heq _ le_rfl]
          exact logAngleSq_logCoordinates κ _ G z _ (hw.imag_positive _ z hla)
        have hb := hδb ((a n).τ ω) hnt'.le
        rw [← ha, hexit] at hb
        exact (not_lt_of_ge hb) hn
      dsimp only [AngularLocalization.physicalWeight]
      rw [← NNReal.coe_min, min_eq_left hbefore, ((a n).chart_identification hBc hz ω γ G F hw).2 t hbefore]
      exact (greenLogDensity_logCoordinates hU hw κ _ z t hl rfl).symm
    · have hnt (n : ℕ) : (a n).τ ω < t := by
        apply lt_of_not_ge
        intro hn
        exact hl (survivingDomain_antitone γ hn ((a n).chart_identification hBc hz ω γ G F hw).1)
      rw [greenDensity, ite_eq_right hl]
      have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
      let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
      have hpow : Tendsto (fun n => K * ε n ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
        have hx := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hεlim).const_mul K
        simpa only [Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using hx
      apply squeeze_zero (fun n => ((a n).physicalWeight_bound hκ hκ8 t ω).1) _ hpow
      intro n
      change greenLogDensity κ _ _ ≤ _
      rw [← NNReal.coe_min, min_eq_right (hnt n).le]
      exact (a n).weight_small_of_not_hit hκ hκ8 ω (hno n (hnt n).le)

lemma physicalGreenLimit_eq_source
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) γ G F) (t : ℝ≥0) :
    physicalGreenLimit a t ω = physicalStoppedGreen κ (fun s => Real.sqrt κ * B s ω) γ G z u t :=
  (physicalWeight_tendsto_source a hεlim hBc hκ hκ8 hz ω γ G F hw t).limUnder_eq

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma localization_weight_tendsto_limit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hκ : 0 < κ) (hκ8 : κ < 8) (ω : Ω) :
    Tendsto (fun n => (a n).weight ω) atTop (𝓝 (terminalGreenLimit a ω)) := by
  suffices ∃ l : ℝ, Tendsto (fun n => (a n).weight ω) atTop (𝓝 l) by
    obtain ⟨l, hl⟩ := this
    simpa only [terminalGreenLimit, hl.limUnder_eq] using hl
  by_cases hh : ∃ n, ω ∈ (a n).hit
  · obtain ⟨n, hn⟩ := hh
    refine ⟨(a n).weight ω, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [eventually_ge_atTop n] with m hnm
    have ht : (a n).τ ω = (a m).τ ω := le_antisymm
      ((a n).stopping_le (a m) le_rfl (hε hnm) ω)
      ((a m).stopping_le_of_hit (a n) le_rfl ω hn)
    have he := (a n).synchronize (a m) ω ((a n).τ ω) le_rfl ht.le
    simp only [AngularLocalization.weight]
    rw [he, ht]
  · refine ⟨0, ?_⟩
    have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
    let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
    have ht : Tendsto (fun n => K * ε n ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
      have hx := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hεlim).const_mul K
      simpa only [Real.zero_rpow hp.ne', mul_zero, Function.comp_def] using hx
    apply squeeze_zero (fun n => ((a n).weight_bound hκ hκ8 ω).1) _ ht
    intro n
    exact (a n).weight_small_of_not_hit hκ hκ8 ω (fun hn => hh ⟨n, hn⟩)

lemma terminalGreenLimit_bound
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hκ : 0 < κ) (hκ8 : κ < 8) (ω : Ω) :
    0 ≤ terminalGreenLimit a ω ∧ terminalGreenLimit a ω ≤
      Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) := by
  have ht := localization_weight_tendsto_limit a hε hεlim hκ hκ8 ω
  exact ⟨ge_of_tendsto ht (Eventually.of_forall fun n => ((a n).weight_bound hκ hκ8 ω).1),
    le_of_tendsto ht (Eventually.of_forall fun n => ((a n).weight_bound hκ hκ8 ω).2)⟩

lemma terminalGreenLimit_stronglyMeasurable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) : StronglyMeasurable (terminalGreenLimit a) := by
  have hs (n : ℕ) := ((a n).physicalWeight_adapted hBc (a n).T).mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le (a n).T)
  have hs' (n : ℕ) : StronglyMeasurable ((a n).weight) := by
    convert hs n using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min,
      min_eq_right ((a n).bounded ω)]
  exact StronglyMeasurable.limUnder hs'

lemma terminalGreenLimit_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} [IsFiniteMeasure P] (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) : Integrable (terminalGreenLimit a) P := by
  apply Integrable.of_bound (terminalGreenLimit_stronglyMeasurable a hBc).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (terminalGreenLimit_bound a hε hεlim hκ hκ8 ω).1]
  exact (terminalGreenLimit_bound a hε hεlim hκ hκ8 ω).2

 

theorem physicalGreenLimit_condExp_terminal
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ωω, Continuous (fun t => B t ωω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (t : ℝ≥0) :
    physicalGreenLimit a t =ᵐ[P]
      P[terminalGreenLimit a | (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) t] := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hi := terminalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8
  apply ae_eq_condExp_of_forall_setIntegral_eq (f.le t) hi
    (fun _ _ _ => (physicalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8 t).integrableOn)
    _ (physicalGreenLimit_adapted a hBc t).aestronglyMeasurable
  intro A hA _
  have hlim₁ : Tendsto (fun n => ∫ ω in A, (a n).physicalWeight t ω ∂P) atTop
      (𝓝 (∫ ω in A, physicalGreenLimit a t ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => ((a n).physicalWeight_integrable (P := P) hBc hκ hκ8 t).integrableOn.aestronglyMeasurable)
      (integrable_const _) _ (Eventually.of_forall (physicalWeight_tendsto_limit a hε hεlim hκ hκ8 t))
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).physicalWeight_bound hκ hκ8 t ω).1]
    exact ((a n).physicalWeight_bound hκ hκ8 t ω).2
  have hw (n : ℕ) : (a n).physicalWeight (max t (a n).T) = (a n).weight := by
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min,
      min_eq_right (((a n).bounded ω).trans (le_max_right _ _))]
  have hwi (n : ℕ) : Integrable ((a n).weight) P := by
    rw [← hw n]
    exact (a n).physicalWeight_integrable (P := P) hBc hκ hκ8 _
  have hlim₂ : Tendsto (fun n => ∫ ω in A, (a n).weight ω ∂P) atTop
      (𝓝 (∫ ω in A, terminalGreenLimit a ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => (hwi n).integrableOn.aestronglyMeasurable) (integrable_const _) _
      (Eventually.of_forall (localization_weight_tendsto_limit a hε hεlim hκ hκ8))
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).weight_bound hκ hκ8 ω).1]
    exact ((a n).weight_bound hκ hκ8 ω).2
  apply tendsto_nhds_unique hlim₁
  convert hlim₂ using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [← hw n]
  exact ((a n).physicalWeight_martingale hB hBm hBc hB0 hκ hκ8).setIntegral_eq (le_max_left _ _) hA

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma terminalGreenLimit_measurable_at_infinity
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    StronglyMeasurable[⨆ n, naturalNatFiltration B hm n] (terminalGreenLimit a) := by
  have hs (n : ℕ) : StronglyMeasurable[⨆ n, naturalNatFiltration B hm n] ((a n).weight) := by
    obtain ⟨m, hm'⟩ := exists_nat_ge (a n).T
    have hme := ((a n).physicalWeight_adapted hBc (a n).T).mono
      (((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).mono hm').trans
        (show naturalNatFiltration B hm m ≤ ⨆ n, naturalNatFiltration B hm n from le_iSup _ m))
    convert hme using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min,
      min_eq_right ((a n).bounded ω)]
  let : MeasurableSpace Ω := ⨆ n, naturalNatFiltration B hm n
  exact StronglyMeasurable.limUnder hs

theorem physicalGreenLimit_tendsto_at_infinity
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => physicalGreenLimit a n ω) atTop (𝓝 (terminalGreenLimit a ω)) := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  have hi := terminalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8
  have ht := hi.tendsto_ae_condExp (ℱ := naturalNatFiltration B hm)
    (terminalGreenLimit_measurable_at_infinity a hBc)
  have he : ∀ᵐ ω ∂P, ∀ n : ℕ, physicalGreenLimit a n ω =
      P[terminalGreenLimit a | naturalNatFiltration B hm n] ω := by
    rw [ae_all_iff]
    intro n
    exact physicalGreenLimit_condExp_terminal a hε hεlim hB hBm hBc hB0 hκ hκ8 n
  filter_upwards [ht, he] with ω hω heω
  simpa only [heω] using hω

lemma terminalGreenLimit_eq_source
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) γ G F) :
    terminalGreenLimit a ω = stoppedGreen κ (fun s => Real.sqrt κ * B s ω) γ G z u :=
  (localization_weight_tendsto a hεlim hBc hκ hκ8 hz ω γ G F hw).limUnder_eq

 

theorem killedGreen_tendsto_zero_of_no_radius
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω)) :
    ∀ᵐ ω ∂P, radiusLevelTime (γ ω) (G ω) z u = ∞ →
      Tendsto (fun n : ℕ => greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) n z)
        atTop (𝓝 0) := by
  filter_upwards [hw, physicalGreenLimit_tendsto_at_infinity a hε hεlim hB hBm hBc hB0 hκ hκ8]
    with ω hω ht
  intro hn
  have ht' : terminalGreenLimit a ω = 0 := by
    rw [terminalGreenLimit_eq_source a hεlim hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω]
    simp only [stoppedGreen, hn, lt_irrefl, ite_false]
  rw [ht'] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [physicalGreenLimit_eq_source a hεlim hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω n,
    physicalStoppedGreen, hn, ite_eq_right (by exact not_le.mpr (ENNReal.coe_lt_top (r := (n : ℝ≥0))))]

end SLEExactGauge

end


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ}

lemma physicalWeight_continuous (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    Continuous (fun t => a.physicalWeight t ω) := by
  have hc : Continuous (fun t : ℝ≥0 => min t (a.τ ω)) := continuous_id.min continuous_const
  exact (greenLogDensity_contDiff κ).continuous.comp
    ((((a.solution.lipschitz ω).continuous.comp NNReal.continuous_coe).comp hc).prodMk
      ((hBc ω).comp hc))

lemma physicalWeight_stopping_measurable (a : AngularLocalization B hm κ z u ε)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Measurable[hσ.measurableSpace] (fun ω => a.physicalWeight (σ ω) ω) := by
  have hp := (a.physicalWeight_adapted hBc).isStronglyProgressive_of_continuous
    (a.physicalWeight_continuous hBc)
  exact measurable_stoppedValue hp hσ

lemma physicalWeight_stopping_integrable (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => a.physicalWeight (σ ω) ω) P := by
  apply Integrable.of_bound
    ((a.physicalWeight_stopping_measurable hBc σ hσ).mono hσ.measurableSpace_le le_rfl).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (a.physicalWeight_bound hκ hκ8 (σ ω) ω).1]
  exact (a.physicalWeight_bound hκ hκ8 (σ ω) ω).2

 

lemma integral_physicalWeight_stopping (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    (∫ ω, a.physicalWeight (σ ω) ω ∂P) = greenLogDensity κ (initialLogCoordinates z) 0 := by
  let ρ (ω : Ω) : ℝ≥0 := min (σ ω) (a.τ ω)
  have hρ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (ρ ω : WithTop ℝ≥0)) := by
    simpa only [ρ, WithTop.coe_min] using hσ.min a.stopping
  have hin (ω : Ω) (v : ℝ≥0) (hv : v ≤ ρ ω) :
      logRadiusClock (Real.log z.im) (a.solution.Q v ω) ≤ u ∧
        a.lo ≤ (a.solution.Q v ω).1.im ∧ (a.solution.Q v ω).1.im ≤ a.hi := by
    have hh := a.inside ω v (hv.trans (min_le_right _ _))
    exact ⟨hh.1, hh.2.2⟩
  have hh := (a.solution.stopped_green_bounded_clock hB hBm hBc hB0 hκ hκ8
    (Real.log z.im) u ρ hρ a.T (fun ω => (min_le_right _ _).trans (a.bounded ω)) hin).2
  simpa only [ρ, physicalWeight, NNReal.coe_min] using hh

lemma physicalWeight_setIntegral_stopping (a : AngularLocalization B hm κ z u ε)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    (∫ ω in A, a.physicalWeight (σ ω) ω ∂P) =
      ∫ ω in A, a.physicalWeight (τ ω) ω ∂P := by
  let _ := hB.isGaussianProcess.isProbabilityMeasure
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let ρ (ω : Ω) : ℝ≥0 := if ω ∈ A then τ ω else σ ω
  have hρ : IsStoppingTime f (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    stopping_paste_after f hσ hτ hστ hA
  have hiσ := a.physicalWeight_stopping_integrable (P := P) hBc hκ hκ8 σ hσ
  have hiρ := a.physicalWeight_stopping_integrable (P := P) hBc hκ hκ8 ρ hρ
  have hiτ := a.physicalWeight_stopping_integrable (P := P) hBc hκ hκ8 τ hτ
  have he (ω : Ω) : a.physicalWeight (ρ ω) ω - a.physicalWeight (σ ω) ω =
      A.indicator (fun ω => a.physicalWeight (τ ω) ω - a.physicalWeight (σ ω) ω) ω := by
    by_cases hω : ω ∈ A <;> simp [ρ, hω]
  have heI : (∫ ω, A.indicator (fun ω => a.physicalWeight (τ ω) ω -
      a.physicalWeight (σ ω) ω) ω ∂P) = 0 := by
    simp_rw [← he]
    rw [integral_sub hiρ hiσ,
      a.integral_physicalWeight_stopping hB hBm hBc hB0 hκ hκ8 ρ hρ,
      a.integral_physicalWeight_stopping hB hBm hBc hB0 hκ hκ8 σ hσ, sub_self]
  rw [integral_indicator (hσ.measurableSpace_le _ hA),
    integral_sub hiτ.integrableOn hiσ.integrableOn] at heI
  exact (sub_eq_zero.mp heI).symm

end AngularLocalization
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma physicalGreenLimit_stopping_measurable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    StronglyMeasurable[hσ.measurableSpace] (fun ω => physicalGreenLimit a (σ ω) ω) := by
  have hs (n : ℕ) : StronglyMeasurable[hσ.measurableSpace]
      (fun ω => (a n).physicalWeight (σ ω) ω) :=
    ((a n).physicalWeight_stopping_measurable hBc σ hσ).stronglyMeasurable
  let : MeasurableSpace Ω := hσ.measurableSpace
  exact StronglyMeasurable.limUnder hs

lemma physicalGreenLimit_stopping_integrable
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => physicalGreenLimit a (σ ω) ω) P := by
  apply Integrable.of_bound
    ((physicalGreenLimit_stopping_measurable a hBc σ hσ).mono hσ.measurableSpace_le).aestronglyMeasurable
    (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (physicalGreenLimit_bound a hε hεlim hκ hκ8 (σ ω) ω).1]
  exact (physicalGreenLimit_bound a hε hεlim hκ hκ8 (σ ω) ω).2

 

end SLEExactGauge
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_InverseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse Moments for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}
theorem physicalGreenLimit_stopping_condExp_terminal
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    (fun ω => physicalGreenLimit a (σ ω) ω) =ᵐ[P]
      P[terminalGreenLimit a | hσ.measurableSpace] := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hi := terminalGreenLimit_integrable a hε hεlim (P := P) hBc hκ hκ8
  apply ae_eq_condExp_of_forall_setIntegral_eq hσ.measurableSpace_le hi
    (fun _ _ _ => (physicalGreenLimit_stopping_integrable a hε hεlim (P := P) hBc hκ hκ8 σ hσ).integrableOn)
    _ (physicalGreenLimit_stopping_measurable a hBc σ hσ).aestronglyMeasurable
  intro A hA _
  have hlim₁ : Tendsto (fun n => ∫ ω in A, (a n).physicalWeight (σ ω) ω ∂P) atTop
      (𝓝 (∫ ω in A, physicalGreenLimit a (σ ω) ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => ((a n).physicalWeight_stopping_integrable (P := P) hBc hκ hκ8 σ hσ).integrableOn.aestronglyMeasurable)
      (integrable_const _) _
      (Eventually.of_forall fun ω => physicalWeight_tendsto_limit a hε hεlim hκ hκ8 (σ ω) ω)
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).physicalWeight_bound hκ hκ8 (σ ω) ω).1]
    exact ((a n).physicalWeight_bound hκ hκ8 (σ ω) ω).2
  have hwi (n : ℕ) : Integrable ((a n).weight) P := by
    have hh := (a n).physicalWeight_integrable (P := P) hBc hκ hκ8 (a n).T
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min,
      min_eq_right ((a n).bounded ω)]
  have hlim₂ : Tendsto (fun n => ∫ ω in A, (a n).weight ω ∂P) atTop
      (𝓝 (∫ ω in A, terminalGreenLimit a ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
      (fun n => (hwi n).integrableOn.aestronglyMeasurable)
      (integrable_const _) _
      (Eventually.of_forall (localization_weight_tendsto_limit a hε hεlim hκ hκ8))
    intro n
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).weight_bound hκ hκ8 ω).1]
    exact ((a n).weight_bound hκ hκ8 ω).2
  have he (n : ℕ) : (∫ ω in A, (a n).physicalWeight (σ ω) ω ∂P) =
      ∫ ω in A, (a n).weight ω ∂P := by
    let τ (ω : Ω) : ℝ≥0 := max (σ ω) (a n).T
    have hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0)) := by
      simpa only [τ, WithTop.coe_max] using hσ.max
        (isStoppingTime_const (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) (a n).T)
    have hx := (a n).physicalWeight_setIntegral_stopping hB hBm hBc hB0 hκ hκ8 σ τ hσ hτ
      (fun ω => le_max_left _ _) hA
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext ω
    simp only [AngularLocalization.physicalWeight, AngularLocalization.weight, ← NNReal.coe_min, τ,
      min_eq_right (((a n).bounded ω).trans (le_max_right _ _))]
  apply tendsto_nhds_unique hlim₁
  simpa only [he] using hlim₂

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem exists_physical_green_stopping_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    let hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
    ∃ (M : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ),
      Martingale M (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) P ∧
      Integrable Z P ∧
      (∀ t ω, 0 ≤ M t ω ∧ M t ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))) ∧
      (∀ ω, 0 ≤ Z ω ∧ Z ω ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))) ∧
      (∀ t, M t =ᵐ[P] P[Z | (Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t]) ∧
      (∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime
          (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
          (fun ω => (σ ω : WithTop ℝ≥0))),
        (fun ω => M (σ ω) ω) =ᵐ[P] P[Z | hσ.measurableSpace]) ∧
      (∀ᵐ ω ∂P, (∀ t, M t ω = physicalStoppedGreen κ (fun s => Real.sqrt κ * B s ω)
          (γ ω) (G ω) z u t) ∧
        Z ω = stoppedGreen κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) z u) ∧
      (∀ᵐ ω ∂P, radiusLevelTime (γ ω) (G ω) z u = ∞ →
        Tendsto (fun n : ℕ => greenDensity κ (fun s => Real.sqrt κ * B s ω)
          (γ ω) (G ω) n z) atTop (𝓝 0)) := by
  dsimp only
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε0 (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεA (n : ℕ) : ε n ≤ A₀ := div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  have hεanti : Antitone ε := by
    intro n m hnm
    exact div_le_div_of_nonneg_left hA₀.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  let a (n : ℕ) : AngularLocalization B hm κ z u (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z u (ε n)
      hu (hε0 n) (hεA n))
  refine ⟨physicalGreenLimit a, terminalGreenLimit a,
    physicalGreenLimit_martingale a hεanti hεlim hB hBm hBc hB0 hκ hκ8,
    terminalGreenLimit_integrable a hεanti hεlim hBc hκ hκ8,
    physicalGreenLimit_bound a hεanti hεlim hκ hκ8,
    terminalGreenLimit_bound a hεanti hεlim hκ hκ8,
    physicalGreenLimit_condExp_terminal a hεanti hεlim hB hBm hBc hB0 hκ hκ8,
    (fun σ hσ => physicalGreenLimit_stopping_condExp_terminal a hεanti hεlim hB hBm hBc hB0 hκ hκ8 σ hσ), ?_,
    killedGreen_tendsto_zero_of_no_radius a hεanti hεlim hB hBm hBc hB0 hκ hκ8 hz γ G F hw⟩
  filter_upwards [hw] with ω hω
  exact ⟨fun t => physicalGreenLimit_eq_source a hεlim hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω t,
    terminalGreenLimit_eq_source a hεlim hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω⟩

end SLEExactGauge

end


section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma spatialHitTime_lt_of_dist_lt {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hstart : r ≤ dist (γ 0) z)
    (t : ℝ≥0) (ht : dist (γ t) z < r) : spatialHitTime γ z r < t := by
  obtain ⟨s, hs, he⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ t from bot_le)
    (hc.dist continuous_const).continuousOn ⟨ht.le, hstart⟩
  have hst : s < t := lt_of_le_of_ne hs.2 (by intro h; subst s; exact ht.ne he)
  exact ((spatialHitTime_le_iff hc z r s).mpr ⟨s, ⟨bot_le, le_rfl⟩, he⟩).trans_lt
    (WithTop.coe_lt_coe.mpr hst)

lemma IsCapacityTwoWitness.radius_hit_forces_spatial_before
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hlevel : (2 * z.im) * Real.exp (-u) < r) (t : ℝ≥0)
    (hτ : radiusLevelTime γ G z u ≤ (t : ℝ≥0∞)) : spatialHitTime γ z r < t := by
  have hex : ∃ a : ℝ≥0, z ∈ survivingDomain γ a ∧
      fullRadius G a z = (2 * z.im) * Real.exp (-u) := by
    by_contra hn
    rw [radiusLevelTime_eq_top_of_no_level γ G z u hn] at hτ
    exact ENNReal.not_top_le_coe hτ
  obtain ⟨a, ha, hR⟩ := hex
  have hat : a ≤ t := by
    rw [radiusLevelTime_eq_of_live_level hU h z u a ha hR] at hτ
    exact ENNReal.coe_le_coe.mp hτ
  obtain ⟨s, hs, hd⟩ := h.trace_approach_of_radius_lt hU a z ha r hr hy (hR ▸ hlevel)
  have hstart : r ≤ dist (γ 0) z := by
    rw [h.2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  exact (spatialHitTime_lt_of_dist_lt h.1 z r hstart s hd).trans_le
    (WithTop.coe_le_coe.mpr (hs.2.trans hat))

lemma IsCapacityTwoWitness.physicalGreen_eq_before_spatial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hlevel : (2 * z.im) * Real.exp (-u) < r) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z r) :
    physicalStoppedGreen κ U γ G z u t = greenDensity κ U γ G t z := by
  apply ite_eq_right
  intro hτ
  exact (not_lt_of_ge ht) (h.radius_hit_forces_spatial_before hU z r hr hy u hlevel t hτ)

lemma IsCapacityTwoWitness.radius_no_hit_of_spatial_no_hit
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hlevel : (2 * z.im) * Real.exp (-u) < r)
    (ht : spatialHitTime γ z r = ⊤) : radiusLevelTime γ G z u = ∞ := by
  apply radiusLevelTime_eq_top_of_no_level
  rintro ⟨t, hl, hR⟩
  have hh := h.radius_hit_forces_spatial_before hU z r hr hy u hlevel t
    (le_of_eq (radiusLevelTime_eq_of_live_level hU h z u t hl hR))
  rw [ht] at hh
  exact not_top_lt hh

lemma boundedSpatialHit_coe (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    (boundedSpatialHit γ z r T : WithTop ℝ≥0) = min (spatialHitTime γ z r) T := by
  have hn : min (spatialHitTime γ z r) (T : WithTop ℝ≥0) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hn
  change (((min (spatialHitTime γ z r) (T : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = _
  rw [← hv, WithTop.untopD_coe]

lemma boundedSpatialHit_le (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    (boundedSpatialHit γ z r T : WithTop ℝ≥0) ≤ spatialHitTime γ z r := by
  rw [boundedSpatialHit_coe]
  exact min_le_left _ _

 

lemma IsCapacityTwoWitness.spatialGreen_limit
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hlevel : (2 * z.im) * Real.exp (-u) < r)
    (hno : radiusLevelTime γ G z u = ∞ →
      Tendsto (fun n : ℕ => greenDensity κ U γ G n z) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => physicalStoppedGreen κ U γ G z u
      (boundedSpatialHit γ z r n)) atTop (𝓝 (spatialGreenWeight κ U γ G z r)) := by
  by_cases ht : spatialHitTime γ z r = ⊤
  · have hn := hno (h.radius_no_hit_of_spatial_no_hit hU z r hr hy u hlevel ht)
    have he (n : ℕ) : boundedSpatialHit γ z r n = n := by
      simp only [boundedSpatialHit, ht, min_eq_right (le_top), WithTop.untopD_coe]
    simpa only [he, h.physicalGreen_eq_before_spatial hU κ z r hr hy u hlevel _
      (by rw [ht]; exact le_top), spatialGreenWeight, ite_eq_left ht] using hn
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ht
    have he : (spatialHitTime γ z r).untopD 0 = v := by rw [← hv, WithTop.untopD_coe]
    rw [spatialGreenWeight, ite_eq_right ht, he]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Nat.ceil (v : ℝ))] with n hn
    have hvn : v ≤ (n : ℝ≥0) := by
      change (v : ℝ) ≤ (n : ℝ)
      exact (Nat.le_ceil (v : ℝ)).trans (Nat.cast_le.mpr hn)
    have hbn : boundedSpatialHit γ z r n = v := by
      simp only [boundedSpatialHit, ← hv, min_eq_left (WithTop.coe_le_coe.mpr hvn), WithTop.untopD_coe]
    rw [hbn]
    exact (h.physicalGreen_eq_before_spatial hU κ z r hr hy u hlevel v hv.le).symm

end SLEExactGauge

end


section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

lemma valid_measurable (n : ℕ) :
    MeasurableSet {p : ℝ≥0 × (ℂ × Ω) | c.valid n p.1 p.2.1 p.2.2} := by
  have hz : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => p.2.1.im) :=
    Complex.measurable_im.comp (measurable_fst.comp measurable_snd)
  have hQ : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => (c.Q n p.1 p.2).1.im) :=
    Complex.measurable_im.comp ((c.measurable n).comp
      ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)).fst
  exact (measurableSet_lt measurable_const hz).inter
    ((measurableSet_le (Real.measurable_log.comp hz) measurable_const).inter
      (measurableSet_le measurable_const hQ))

lemma derivative_compact (n : ℕ) (z : ℂ) (ω : Ω) (T : ℝ≥0) (t : ℝ)
    (ht : t ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt (fun s => c.Q n s (z, ω))
      (clippedLogLoewnerField (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n])
        (U t.toNNReal ω) (c.Q n t (z, ω))) (Icc 0 (T : ℝ)) t :=
  (c.derivative n z ω t ht.1).mono Icc_subset_Ici_self

lemma live_of_valid {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (h : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (n : ℕ) (t : ℝ≥0) (z : ℂ) (hv : c.valid n t z ω) :
    z ∈ survivingDomain γ t := by
  exact (clipped_log_identification_of_endpoint hUc h t z hv.1 _ _ _
    (fun s => c.Q n s (z, ω)) (c.initial n z ω)
    (c.derivative_compact n z ω t) hv.2.2 hv.2.1).1

lemma agrees_of_live {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (h : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (n : ℕ) (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (hlo : -(n : ℝ) ≤ Real.log (G t z).im) (hhi : Real.log z.im ≤ (n : ℝ)) :
    c.Q n t (z, ω) = logLoewnerCoordinates G z t := by
  exact clipped_log_loewner_agrees hUc h t z hz _ _ _ hlo hhi
    (fun s => c.Q n s (z, ω)) (c.initial n z ω)
    (c.derivative_compact n z ω t) ⟨t.coe_nonneg, le_rfl⟩

lemma eventually_valid_agrees {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (ω : Ω) (hUc : Continuous (fun t => U t ω))
    (h : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t) :
    ∀ᶠ n : ℕ in atTop, c.valid n t z ω ∧
      c.Q n t (z, ω) = logLoewnerCoordinates G z t := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max (-Real.log (G t z).im) (Real.log z.im))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlo : -(n : ℝ) ≤ Real.log (G t z).im := by
    have ha := (le_max_left (-Real.log (G t z).im) (Real.log z.im)).trans (hN.trans hNn)
    linarith
  have hhi : Real.log z.im ≤ (n : ℝ) := (le_max_right _ _).trans (hN.trans hNn)
  have he := c.agrees_of_live ω hUc h n t z hz hlo hhi
  refine ⟨⟨hz.1.1, hhi, ?_⟩, he⟩
  rw [he, logCoordinates_im]
  exact hlo

end SpatialClippedFamily
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

lemma greenApprox_measurable (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (n : ℕ) :
    Measurable (c.greenApprox κ B n) := by
  have hQ := (c.measurable n).comp
    ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hB : Measurable (fun p : ℝ≥0 × (ℂ × Ω) => B p.1 p.2.2) :=
    hBm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  apply Measurable.ite (c.valid_measurable n) _ measurable_const
  exact (greenLogDensity_contDiff κ).continuous.measurable.comp (hQ.prodMk hB)

lemma jointGreen_measurable (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) :
    Measurable (c.jointGreen κ B) :=
  (StronglyMeasurable.limUnder (fun n => (c.greenApprox_measurable κ B hBm n).stronglyMeasurable)).measurable

lemma jointGreen_eq (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hUc : Continuous (fun t => U t ω))
    (hU : ∀ t, U t ω = Real.sqrt κ * B t ω)
    (hw : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (t : ℝ≥0) (z : ℂ) :
    c.jointGreen κ B (t, z, ω) = greenDensity κ (fun s => U s ω) γ G t z := by
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_nhds_of_eventually_eq
  by_cases hz : z ∈ survivingDomain γ t
  · filter_upwards [c.eventually_valid_agrees ω hUc hw t z hz] with n hn
    rw [greenApprox, ite_eq_left hn.1, hn.2]
    exact greenLogDensity_logCoordinates hUc hw κ (B t ω) z t hz (hU t)
  · filter_upwards [] with n
    have hn : ¬ c.valid n t z ω := fun hv => hz (c.live_of_valid ω hUc hw n t z hv)
    simp only [greenApprox, ite_eq_right hn, greenDensity, ite_eq_right hz]

end SpatialClippedFamily



end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SpatialMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial Means for chordal SLE. -/

section
section


section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma spatialGreenWeight_eq_live {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (κ : ℝ) (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) :
    spatialGreenWeight κ U γ G z r =
      if liveSpatialHitTime γ z r = ⊤ then 0 else
        greenDensity κ U γ G ((liveSpatialHitTime γ z r).untopD 0) z := by
  rw [liveSpatialHitTime_eq hc z r hs]
  by_cases hn : spatialHitTime γ z r = ⊤
  · simp only [spatialGreenWeight, ite_eq_left hn, ite_true]
  · rw [ite_eq_right hn]
    by_cases hl : z ∈ survivingDomain γ ((spatialHitTime γ z r).untopD 0)
    · simp only [ite_eq_left hl, ite_eq_right hn, spatialGreenWeight]
    · simp only [spatialGreenWeight, ite_eq_right hn,
        greenDensity, ite_eq_right hl, ite_true]

lemma spatialHitTime_measurable {Ω : Type*} [MeasurableSpace Ω]
    (γ : Ω → ℝ≥0 → ℂ) (hc : ∀ ω, Continuous (γ ω))
    (hm : ∀ t, Measurable (fun ω => γ ω t)) (r : ℝ) :
    Measurable (fun p : ℂ × Ω => spatialHitTime (γ p.2) p.1 r) := by
  let X (t : ℝ≥0) (p : ℂ × Ω) : ℝ := dist (γ p.2 t) p.1 - r
  have hXa : Adapted (⊤ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℂ × Ω))) X := by
    intro t
    exact (((hm t).comp measurable_snd).dist measurable_fst).sub_const r
  have hXc (p : ℂ × Ω) : Continuous (fun t => X t p) :=
    ((hc p.2).dist continuous_const).sub continuous_const
  have h := continuous_zero_hit_stopping ⊤ X hXa hXc 0
  exact h.measurable.mono h.measurableSpace_le le_rfl

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma jointGreen_measurable :
    Measurable (fun p : ℝ≥0 × (ℂ × a.samples) => greenDensity κ
      (fun t => Real.sqrt κ * a.B t p.2.2) (γ p.2.2) (a.G p.2.2) p.1 p.2.1) := by
  have hm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  let c := spatialClippedFamily (fun t ω => Real.sqrt κ * a.B t ω)
    (hm.const_mul _) (fun ω => (a.continuous_B ω).const_mul _)
  convert c.jointGreen_measurable κ a.B hm using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact (c.jointGreen_eq κ a.B p.2.2 ((a.continuous_B _).const_mul _)
    (fun _ => rfl) (a.witness _) p.1 p.2.1).symm

lemma spatialGreenWeight_measurable (r : ℝ) :
    Measurable (fun p : ℂ × a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t p.2) (γ p.2) (a.G p.2) p.1 r) := by
  classical
  have hm (t : ℝ≥0) : Measurable (fun ω : a.samples => γ ω t) :=
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl
  have hc (ω : a.samples) : Continuous (γ ω) := a.trace_continuous ω
  have ht : Measurable (fun p : ℂ × a.samples => spatialHitTime (γ p.2) p.1 r) :=
    spatialHitTime_measurable (fun ω : a.samples => γ ω) hc hm r
  have he : MeasurableSet {p : ℂ × a.samples | spatialHitTime (γ p.2) p.1 r = ⊤} :=
    measurableSet_eq_fun ht measurable_const
  have hg := a.jointGreen_measurable.comp ((ht.untopD 0).prodMk measurable_id)
  have hh := @Measurable.ite _ _ _ _ _ _ _ (fun _ => Classical.propDecidable _) he
    (measurable_const (a := (0 : ℝ))) hg
  simpa only [spatialGreenWeight, Function.comp_def, id_eq] using hh

end RegularSLEPresentation
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.radius_before_spatial_hit
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im) (t : ℝ≥0)
    (hz : z ∈ survivingDomain γ t) (ht : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z r) :
    r ≤ fullRadius G t z := by
  apply h.radius_ge_of_no_trace_approach hU t z hz hr hy
  intro s hs
  by_contra hn
  have hstart : r ≤ dist (γ 0) z := by
    rw [h.2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have hhit := spatialHitTime_lt_of_dist_lt h.1 z r hstart s (lt_of_not_ge hn)
  exact (not_lt_of_ge ht) (hhit.trans_le (WithTop.coe_le_coe.mpr hs.2))

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.green_before_spatial_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ r : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hr : 0 < r)
    (z : ℂ) (hy : r ≤ z.im) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z r) :
    greenDensity κ U γ G t z ≤ r ^ (-codimension κ) := by
  by_cases hz : z ∈ survivingDomain γ t
  · have hR := h.radius_before_spatial_hit hU z r hr hy t hz ht
    have hs : 0 ≤ Real.sin (Complex.arg (G t z - (U t : ℂ))) := by
      rw [Complex.sin_arg]
      have hi := (h.imag_positive t z hz).le
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact div_nonneg hi (norm_nonneg _)
    rw [greenDensity, ite_eq_left hz]
    calc
      _ ≤ r ^ (-codimension κ) * 1 := mul_le_mul
        (Real.rpow_le_rpow_of_nonpos hr hR (neg_nonpos.mpr (codimension_pos κ hκ8).le))
        (Real.rpow_le_one hs (Real.sin_le_one _) (greenExponent_pos κ hκ hκ8).le)
        (Real.rpow_nonneg hs _) (Real.rpow_nonneg hr.le _)
      _ = _ := mul_one _
  · rw [greenDensity, ite_eq_right hz]
    exact Real.rpow_nonneg hr.le _

lemma IsCapacityTwoWitness.spatialGreenWeight_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ r : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hr : 0 < r)
    (z : ℂ) (hy : r ≤ z.im) :
    0 ≤ spatialGreenWeight κ U γ G z r ∧
      spatialGreenWeight κ U γ G z r ≤ r ^ (-codimension κ) := by
  by_cases ht : spatialHitTime γ z r = ⊤
  · simp only [spatialGreenWeight, ite_eq_left ht]
    exact ⟨le_rfl, Real.rpow_nonneg hr.le _⟩
  · rw [spatialGreenWeight, ite_eq_right ht]
    refine ⟨greenDensity_nonneg h κ _ z, h.green_before_spatial_bound hU hκ hκ8 hr z hy _ ?_⟩
    exact WithTop.coe_untopD_le _ _

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma spatialRealMass_measurable (A : Set ℂ) (r : ℝ) :
    Measurable (fun ω : a.samples => spatialRealMass κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) r A) :=
  (a.spatialGreenWeight_measurable r).stronglyMeasurable.integral_prod_left'.measurable

lemma spatialGreenWeight_spatial_integrable
    (hκ : 0 < κ) (hκ8 : κ < 8) (r : ℝ) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (hheight : ∀ z ∈ A, r ≤ z.im) (ω : a.samples) :
    IntegrableOn (fun z => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) A := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  apply Integrable.of_bound
    ((a.spatialGreenWeight_measurable r).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (r ^ (-codimension κ))
  filter_upwards [ae_restrict_mem hA] with z hz
  have h := (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _) hκ hκ8 hr z (hheight z hz)
  simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

lemma spatialRealMass_bound
    (hκ : 0 < κ) (hκ8 : κ < 8) (r : ℝ) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (hheight : ∀ z ∈ A, r ≤ z.im) (ω : a.samples) :
    0 ≤ spatialRealMass κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) r A ∧
      spatialRealMass κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) r A ≤
        (volume A).toReal * r ^ (-codimension κ) := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hi := a.spatialGreenWeight_spatial_integrable hκ hκ8 r hr A hA hfin hheight ω
  have hb : ∀ᵐ z ∂(volume.restrict A), 0 ≤ spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r ∧
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r ≤ r ^ (-codimension κ) := by
    filter_upwards [ae_restrict_mem hA] with z hz
    exact (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _) hκ hκ8 hr z (hheight z hz)
  refine ⟨integral_nonneg_of_ae (hb.mono fun _ h => h.1), ?_⟩
  calc
    _ ≤ ∫ _z in A, r ^ (-codimension κ) := integral_mono_ae hi (integrable_const _) (hb.mono fun _ h => h.2)
    _ = _ := by simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, measureReal_def]

end RegularSLEPresentation
end SLEExactGauge

end

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal

open Set Filter Metric Complex
open scoped Topology NNReal

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

theorem source_killedGreen_progressive
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (z : ℂ) :
    IsStronglyProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) := by
  classical
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hnn (n : ℕ) : -(n : ℝ) ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) n]
  let c (n : ℕ) := (exists_clippedLogSolution B hm hBm hc κ (-(n : ℝ)) n (hnn n)
    (initialLogCoordinates z)).some
  let v (n : ℕ) (t : ℝ≥0) (ω : Ω) : Prop :=
    0 < z.im ∧ Real.log z.im ≤ (n : ℝ) ∧ -(n : ℝ) ≤ ((c n).Q t ω).1.im
  let A (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if v n t ω then greenLogDensity κ ((c n).Q t ω) (B t ω) else 0
  have hQp (n : ℕ) : IsStronglyProgressive f (fun t : ℝ≥0 => (c n).Q t) :=
    (show StronglyAdapted f (fun t : ℝ≥0 => (c n).Q t) from
      fun t => ((c n).adapted t).stronglyMeasurable).isStronglyProgressive_of_continuous
      (fun ω => ((c n).lipschitz ω).continuous.comp NNReal.continuous_coe)
  have hAp (n : ℕ) : IsStronglyProgressive f (A n) := by
    intro T
    have hQ := (hQp n T).measurable
    let : MeasurableSpace Ω := f T
    have hv : MeasurableSet {p : Iic T × Ω | v n p.1 p.2} :=
      (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        (measurableSet_le measurable_const (Complex.measurable_im.comp hQ.fst)))
    have hBp := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).isStronglyProgressive_of_continuous hc
    have hBm := (hBp T).measurable
    exact (Measurable.ite hv ((greenLogDensity_contDiff κ).continuous.measurable.comp
      (hQ.prodMk hBm)) measurable_const).stronglyMeasurable
  have hlim (t : ℝ≥0) (ω : Ω) : Tendsto (fun n => A n t ω) atTop
      (𝓝 (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z)) := by
    apply tendsto_nhds_of_eventually_eq
    have hU : Continuous (fun s => Real.sqrt κ * B s ω) := (hc ω).const_mul _
    have hd (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :=
      ((c n).derivative ω s hs.1).mono (show Icc (0 : ℝ) (t : ℝ) ⊆ Ici 0 from Icc_subset_Ici_self)
    by_cases hz : z ∈ survivingDomain (γ ω) t
    · obtain ⟨N, hN⟩ := exists_nat_ge (max (-Real.log (G ω t z).im) (Real.log z.im))
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hlo : -(n : ℝ) ≤ Real.log (G ω t z).im := by
        have hh := (le_max_left (-Real.log (G ω t z).im) (Real.log z.im)).trans (hN.trans hNn)
        linarith
      have hhi : Real.log z.im ≤ (n : ℝ) := (le_max_right _ _).trans (hN.trans hNn)
      have he : (c n).Q t ω = logLoewnerCoordinates (G ω) z t :=
        clipped_log_loewner_agrees hU (hw ω) t z hz _ _ _ hlo hhi
          (fun s => (c n).Q s ω) ((c n).initial ω) (hd n) ⟨t.coe_nonneg, le_rfl⟩
      have hv : v n t ω := ⟨hz.1.1, hhi, by simpa only [he, logCoordinates_im] using hlo⟩
      simp only [A, ite_eq_left hv, he]
      exact greenLogDensity_logCoordinates hU (hw ω) κ (B t ω) z t hz rfl
    · filter_upwards [] with n
      have hv : ¬ v n t ω := by
        intro hv
        exact hz (clipped_log_identification_of_endpoint hU (hw ω) t z hv.1 _ _ _
          (fun s => (c n).Q s ω) ((c n).initial ω) (hd n) hv.2.2 hv.2.1).1
      simp only [A, ite_eq_right hv, greenDensity, ite_eq_right hz]
  exact isStronglyProgressive_of_tendsto hAp
    (tendsto_pi_nhds.mpr (fun t => tendsto_pi_nhds.mpr (hlim t)))

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal

end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_OccupationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Occupation Bound for chordal SLE. -/

section
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

lemma occupation_difference {F H : ℝ → ℝ} {v A C L : ℝ}
    (hv : 0 ≤ v) (hFi : IntervalIntegrable F volume 0 v) (hHi : IntervalIntegrable H volume 0 v)
    (hbal : ∀ u ∈ Icc 0 v, F u + C * (∫ s in (0 : ℝ)..u, H s) =
      L + A * (∫ s in (0 : ℝ)..u, F s))
    {s t : ℝ} (hs : s ∈ Icc 0 v) (ht : t ∈ Icc 0 v) :
    F t + C * (∫ u in s..t, H u) = F s + A * (∫ u in s..t, F u) := by
  have sub (x : ℝ) (hx : x ∈ Icc 0 v) : uIcc 0 x ⊆ uIcc 0 v := by
    simpa only [uIcc_of_le hx.1, uIcc_of_le hv] using Icc_subset_Icc le_rfl hx.2
  rw [← intervalIntegral.integral_interval_sub_left (hHi.mono_set (sub t ht)) (hHi.mono_set (sub s hs)),
    ← intervalIntegral.integral_interval_sub_left (hFi.mono_set (sub t ht)) (hFi.mono_set (sub s hs))]
  linarith [hbal s hs, hbal t ht]

lemma high_occupation_le {F H : ℝ → ℝ} {v A C L D s t : ℝ}
    (hv : 0 ≤ v) (hA : 0 ≤ A) (hC : 0 < C)
    (hFi : IntervalIntegrable F volume 0 v) (hHi : IntervalIntegrable H volume 0 v)
    (hbal : ∀ u ∈ Icc 0 v, F u + C * (∫ x in (0 : ℝ)..u, H x) =
      L + A * (∫ x in (0 : ℝ)..u, F x))
    (hs : s ∈ Icc 0 v) (ht : t ∈ Icc 0 v) (hst : s ≤ t)
    (hn : 0 ≤ F t) (hb : ∀ x ∈ Icc s t, F x ≤ D) :
    (∫ x in s..t, H x) ≤ D * (1 + A * (t - s)) / C := by
  have sub : uIcc s t ⊆ uIcc 0 v := by
    simpa only [uIcc_of_le hst, uIcc_of_le hv] using Icc_subset_Icc hs.1 ht.2
  have hl : (∫ x in s..t, F x) ≤ (t - s) * D := by
    have h := intervalIntegral.integral_mono_on hst (hFi.mono_set sub) intervalIntegrable_const hb
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have he := occupation_difference hv hFi hHi hbal hs ht
  have hh := mul_le_mul_of_nonneg_left hl hA
  apply (le_div_iff₀ hC).mpr
  have hFs := hb s (left_mem_Icc.mpr hst)
  nlinarith

lemma point_le_occupation {H : ℝ → ℝ} {s t G Q : ℝ}
    (hst : s < t) (hi : IntervalIntegrable H volume s t)
    (hd : ∀ᵐ x ∂volume.restrict (Icc s t), G ≤ Q * H x) :
    G ≤ Q * (∫ x in s..t, H x) / (t - s) := by
  have hh := intervalIntegral.integral_mono_ae_restrict hst.le
    (intervalIntegrable_const (c := G)) (hi.const_mul Q) hd
  rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul] at hh
  exact (le_div_iff₀ (sub_pos.mpr hst)).mpr (by nlinarith)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ≥0} {ε : ℕ → ℝ}

lemma radiusMoment_zero_growth
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (hκ8 : κ < 8)
    (hz : z ∈ upperHalfPlane) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    radiusMoment P c (greenExponent κ) t ≤ Real.exp (codimension κ * (t - s)) *
      radiusMoment P c (greenExponent κ) s := by
  have hh := div_le_div_of_nonneg_right
    (integral_limitRadiusKernel_zero_growth (P := P) c hε hBm (codimension κ) s t (codimension_pos κ hκ8).le hs hst)
    (initialGreen_pos κ z hz).le
  simpa only [radiusMoment, sub_self, mul_div_assoc] using hh

lemma radiusMoment_zero_le_high
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (hκ8 : κ < 8)
    (hz : z ∈ upperHalfPlane) (b s : ℝ) (hb : greenExponent κ ≤ b + 2)
    (hh : Integrable (limitRadiusKernel c (codimension κ) (greenExponent κ - b - 2) s) P) :
    radiusMoment P c (greenExponent κ) s ≤ radiusMoment P c (b + 2) s := by
  apply div_le_div_of_nonneg_right _ (initialGreen_pos κ z hz).le
  rw [sub_self, sub_add_eq_sub_sub]
  apply integral_limitRadiusKernel_antitone_power c hε (codimension κ) (greenExponent κ - b - 2) 0 s
    (by linarith) hh
  exact limitRadiusKernel_integrable c hε hBm (codimension κ) 0 (codimension_pos κ hκ8).le le_rfl s

lemma radiusMoment_high_integrable
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ) :
    IntervalIntegrable (radiusMoment P (a v) (b + 2)) volume 0 v := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  apply radiusMoment_intervalIntegrable _ v.coe_nonneg
  simpa only [sub_add_eq_sub_sub] using
    (limit_power_balance (a v) (a v) hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb v.coe_nonneg le_rfl).1

lemma radiusMoment_high_occupation
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hηv : 2 * η ≤ (v : ℝ)) :
    (∫ s in (v : ℝ) - η..v, radiusMoment P (a v) (b + 2) s) ≤
      angularMomentBound κ b η * (1 + lyapunovA κ b * η) / lyapunovC κ b := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hFi := radiusMoment_intervalIntegrable (P := P) (a v) v.coe_nonneg
    (limitRadiusKernel_region_integrable (a v) hε hBm (codimension κ) (greenExponent κ - b)
      (codimension_pos κ hκ8).le (sub_pos.mpr hb).le v)
  have hHi := radiusMoment_high_integrable a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb (v := v)
  have hbal := radiusMoment_balance a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb (v := v)
  have hbound := radiusMoment_bound a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 hz b hb0 hb η hη hη1 (v := v)
  have hh := high_occupation_le v.coe_nonneg (lyapunovA_nonneg hκ hb0 hb) (lyapunovC_pos hκ hb0 hb)
    hFi hHi hbal (s := (v : ℝ) - η) (t := v) (D := angularMomentBound κ b η)
    (by constructor <;> linarith) ⟨v.coe_nonneg, le_rfl⟩ (by linarith)
    (radiusMoment_nonneg _ (initialGreen_pos κ z hz).le b v)
    (fun x hx => hbound x ⟨by linarith [hx.1], hx.2⟩)
  simpa only [sub_sub_cancel] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma inverseAngleBound_pos {κ b η : ℝ} (hκ : 0 < κ) (hb0 : 0 < b)
    (hb : b < greenExponent κ) (hη : 0 < η) : 0 < inverseAngleBound κ b η := by
  have hD := angularMomentBound_pos hκ hb0 hb hη
  have hA := lyapunovA_nonneg hκ hb0 hb
  have hC := lyapunovC_pos hκ hb0 hb
  dsimp only [inverseAngleBound]
  positivity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ≥0} {ε : ℕ → ℝ}

lemma radiusMoment_zero_growth_high_ae
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ) (hb2 : greenExponent κ ≤ b + 2)
    (η : ℝ) (_hη : 0 < η) (hηv : η ≤ (v : ℝ)) :
    ∀ᵐ s ∂volume.restrict (Icc ((v : ℝ) - η) v),
      radiusMoment P (a v) (greenExponent κ) v ≤
        Real.exp (codimension κ * η) * radiusMoment P (a v) (b + 2) s := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hh := (limit_power_balance (a v) (a v) hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb v.coe_nonneg le_rfl).1.prod_right_ae
  rw [restrict_Ioc_eq_restrict_Icc] at hh
  have hs : Icc ((v : ℝ) - η) v ⊆ Icc 0 v := Icc_subset_Icc (by linarith) le_rfl
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hh, ae_restrict_mem measurableSet_Icc] with s hsi hsm
  have hs0 : 0 ≤ s := (hs hsm).1
  have hg := radiusMoment_zero_growth (a v) hε hBm hκ8 hz hs0 hsm.2 (P := P)
  have hdom := radiusMoment_zero_le_high (a v) hε hBm hκ8 hz b s hb2 hsi (P := P)
  have he : Real.exp (codimension κ * ((v : ℝ) - s)) ≤ Real.exp (codimension κ * η) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [hsm.1]) (codimension_pos κ hκ8).le
  exact hg.trans ((mul_le_mul_of_nonneg_right he
    (radiusMoment_nonneg _ (initialGreen_pos κ z hz).le _ _)).trans
      (mul_le_mul_of_nonneg_left hdom (Real.exp_pos _).le))

 

theorem radiusMoment_inverseAngle_bound
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ) (hb2 : greenExponent κ ≤ b + 2)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hηv : 2 * η ≤ (v : ℝ)) :
    radiusMoment P (a v) (greenExponent κ) v ≤ inverseAngleBound κ b η := by
  have hd := radiusMoment_zero_growth_high_ae a hε hεlim hε0 hB hBm hBc hB0
    hκ hκ8 hz b hb0 hb hb2 η hη (by linarith : η ≤ (v : ℝ))
  have hi := radiusMoment_high_integrable a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb (v := v)
  have his : IntervalIntegrable (radiusMoment P (a v) (b + 2)) volume ((v : ℝ) - η) v := by
    apply hi.mono_set
    simp only [uIcc_of_le (by linarith : (v : ℝ) - η ≤ v), uIcc_of_le v.coe_nonneg]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hp := point_le_occupation (by linarith : (v : ℝ) - η < v) his hd
  have hocc := radiusMoment_high_occupation a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 hz b hb0 hb η hη hη1 hηv
  simp only [sub_sub_cancel] at hp
  exact hp.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hocc (Real.exp_pos _).le) hη.le)

end SLEExactGauge
end


section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma inverseAngleSubcritical_bounds (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < inverseAngleSubcritical κ ∧ inverseAngleSubcritical κ < greenExponent κ ∧
      greenExponent κ ≤ inverseAngleSubcritical κ + 2 := by
  have ha := greenExponent_pos κ hκ hκ8
  unfold inverseAngleSubcritical
  have hm0 : 0 < min (greenExponent κ / 2) 1 := lt_min (by positivity) (by norm_num)
  have hm := min_le_left (greenExponent κ / 2) 1
  have hm1 := min_le_right (greenExponent κ / 2) 1
  constructor
  · linarith
  constructor <;> linarith

lemma uniformInverseAngleConstant_pos (κ u₀ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (hu₀ : 0 < u₀) :
    0 < uniformInverseAngleConstant κ u₀ := by
  have hb := inverseAngleSubcritical_bounds κ hκ hκ8
  exact inverseAngleBound_pos hκ hb.1 hb.2.1 (lt_min (by positivity) (by norm_num))

 

theorem uniform_inverse_angle_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u₀ : ℝ) (hu₀ : 0 < u₀)
    (v : ℝ≥0) (hv : u₀ ≤ v) :
    Integrable (fun ω => stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z v (greenExponent κ))
      (finiteCenteredLaw P κ B γ G z v) ∧
    (∫ ω, stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z v (greenExponent κ)
      ∂finiteCenteredLaw P κ B γ G z v) ≤ uniformInverseAngleConstant κ u₀ := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε0 (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεA (n : ℕ) : ε n ≤ A₀ := div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  have hεanti : Antitone ε := by
    intro n m hnm
    exact div_le_div_of_nonneg_left hA₀.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  let a (u : ℝ≥0) (n : ℕ) : AngularLocalization B hm κ z u (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z u (ε n)
      u.coe_nonneg (hε0 n) (hεA n))
  obtain ⟨hi, he⟩ := finiteCenteredLaw_inverseAngle_moment hB hBm hBc κ hκ hκ8 γ G F hw z hz v v.coe_nonneg
    (a v) hεanti hεlim (greenExponent κ) le_rfl
  refine ⟨hi, he.trans_le ?_⟩
  have hb := inverseAngleSubcritical_bounds κ hκ hκ8
  apply radiusMoment_inverseAngle_bound a hεanti hεlim hε0 hB hBm hBc hB0 hκ hκ8 hz
    (inverseAngleSubcritical κ) hb.1 hb.2.1 hb.2.2
    (inverseAngleBuffer u₀) (lt_min (by positivity) (by norm_num)) (min_le_right _ _)
  have hη := min_le_left (u₀ / 2) 1
  dsimp only [inverseAngleBuffer]
  linarith



end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma radius_approach_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ)) :
    (P {ω | radiusLevelTime (γ ω) (G ω) z v < ∞}).toReal ≤
      uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        (Real.sin (Complex.arg z)) ^ greenExponent κ := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε0 (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεA (n : ℕ) : ε n ≤ A₀ := div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  have hεanti : Antitone ε := by
    intro n m hnm
    exact div_le_div_of_nonneg_left hA₀.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  let a (n : ℕ) : AngularLocalization B hm κ z v (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z v (ε n)
      v.coe_nonneg (hε0 n) (hεA n))
  have hbound := (uniform_inverse_angle_regular hB hBm hBc hB0 κ hκ hκ8 γ G F hw z hz
    1 (by norm_num) v hv).2
  have he := (finiteCenteredLaw_inverseAngle_moment hB hBm hBc κ hκ hκ8 γ G F hw z hz v v.coe_nonneg
    a hεanti hεlim (greenExponent κ) le_rfl).2
  rw [he, radiusMoment, sub_self,
    integral_limitRadiusKernel_zero_eq_probability a hεanti hεlim hBm hBc hz v.coe_nonneg γ G F hw] at hbound
  have hmult := (div_le_iff₀ (initialGreen_pos κ z hz)).mp hbound
  calc
    (P {ω | radiusLevelTime (γ ω) (G ω) z v < ∞}).toReal ≤
        uniformInverseAngleConstant κ 1 * initialGreen κ z /
          Real.exp (codimension κ * ((v : ℝ) - Real.log 2 - Real.log z.im)) := by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa only [mul_comm] using hmult
    _ = uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        (Real.sin (Complex.arg z)) ^ greenExponent κ := by
      rw [mul_div_assoc, initialGreen_div_zeroKernel κ v z hz, mul_assoc]

 

theorem radius_approach
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ)) :
    (P {ω | radiusLevelTime (γ ω) (G ω) z v < ∞}).toReal ≤
      uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        (Real.sin (Complex.arg z)) ^ greenExponent κ := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw, hCB] with ω hω he
    simpa only [he] using hω
  exact radius_approach_regular hC hCm hCc hC0 κ hκ hκ8 γ G F hwC z hz v hv

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem euclidean_approach_at_level
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ))
    (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (hscale : (128 * Real.pi) * r ≤ (2 * z.im) * Real.exp (-v)) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        (Real.sin (Complex.arg z)) ^ greenExponent κ := by
  apply le_trans _ (radius_approach hB κ hκ hκ8 γ G F hw z hz v hv)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hw, hB.cont] with ω hω hc
  rintro ⟨t, ht⟩
  have hU : Continuous (fun s => Real.sqrt κ * B s ω) := hc.const_mul _
  obtain ⟨s, _, hsl, hsR⟩ := hω.radius_approach_of_trace_approach hU z r hr hy t ht
  exact radiusLevelTime_finite_of_live_radius_lt hU hω z v v.coe_nonneg s hsl
    (hsR.trans_le hscale)

 

theorem euclidean_approach
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (r : ℝ) (hr : 0 < r)
    (hy : r ≤ z.im)
    (hsmall : 1 ≤ Real.log ((2 * z.im) / ((128 * Real.pi) * r))) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
        initialGreen κ z * r ^ codimension κ := by
  let u := Real.log ((2 * z.im) / ((128 * Real.pi) * r))
  have hu : 0 ≤ u := (by norm_num : (0 : ℝ) ≤ 1).trans hsmall
  have hC : 0 < 128 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hy0 : 0 < 2 * z.im := mul_pos (by norm_num) hz
  have hratio : 0 < (2 * z.im) / ((128 * Real.pi) * r) := div_pos hy0 (mul_pos hC hr)
  have he : (2 * z.im) * Real.exp (-u) = (128 * Real.pi) * r := by
    dsimp only [u]
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp [(show 0 < z.im from hz).ne']
  have hb := euclidean_approach_at_level hB κ hκ hκ8 γ G F hw z hz
    ⟨u, hu⟩ hsmall r hr hy he.ge
  have hexp : Real.exp (-codimension κ * u) =
      (128 * Real.pi) ^ codimension κ * r ^ codimension κ *
        (2 * z.im) ^ (-codimension κ) := by
    rw [Real.rpow_def_of_pos hC, Real.rpow_def_of_pos hr,
      Real.rpow_def_of_pos hy0, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [u]
    rw [Real.log_div hy0.ne' (mul_pos hC hr).ne', Real.log_mul hC.ne' hr.ne']
    ring
  change (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
    uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * u) *
      (Real.sin (Complex.arg z)) ^ greenExponent κ at hb
  rw [hexp] at hb
  simpa only [initialGreen, mul_assoc, mul_comm, mul_left_comm] using hb

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SausagePointBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sausage Point Bound for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma initialGreen_le_height (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    initialGreen κ z ≤ (2 : ℝ) ^ (-codimension κ) * z.im ^ (-codimension κ) := by
  have hs : 0 ≤ Real.sin (Complex.arg z) := by
    rw [Complex.sin_arg]; exact div_nonneg hz.le (norm_nonneg _)
  calc
    initialGreen κ z ≤ (2 * z.im) ^ (-codimension κ) * 1 :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_one hs (Real.sin_le_one _) (greenExponent_pos κ hκ hκ8).le)
        (Real.rpow_nonneg (mul_nonneg (by norm_num) hz.le) _)
    _ = (2 : ℝ) ^ (-codimension κ) * z.im ^ (-codimension κ) := by
      rw [mul_one, Real.mul_rpow (by norm_num) hz.le]

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_PhysicalKernelUtilities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Kernel Utilities for chordal SLE. -/


section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
namespace SLEExactGauge

lemma source_condExp_le_of_setIntegral_le
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hgm : StronglyMeasurable[m] g)
    (h : ∀ A : Set Ω, MeasurableSet[m] A → (∫ ω in A, f ω ∂μ) ≤ ∫ ω in A, g ω ∂μ) :
    μ[f | m] ≤ᵐ[μ] g := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le
    (Integrable.trim hm integrable_condExp stronglyMeasurable_condExp)
    (Integrable.trim hm hg hgm)
  intro A hA _
  rw [← setIntegral_trim hm stronglyMeasurable_condExp hA,
    ← setIntegral_trim hm hgm hA, setIntegral_condExp hm hf hA]
  exact h A hA

end SLEExactGauge
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal NNReal
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Geometry for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_liveHit_mem {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) (t : ℝ≥0)
    (ht : liveSpatialHitTime γ z r = t) :
    z ∈ survivingDomain γ t ∧ dist (γ t) z = r := by
  rw [liveSpatialHitTime_eq hc z r hs] at ht
  split_ifs at ht with hn hl
  · exact (WithTop.coe_ne_top ht.symm).elim
  · constructor
    · simpa only [ht, WithTop.untopD_coe] using hl
    · exact spatialHitTime_mem hc z r t ht
  · exact (WithTop.coe_ne_top ht.symm).elim

lemma source_liveHit_le (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (t : ℝ≥0)
    (hl : z ∈ survivingDomain γ t) (hd : dist (γ t) z ≤ r) :
    liveSpatialHitTime γ z r ≤ (t : WithTop ℝ≥0) := by
  unfold liveSpatialHitTime
  rw [ite_eq_left ⟨t, hl, hd⟩]
  exact WithTop.coe_le_coe.mpr (csInf_le ⟨0, fun _ _ => bot_le⟩ ⟨hl, hd⟩)

lemma source_liveHit_antitone {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) {ε r : ℝ} (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    liveSpatialHitTime γ z r ≤ liveSpatialHitTime γ z ε := by
  by_cases hn : liveSpatialHitTime γ z ε = ⊤
  · rw [hn]; exact le_top
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  have hmem := source_liveHit_mem hc z ε (her.trans hs) t ht.symm
  rw [← ht]
  exact source_liveHit_le γ z r t hmem.1 (hmem.2.le.trans her)

lemma source_window_start_le {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) :
    liveSpatialHitTime γ z r ≤ sourceSpatialWindowTime γ z r ε R := by
  by_cases hn : sourceSpatialWindowTime γ z r ε R = ⊤
  · rw [hn]; exact le_top
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  rw [← ht]
  exact (source_window_mem hc z r ε R t ht.symm).1

lemma source_before_window (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ)
    (t : ℝ≥0) (hs : liveSpatialHitTime γ z r ≤ (t : WithTop ℝ≥0))
    (ht : (t : WithTop ℝ≥0) < sourceSpatialWindowTime γ z r ε R) :
    z ∈ survivingDomain γ t ∧ ε < dist (γ t) z ∧ dist (γ t) z < R := by
  have hh : ¬ (dist (γ t) z ≤ ε ∨ R ≤ dist (γ t) z ∨ z ∉ survivingDomain γ t) := by
    intro hh
    exact not_le_of_gt ht (source_window_le_of_mem γ z r ε R t ⟨hs,hh⟩)
  push Not at hh
  exact ⟨hh.2.2,hh.1,hh.2.1⟩

lemma source_window_le_fine {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    sourceSpatialWindowTime γ z r ε R ≤ liveSpatialHitTime γ z ε := by
  by_cases hn : liveSpatialHitTime γ z ε = ⊤
  · rw [hn]; exact le_top
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  have hm := source_liveHit_mem hc z ε (her.trans hs) t ht.symm
  rw [← ht]
  exact source_window_le_of_mem γ z r ε R t
    ⟨by simpa only [← ht] using source_liveHit_antitone hc z her hs, Or.inl hm.2.le⟩

lemma source_windowH_iff {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    sourceSpatialWindowH γ z r ε R = 1 ↔
      sourceSpatialWindowTime γ z r ε R = liveSpatialHitTime γ z ε ∧
      liveSpatialHitTime γ z ε ≠ ⊤ := by
  constructor
  · intro hH
    have hh : sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
        z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopD 0) ∧
        dist (γ ((sourceSpatialWindowTime γ z r ε R).untopD 0)) z ≤ ε := by
      simpa only [sourceSpatialWindowH, ite_eq_left_iff, zero_ne_one, imp_false, not_not] using hH
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hh.1
    have hm : z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ ε := by
      simpa only [← ht, WithTop.untopD_coe] using hh.2
    have hf := source_liveHit_le γ z ε t hm.1 hm.2
    rw [ht] at hf
    have he := le_antisymm (source_window_le_fine hc z r ε R her hs) hf
    exact ⟨he, he ▸ hh.1⟩
  · rintro ⟨he,hn⟩
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
    have hm := source_liveHit_mem hc z ε (her.trans hs) t ht.symm
    simp only [sourceSpatialWindowH, he, ← ht, WithTop.coe_ne_top, ne_eq, not_false_eq_true,
      WithTop.untopD_coe, hm.1, hm.2.le, and_self, ite_true]

lemma source_windowB_before {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hrR : r < R)
    (hs : r ≤ dist (γ 0) z) (hB : sourceSpatialWindowB γ z r ε R = 1) :
    ∃ t : ℝ≥0, liveSpatialHitTime γ z r ≤ (t : WithTop ℝ≥0) ∧
      z ∈ survivingDomain γ t ∧ R ≤ dist (γ t) z ∧
      (t : WithTop ℝ≥0) < liveSpatialHitTime γ z ε := by
  have hh : sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
        z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopD 0) ∧
        R ≤ dist (γ ((sourceSpatialWindowTime γ z r ε R).untopD 0)) z := by
    simpa only [sourceSpatialWindowB, ite_eq_left_iff, zero_ne_one, imp_false, not_not] using hB
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hh.1
  have hm : z ∈ survivingDomain γ t ∧ R ≤ dist (γ t) z := by
    simpa only [← ht, WithTop.untopD_coe] using hh.2
  refine ⟨t,(source_window_mem hc z r ε R t ht.symm).1,hm.1,hm.2,?_⟩
  apply lt_of_le_of_ne (by simpa only [← ht] using source_window_le_fine hc z r ε R her hs)
  intro he
  have hf := (source_liveHit_mem hc z ε (her.trans hs) t he.symm).2
  linarith

lemma source_window_missed {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    (if liveSpatialHitTime γ z ε = ⊤ then (0 : ℝ) else 1) ≤
      sourceSpatialWindowH γ z r ε R + sourceSpatialWindowB γ z r ε R := by
  by_cases hn : liveSpatialHitTime γ z ε = ⊤
  · simp only [ite_eq_left hn]
    unfold sourceSpatialWindowH sourceSpatialWindowB
    split_ifs <;> norm_num
  rw [ite_eq_right hn]
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  have hle := source_window_le_fine hc z r ε R her hs
  have hwn : sourceSpatialWindowTime γ z r ε R ≠ ⊤ :=
    ne_top_of_le_ne_top hn hle
  obtain ⟨s,hs'⟩ := WithTop.ne_top_iff_exists.mp hwn
  have hst : s ≤ t := WithTop.coe_le_coe.mp (by simpa only [← ht,← hs'] using hle)
  have hl : z ∈ survivingDomain γ s := survivingDomain_antitone γ hst
    (source_liveHit_mem hc z ε (her.trans hs) t ht.symm).1
  have hm := (source_window_mem hc z r ε R s hs'.symm).2
  rcases hm with hd | hd | hd
  · have hH : sourceSpatialWindowH γ z r ε R = 1 := by
      simp only [sourceSpatialWindowH, ← hs', WithTop.coe_ne_top, ne_eq, not_false_eq_true,
        WithTop.untopD_coe, hl, hd, and_self, ite_true]
    rw [hH]; unfold sourceSpatialWindowB; split_ifs <;> norm_num
  · have hB : sourceSpatialWindowB γ z r ε R = 1 := by
      simp only [sourceSpatialWindowB, ← hs', WithTop.coe_ne_top, ne_eq, not_false_eq_true,
        WithTop.untopD_coe, hl, hd, and_self, ite_true]
    rw [hB]; unfold sourceSpatialWindowH; split_ifs <;> norm_num
  · exact (hd hl).elim

theorem sourceSpatialWindowGeometry_proved : SourceSpatialWindowGeometryTarget := by
  intro U γ G F hU hw κ hκ hκ8 z ε r R he her hrR hry
  have hs : r ≤ dist (γ 0) z := by
    rw [hw.2.1, dist_zero_left]
    exact hry.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  dsimp only
  have hH0 : 0 ≤ sourceSpatialWindowH γ z r ε R := by
    unfold sourceSpatialWindowH; split_ifs <;> norm_num
  have hH1 : sourceSpatialWindowH γ z r ε R ≤ 1 := by
    unfold sourceSpatialWindowH; split_ifs <;> norm_num
  have hB0 : 0 ≤ sourceSpatialWindowB γ z r ε R := by
    unfold sourceSpatialWindowB; split_ifs <;> norm_num
  have hB1 : sourceSpatialWindowB γ z r ε R ≤ 1 := by
    unfold sourceSpatialWindowB; split_ifs <;> norm_num
  refine ⟨source_window_start_le hw.1 z r ε R,
    source_before_window γ z r ε R, ?_, ?_, hH0,hH1,hB0,hB1,?_,
    source_windowB_before hw.1 z r ε R her.le hrR hs,
    source_window_missed hw.1 z r ε R her.le hs, ?_⟩
  · intro ht
    simp only [sourceSpatialWindowH, sourceSpatialWindowB, ht, ne_eq, not_true_eq_false,
      false_and, ite_false, and_self]
  · intro ht
    exact top_le_iff.mp (by simpa only [ht] using source_window_start_le hw.1 z r ε R)
  · by_cases hn : liveSpatialHitTime γ z ε = ⊤
    · rw [ite_eq_left hn]
      have hh : sourceSpatialWindowH γ z r ε R ≠ 1 := by
        intro hh
        exact ((source_windowH_iff hw.1 z r ε R her.le hs).mp hh).2 hn
      unfold sourceSpatialWindowH at hh ⊢
      split_ifs at hh ⊢ <;> norm_num at *
    · rw [ite_eq_right hn]; exact hH1
  · have hW := hw.spatialGreenWeight_bound hU hκ hκ8 he z (her.le.trans hry)
    have hR : 0 ≤ ε ^ (-codimension κ) := Real.rpow_nonneg he.le _
    by_cases hh : sourceSpatialWindowH γ z r ε R = 1
    · rw [hh,mul_one]; exact le_add_of_nonneg_right (mul_nonneg hR hB0)
    have hh0 : sourceSpatialWindowH γ z r ε R = 0 := by
      unfold sourceSpatialWindowH at hh ⊢
      split_ifs at hh ⊢ <;> norm_num at *
    rw [hh0,mul_zero,zero_add]
    by_cases hn : liveSpatialHitTime γ z ε = ⊤
    · rw [spatialGreenWeight_eq_live hw.1 κ U G z ε (her.le.trans hs), ite_eq_left hn]
      exact mul_nonneg hR hB0
    · have hm := source_window_missed hw.1 z r ε R her.le hs
      rw [ite_eq_right hn,hh0,zero_add] at hm
      have hb := le_antisymm hB1 hm
      rw [hb,mul_one]
      exact hW.2

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.SLEExactGauge.windowGeometryPathMeasurableSpace
attribute [local instance] OAI.SLEExactGauge.windowGeometryPathBorelSpace
lemma source_tracePath_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) :
    Measurable (fun ω : a.samples => (⟨γ ω,a.trace_continuous ω⟩ : C(ℝ≥0,ℂ))) := by
  apply source_path_measurable
  intro t
  exact (a.trace_adapted t).mono (a.filtration.le t) le_rfl

lemma source_joint_survival_measurable
    {X : Type*} [MeasurableSpace X] (g : X → C(ℝ≥0,ℂ)) (t : X → ℝ≥0) (z : X → ℂ)
    (hg : Measurable g) (ht : Measurable t) (hz : Measurable z) :
    MeasurableSet {x | z x ∈ survivingDomain (g x) (t x)} :=
  source_survival_open.measurableSet.preimage ((hg.prodMk ht).prodMk hz)

lemma source_collarStart_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (hD : MeasurableSet D) (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) :
    Measurable (fun p : ℂ × a.samples => sourceCollarStart D (γ p.2) p.1 r) := by
  have hhit := spatialHitTime_measurable (fun ω : a.samples => γ ω) a.trace_continuous
    (fun t => (a.trace_adapted t).mono (a.filtration.le t) le_rfl) r
  have hl := source_joint_survival_measurable
    (fun p : ℂ × a.samples => (⟨γ p.2,a.trace_continuous p.2⟩ : C(ℝ≥0,ℂ)))
    (fun p => (spatialHitTime (γ p.2) p.1 r).untopA) Prod.fst
    ((source_tracePath_measurable a).comp measurable_snd)
    (WithTop.measurable_untopA.comp hhit) measurable_fst
  have hm : Measurable (fun p : ℂ × a.samples =>
      if p.1 ∈ D then (if p.1 ∈ survivingDomain (γ p.2) (spatialHitTime (γ p.2) p.1 r).untopA
      then spatialHitTime (γ p.2) p.1 r else ⊤) else ⊤) :=
    Measurable.ite (hD.preimage measurable_fst)
    (Measurable.ite hl hhit (measurable_const (a := (⊤ : WithTop ℝ≥0))))
    (measurable_const (a := (⊤ : WithTop ℝ≥0)))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  by_cases hz : p.1 ∈ D
  · simp only [sourceCollarStart, ite_eq_left hz]
    apply source_liveTime_eq_killed (a.trace_continuous p.2)
    rw [(a.witness p.2).2.1, dist_zero_left]
    exact (hy p.1 hz).trans ((le_abs_self p.1.im).trans (Complex.abs_im_le_norm _))
  · simp only [sourceCollarStart, ite_eq_right hz]

lemma source_collarFinish_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (hD : MeasurableSet D) (r ε R : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) :
    Measurable (fun p : ℂ × a.samples => sourceCollarFinish D (γ p.2) p.1 r ε R) := by
  have hσ := source_collarStart_joint a D hD r hy
  apply measurable_of_Iic
  intro b
  by_cases hb : b = ⊤
  · subst b
    simp only [preimage, mem_Iic, le_top, ofPred_true]
    exact MeasurableSet.univ
  obtain ⟨T,hT⟩ := WithTop.ne_top_iff_exists.mp hb
  subst b
  have hp : Measurable (fun p : ℂ × a.samples =>
      (((min (sourceCollarStart D (γ p.2) p.1 r) T).untopD 0,
      (⟨γ p.2,a.trace_continuous p.2⟩ : C(ℝ≥0,ℂ))),p.1)) :=
    (((hσ.min measurable_const).untopD 0).prodMk
      ((source_tracePath_measurable a).comp measurable_snd)).prodMk measurable_fst
  have hK := (source_windowKernel_closed T ε R).measurableSet.preimage hp
  have he : (fun p : ℂ × a.samples => sourceCollarFinish D (γ p.2) p.1 r ε R) ⁻¹' Iic (T : WithTop ℝ≥0) =
      (Prod.fst ⁻¹' D) ∩ {p : ℂ × a.samples | sourceCollarStart D (γ p.2) p.1 r ≤ (T : WithTop ℝ≥0)} ∩
      {p : ℂ × a.samples | ∃ t ∈ Icc (0 : ℝ≥0) T,
      (min (sourceCollarStart D (γ p.2) p.1 r) T).untopD 0 ≤ t ∧
      (dist (γ p.2 t) p.1 ≤ ε ∨ R ≤ dist (γ p.2 t) p.1 ∨ p.1 ∉ survivingDomain (γ p.2) t)} := by
    ext p
    simp only [mem_preimage, mem_Iic, mem_inter_iff, mem_ofPred_eq]
    by_cases hz : p.1 ∈ D
    · simp only [hz, true_and, sourceCollarStart, sourceCollarFinish]
      exact source_window_kernel_iff (a.trace_continuous p.2) p.1 r ε R T
    · simp only [hz, false_and, sourceCollarFinish, iff_false]
      exact not_le_of_gt (WithTop.coe_lt_top _)
  rw [he]
  exact ((hD.preimage measurable_fst).inter (measurableSet_le hσ measurable_const)).inter hK

lemma source_spatialWeight_stopping_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (z : ℂ) (r : ℝ)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => spatialHitTime (γ ω) z r)) :
    Measurable[hτ.measurableSpace] (fun ω => spatialGreenWeight κ
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z r) := by
  have hmG := measurable_stoppedValue (source_killedGreen_progressive hm hc κ γ G F hw z) hτ
  have he : MeasurableSet[hτ.measurableSpace] {ω | spatialHitTime (γ ω) z r = ⊤} :=
    measurableSet_eq_fun hτ.measurable measurable_const
  have hmo : Measurable[hτ.measurableSpace] (fun ω =>
      if spatialHitTime (γ ω) z r = ⊤ then (0:ℝ) else
        greenDensity κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω)
          (spatialHitTime (γ ω) z r).untopA z) :=
    Measurable.ite he measurable_const hmG
  convert hmo using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  by_cases ht : spatialHitTime (γ ω) z r = ⊤
  · simp only [spatialGreenWeight, ite_eq_left ht]
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ht
    simp only [spatialGreenWeight, ite_eq_right ht]
    rw [← hv]
    rfl

lemma source_windowH_untopA (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) :
    sourceSpatialWindowH γ z r ε R =
    if sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
      z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopA) ∧
      dist (γ ((sourceSpatialWindowTime γ z r ε R).untopA)) z ≤ ε then 1 else 0 := by
  by_cases ht : sourceSpatialWindowTime γ z r ε R = ⊤
  · simp only [sourceSpatialWindowH, ht, ne_eq, not_true_eq_false, false_and, ite_false]
  · obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp ht
    unfold sourceSpatialWindowH
    rw [← ht]
    rfl

lemma source_windowB_untopA (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) :
    sourceSpatialWindowB γ z r ε R =
    if sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
      z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopA) ∧
      R ≤ dist (γ ((sourceSpatialWindowTime γ z r ε R).untopA)) z then 1 else 0 := by
  by_cases ht : sourceSpatialWindowTime γ z r ε R = ⊤
  · simp only [sourceSpatialWindowB, ht, ne_eq, not_true_eq_false, false_and, ite_false]
  · obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp ht
    unfold sourceSpatialWindowB
    rw [← ht]
    rfl

lemma source_windowHB_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r ε R : ℝ)
    (hτ : IsStoppingTime a.filtration (fun ω : a.samples => sourceSpatialWindowTime (γ ω) z r ε R)) :
    Measurable[hτ.measurableSpace] (fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R) ∧
    Measurable[hτ.measurableSpace] (fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε R) := by
  have htp := (show StronglyAdapted a.filtration (fun t (ω : a.samples) => γ ω t) from
    fun t => (a.trace_adapted t).stronglyMeasurable).isStronglyProgressive_of_continuous a.trace_continuous
  have hv := measurable_stoppedValue htp hτ
  let : MeasurableSpace a.samples := hτ.measurableSpace
  have hl := source_live_stopped_measurable a z hτ
  have hn : MeasurableSet[hτ.measurableSpace] {ω : a.samples | sourceSpatialWindowTime (γ ω) z r ε R ≠ ⊤} :=
    (measurableSet_eq_fun hτ.measurable measurable_const).compl
  have hd : Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      dist (γ ω (sourceSpatialWindowTime (γ ω) z r ε R).untopA) z) := hv.dist measurable_const
  have hH : Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      if sourceSpatialWindowTime (γ ω) z r ε R ≠ ⊤ ∧
      z ∈ survivingDomain (γ ω) (sourceSpatialWindowTime (γ ω) z r ε R).untopA ∧
      dist (γ ω (sourceSpatialWindowTime (γ ω) z r ε R).untopA) z ≤ ε then (1:ℝ) else 0) :=
    Measurable.ite (hn.inter (hl.inter (measurableSet_le hd measurable_const)))
    (measurable_const (a := (1:ℝ))) (measurable_const (a := (0:ℝ)))
  have hB : Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      if sourceSpatialWindowTime (γ ω) z r ε R ≠ ⊤ ∧
      z ∈ survivingDomain (γ ω) (sourceSpatialWindowTime (γ ω) z r ε R).untopA ∧
      R ≤ dist (γ ω (sourceSpatialWindowTime (γ ω) z r ε R).untopA) z then (1:ℝ) else 0) :=
    Measurable.ite (hn.inter (hl.inter (measurableSet_le measurable_const hd)))
    (measurable_const (a := (1:ℝ))) (measurable_const (a := (0:ℝ)))
  constructor
  · convert hH using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    exact source_windowH_untopA (γ ω) z r ε R
  · convert hB using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    exact source_windowB_untopA (γ ω) z r ε R

end
end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Bounds for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.windowBoundsPathMeasurableSpace
local instance windowBoundsPathBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma source_liveTime_eq_sphere_of_finite {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) (hn : liveSpatialHitTime γ z r ≠ ⊤) :
    liveSpatialHitTime γ z r = spatialHitTime γ z r := by
  have he := source_liveTime_eq_killed hc z r hs
  split_ifs at he with hl
  · exact he
  · exact (hn he).elim

lemma source_windowV_stopped_eq {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ) (κ : ℝ) (z : ℂ) (r ε R : ℝ)
    (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    spatialGreenWeight κ U γ G z ε * sourceSpatialWindowH γ z r ε R =
      greenDensity κ U γ G (sourceSpatialWindowTime γ z r ε R).untopA z *
        sourceSpatialWindowH γ z r ε R := by
  by_cases hH : sourceSpatialWindowH γ z r ε R = 1
  · obtain ⟨he,hn⟩ := (source_windowH_iff hc z r ε R her hs).mp hH
    have hr := source_liveTime_eq_sphere_of_finite hc z ε (her.trans hs) hn
    have hraw : spatialHitTime γ z ε ≠ ⊤ := hr ▸ hn
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hraw
    rw [hH, mul_one, mul_one, he, hr, spatialGreenWeight, ite_eq_right hraw, ← ht]
    rfl
  · have hz : sourceSpatialWindowH γ z r ε R = 0 := by
      unfold sourceSpatialWindowH at hH ⊢
      split_ifs <;> simp_all
    rw [hz,mul_zero,mul_zero]

lemma source_windowV_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r ε R : ℝ) (her : ε ≤ r) (hy : r ≤ z.im)
    (hτ : IsStoppingTime a.filtration (fun ω : a.samples => sourceSpatialWindowTime (γ ω) z r ε R)) :
    Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z ε *
        sourceSpatialWindowH (γ ω) z r ε R) := by
  have hg := measurable_stoppedValue
    (source_killedGreen_progressive a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z) hτ
  have hH := (source_windowHB_stopped_measurable a z r ε R hτ).1
  convert hg.mul hH using 1 <;> try rfl
  funext ω
  apply source_windowV_stopped_eq (a.trace_continuous ω) _ _ _ _ _ _ _ her
  rw [(a.witness ω).2.1,dist_zero_left]
  exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm _))

lemma source_liveWeight_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r : ℝ) (hy : r ≤ z.im)
    (hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r)) :
    Measurable[hσ.measurableSpace] (fun ω : a.samples =>
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) := by
  have hraw : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r) :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  have hm := source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
    (fun ω : a.samples => γ ω) a.G a.F a.witness z r hraw
  apply hm.mono (hraw.measurableSpace_mono hσ ?_) le_rfl
  intro ω
  have hs : r ≤ dist (γ ω 0) z := by
    rw [(a.witness ω).2.1,dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm _))
  change spatialHitTime (γ ω) z r ≤ liveSpatialHitTime (γ ω) z r
  rw [source_liveTime_eq_killed (a.trace_continuous ω) z r hs]
  split_ifs <;> first | exact le_rfl | exact le_top

lemma source_collarHB_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (hD : MeasurableSet D) (r ε R : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) :
    Measurable (fun p : ℂ × a.samples => sourceCollarH D (γ p.2) p.1 r ε R) ∧
    Measurable (fun p : ℂ × a.samples => sourceCollarB D (γ p.2) p.1 r ε R) := by
  let τ := fun p : ℂ × a.samples => sourceCollarFinish D (γ p.2) p.1 r ε R
  have ht : Measurable τ := source_collarFinish_joint a D hD r ε R hy
  have hg : Measurable (fun p : ℂ × a.samples => (⟨γ p.2,a.trace_continuous p.2⟩ : C(ℝ≥0,ℂ))) :=
    (source_tracePath_measurable a).comp measurable_snd
  have hl := source_joint_survival_measurable
    (fun p : ℂ × a.samples => (⟨γ p.2,a.trace_continuous p.2⟩ : C(ℝ≥0,ℂ)))
    (fun p => (τ p).untopD 0) Prod.fst hg (ht.untopD 0) measurable_fst
  have hd : Measurable (fun p : ℂ × a.samples => dist (γ p.2 ((τ p).untopD 0)) p.1) :=
    (continuous_eval.measurable.comp (hg.prodMk (ht.untopD 0))).dist measurable_fst
  have hn : MeasurableSet {p | τ p ≠ ⊤} := (measurableSet_eq_fun ht measurable_const).compl
  have hH : Measurable (fun p : ℂ × a.samples =>
      if τ p ≠ ⊤ ∧ p.1 ∈ survivingDomain (γ p.2) ((τ p).untopD 0) ∧
      dist (γ p.2 ((τ p).untopD 0)) p.1 ≤ ε then (1:ℝ) else 0) :=
    Measurable.ite (hn.inter (hl.inter (measurableSet_le hd measurable_const))) measurable_const measurable_const
  have hB : Measurable (fun p : ℂ × a.samples =>
      if τ p ≠ ⊤ ∧ p.1 ∈ survivingDomain (γ p.2) ((τ p).untopD 0) ∧
      R ≤ dist (γ p.2 ((τ p).untopD 0)) p.1 then (1:ℝ) else 0) :=
    Measurable.ite (hn.inter (hl.inter (measurableSet_le measurable_const hd))) measurable_const measurable_const
  constructor
  · convert hH using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    by_cases hz : p.1 ∈ D
    · simp only [sourceCollarH,sourceSpatialWindowH,τ,sourceCollarFinish,ite_eq_left hz]
    · simp only [sourceCollarH,τ,sourceCollarFinish,ite_eq_right hz,ne_eq,not_true_eq_false,false_and,ite_false]
  · convert hB using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    by_cases hz : p.1 ∈ D
    · simp only [sourceCollarB,sourceSpatialWindowB,τ,sourceCollarFinish,ite_eq_left hz]
    · simp only [sourceCollarB,τ,sourceCollarFinish,ite_eq_right hz,ne_eq,not_true_eq_false,false_and,ite_false]

lemma source_stop_space_congr {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ) (he : σ = τ) :
    hσ.measurableSpace = hτ.measurableSpace := by
  subst τ
  rfl

lemma source_collarHBV_stopped
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (r ε R : ℝ) (her : ε ≤ r) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) :
    let hτ := source_collarFinish_stopping a D r ε R hy z
    Measurable[hτ.measurableSpace] (fun ω : a.samples => sourceCollarH D (γ ω) z r ε R) ∧
    Measurable[hτ.measurableSpace] (fun ω : a.samples => sourceCollarB D (γ ω) z r ε R) ∧
    Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z ε *
        sourceCollarH D (γ ω) z r ε R) := by
  dsimp only
  by_cases hz : z ∈ D
  · have ht := source_window_stopping a z r ε R (hy z hz)
    have hh := source_windowHB_stopped_measurable a z r ε R ht
    have hv := source_windowV_stopped_measurable a z r ε R her (hy z hz) ht
    have hspace := source_stop_space_congr (source_collarFinish_stopping a D r ε R hy z) ht
      (funext fun ω => by simp only [sourceCollarFinish,ite_eq_left hz])
    rw [hspace]
    simpa only [sourceCollarH,sourceCollarB,ite_eq_left hz] using And.intro hh.1 (And.intro hh.2 hv)
  · simp only [sourceCollarH,sourceCollarB,ite_eq_right hz,mul_zero]
    exact ⟨measurable_const,measurable_const,measurable_const⟩

lemma source_collarWeight_stopped
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) :
    Measurable[(source_collarStart_stopping a D r hy z).measurableSpace] (fun ω : a.samples =>
      if z ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r else 0) := by
  by_cases hz : z ∈ D
  · have hs := source_liveHit_stopping a z r (hy z hz)
    have hw := source_liveWeight_stopped_measurable a z r (hy z hz) hs
    have hspace := source_stop_space_congr (source_collarStart_stopping a D r hy z) hs
      (funext fun ω => by simp only [sourceCollarStart,ite_eq_left hz])
    rw [hspace]
    simpa only [ite_eq_left hz] using hw
  · simp only [ite_eq_right hz]
    exact measurable_const

end
end SLEExactGauge

end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Tails for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
namespace SLEExactGauge
noncomputable section
universe u_source_spatial

lemma spatialHitTime_antitone_radius {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) {ε r : ℝ} (hεr : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    spatialHitTime γ z r ≤ spatialHitTime γ z ε := by
  by_cases he : spatialHitTime γ z ε = ⊤
  · rw [he]; exact le_top
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp he
  rw [← ht]
  have hd := spatialHitTime_mem hc z ε t ht.symm
  exact spatialHitTime_le_of_dist_le hc z r hs t (hd.le.trans hεr)

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable



lemma source_windowHB_range (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) :
    (sourceSpatialWindowH γ z r ε R = 0 ∨ sourceSpatialWindowH γ z r ε R = 1) ∧
    (sourceSpatialWindowB γ z r ε R = 0 ∨ sourceSpatialWindowB γ z r ε R = 1) := by
  constructor <;> (first | unfold sourceSpatialWindowH | unfold sourceSpatialWindowB) <;>
    split_ifs <;> simp

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_window_origin_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r : ℝ)
    (hy : r ≤ z.im) (ω : a.samples) : r ≤ dist (γ ω 0) z := by
  rw [(a.witness ω).2.1,dist_zero_left]
  exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))

lemma source_window_weight_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r : ℝ)
    (hy : r ≤ z.im) (ω : a.samples) (h : liveSpatialHitTime (γ ω) z r = ⊤) :
    spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r = 0 := by
  rw [spatialGreenWeight_eq_live (a.trace_continuous ω) κ _ _ z r
    (source_window_origin_bound a z r hy ω),ite_eq_left h]

end
end SLEExactGauge

end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_GreenCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Green Covariance for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma exists_uniform_radius_level (ε R : ℝ) (hε : 0 < ε) (_hR : 0 ≤ R) :
    ∃ u : ℝ, 0 ≤ u ∧ (2 * R) * Real.exp (-u) < ε := by
  have ht : Tendsto (fun u : ℝ => (2 * R) * Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (2 * R)
  obtain ⟨u, hu0, hu⟩ := (eventually_ge_atTop (0 : ℝ)).and ((tendsto_order.mp ht).2 ε hε) |>.exists
  exact ⟨u, hu0, hu⟩

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma boundedSpatialGreen_measurable (r : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℂ × a.samples => greenDensity κ
      (fun t => Real.sqrt κ * a.B t p.2) (γ p.2) (a.G p.2)
      (boundedSpatialHit (γ p.2) p.1 r T) p.1) := by
  have hγ (t : ℝ≥0) : Measurable (fun ω : a.samples => γ ω t) :=
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl
  have ht := spatialHitTime_measurable (fun ω : a.samples => γ ω)
    a.trace_continuous hγ r
  have hτ : Measurable (fun p : ℂ × a.samples => boundedSpatialHit (γ p.2) p.1 r T) :=
    (ht.min (measurable_const (a := (T : WithTop ℝ≥0)))).untopD 0
  have hh := a.jointGreen_measurable.comp (hτ.prodMk measurable_id)
  simpa only [Function.comp_def, id_eq] using hh

 

theorem spatialGreen_tendsto_and_bound_of_level [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hu : 0 ≤ u) (hlevel : (2 * z.im) * Real.exp (-u) < r) :
    ∀ᵐ ω : a.samples ∂(P.comap Subtype.val),
      Tendsto (fun n : ℕ => greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z) atTop
        (𝓝 (spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r)) ∧
      ∀ n : ℕ, ‖greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z‖ ≤
        Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  obtain ⟨M, Z, hM, hZ, hMb, hZb, hClosed, hStop, heq, hNoHit⟩ :=
    exists_physical_green_stopping_regular a.brownian hBm a.continuous_B a.zero_B
      κ hκ hκ8 (γ ∘ Subtype.val) a.G a.F (Eventually.of_forall a.witness)
      z (hr.trans_le hy) u hu
  filter_upwards [heq, hNoHit] with ω he hn
  have hident (n : ℕ) : physicalStoppedGreen κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) z u (boundedSpatialHit (γ ω) z r n) =
      greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω)
        (boundedSpatialHit (γ ω) z r n) z :=
    (a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z r hr hy u hlevel _ (boundedSpatialHit_le _ _ _ _)
  refine ⟨?_, ?_⟩
  · simpa only [hident] using (a.witness ω).spatialGreen_limit
      ((a.continuous_B ω).const_mul _) κ z r hr hy u hlevel hn
  · intro n
    dsimp only [Function.comp_apply] at he
    rw [← hident n, ← he.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (hMb _ ω).1]
    exact (hMb _ ω).2

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem spatialGreen_ae_spatial_limit [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (A : Set ℂ) (hA : MeasurableSet A)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R) :
    ∃ K : ℝ, ∀ᵐ ω : a.samples ∂(P.comap Subtype.val),
      ∀ᵐ z ∂(volume.restrict A),
      Tendsto (fun n : ℕ => greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z) atTop
        (𝓝 (spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r)) ∧
      ∀ n : ℕ, ‖greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z‖ ≤ K := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  obtain ⟨u, hu, hul⟩ := exists_uniform_radius_level r R hr (hr.trans_le hrR).le
  let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log r))
  refine ⟨K, ?_⟩
  let f (n : ℕ) (p : ℂ × a.samples) := greenDensity κ
    (fun t => Real.sqrt κ * a.B t p.2) (γ p.2) (a.G p.2)
    (boundedSpatialHit (γ p.2) p.1 r n) p.1
  let g (p : ℂ × a.samples) := spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t p.2) (γ p.2) (a.G p.2) p.1 r
  have hf (n : ℕ) : Measurable (f n) := a.boundedSpatialGreen_measurable r n
  have hg : Measurable g := a.spatialGreenWeight_measurable r
  have hm : MeasurableSet {p : ℂ × a.samples |
      Tendsto (fun n => f n p) atTop (𝓝 (g p)) ∧ ∀ n, ‖f n p‖ ≤ K} :=
    (measurableSet_tendsto_fun hf hg).inter (by
      change MeasurableSet {p : ℂ × a.samples | ∀ n : ℕ, ‖f n p‖ ≤ K}
      have he : {p : ℂ × a.samples | ∀ n : ℕ, ‖f n p‖ ≤ K} =
          ⋂ n : ℕ, {p : ℂ × a.samples | ‖f n p‖ ≤ K} := by
        ext p
        simp only [mem_iInter, mem_ofPred_eq]
      rw [he]
      exact MeasurableSet.iInter (fun n => measurableSet_le (hf n |>.norm) (measurable_const (a := K))))
  apply (Measure.ae_ae_comm (μ := volume.restrict A) (ν := μ) hm).mp
  filter_upwards [ae_restrict_mem hA] with z hz
  have hlevel : (2 * z.im) * Real.exp (-u) < r := by
    have hi : z.im ≤ R := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans (hbound z hz))
    exact (mul_le_mul_of_nonneg_right (by linarith : 2 * z.im ≤ 2 * R) (Real.exp_pos _).le).trans_lt hul
  filter_upwards [a.spatialGreen_tendsto_and_bound_of_level hκ hκ8 z r hr
    (hheight z hz) u hu hlevel] with ω hω
  refine ⟨hω.1, fun n => (hω.2 n).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left
    (by linarith [Real.log_le_log hr (hheight z hz)]) (codimension_pos κ hκ8).le

 

theorem spatial_slab_area_tendsto [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R) :
    ∀ᵐ ω : a.samples ∂(P.comap Subtype.val),
      Tendsto (fun n : ℕ => ∫ z in A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε n) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z) atTop
      (𝓝 (∫ z in A,
        spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z ε -
        spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r)) := by
  let ν := volume.restrict A
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  obtain ⟨Kε, hεlim⟩ := a.spatialGreen_ae_spatial_limit hκ hκ8 A hA ε R hε
    (hεr.trans hrR) (fun z hz => hεr.trans (hheight z hz)) hbound
  obtain ⟨Kr, hrlim⟩ := a.spatialGreen_ae_spatial_limit hκ hκ8 A hA r R
    (hε.trans_le hεr) hrR hheight hbound
  filter_upwards [hεlim, hrlim] with ω hωε hωr
  apply tendsto_integral_of_dominated_convergence (fun _ => Kε + Kr)
  · intro n
    exact (((a.boundedSpatialGreen_measurable ε n).sub
      (a.boundedSpatialGreen_measurable r n)).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hωε, hωr] with z hzε hzr
    exact (norm_sub_le _ _).trans (add_le_add (hzε.2 n) (hzr.2 n))
  · filter_upwards [hωε, hωr] with z hzε hzr
    exact hzε.1.sub hzr.1

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma spatialSlabIncrement_measurable (A : Set ℂ) (ε r : ℝ) :
    Measurable (fun ω : a.samples => spatialSlabIncrement κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) A ε r) :=
  ((a.spatialGreenWeight_measurable ε).sub (a.spatialGreenWeight_measurable r)).stronglyMeasurable.integral_prod_left'.measurable



end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma hasSubgaussianMGF_of_compensated
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (c : ℝ≥0)
    (h : ∀ θ : ℝ, (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω - θ^2 * c / 2)) ∂μ) ≤ 1) :
    HasSubgaussianMGF X c μ := by
  have hb (θ : ℝ) : (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω)) ∂μ) ≤
      ENNReal.ofReal (Real.exp (c * θ^2 / 2)) := by
    have he (ω : Ω) : Real.exp (θ * X ω) = Real.exp (c * θ^2 / 2) *
        Real.exp (θ * X ω - θ^2 * c / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [lintegral_const_mul'' _ (((hX.const_mul θ).sub_const (θ^2*c/2)).exp.ennreal_ofReal)]
    simpa only [mul_one] using mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (c * θ^2/2)))) (h θ)
  have hi (θ : ℝ) : Integrable (fun ω => Real.exp (θ * X ω)) μ := by
    refine ⟨(hX.const_mul θ).exp.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)).mpr
    exact (hb θ).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, fun θ => ?_⟩
  change (∫ ω, Real.exp (θ * X ω) ∂μ) ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => (Real.exp_pos _).le) (hi θ).1]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb θ)).trans_eq (ENNReal.toReal_ofReal (Real.exp_pos _).le)

lemma HasSubgaussianMGF.mono_parameter
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c d : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) : HasSubgaussianMGF X d μ := by
  refine ⟨h.integrable_exp_mul, fun θ => (h.mgf_le θ).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcd) (sq_nonneg θ)) (by norm_num)

 

lemma subgaussian_sum_amplitudes
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (b : ℕ → ℝ≥0) (N : ℕ)
    (h : ∀ n < N, HasSubgaussianMGF (X n) (b n ^ 2) μ) :
    HasSubgaussianMGF (fun ω => ∑ n ∈ Finset.range N, X n ω)
      ((∑ n ∈ Finset.range N, b n)^2) μ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsum := (ih (fun n hn => h n (Nat.lt_succ_of_lt hn))).add (h N (Nat.lt_succ_self N))
    simpa only [NNReal.sqrt_sq, Finset.sum_range_succ] using hsum

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma slabVariance_real_formula (κ ε r : ℝ) (A : Set ℂ) :
    slabVariance κ ε r A =
      ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (layerGreenConstant * r^2 * (volume A).toReal)) := by
  simp only [slabVariance, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (show 0 ≤ (Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4 by positivity),
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (mul_nonneg layerGreenConstant_pos.le (sq_nonneg r))]

lemma slabVariance_scale (κ q r : ℝ) (A : Set ℂ) (hq : 0 < q) (hr : 0 < r) :
    slabVariance κ (q*r) r A =
      (slabAmplitude κ q A * r ^ (1 - codimension κ)) ^ 2 := by
  rw [slabVariance_real_formula, Real.mul_rpow hq.le hr.le]
  have he : r ^ (1 - codimension κ) = r * r ^ (-codimension κ) := by
    rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
  rw [he]
  symm
  rw [mul_pow, slabAmplitude, Real.sq_sqrt]
  · ring
  · exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
      (mul_nonneg layerGreenConstant_pos.le ENNReal.toReal_nonneg)

lemma slabVariance_scale_le {κ q ε r : ℝ} (A : Set ℂ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hq : 0 < q) (hr : 0 < r) (hqr : q*r ≤ ε) :
    slabVariance κ ε r A ≤ (slabAmplitude κ q A * r ^ (1 - codimension κ)) ^ 2 := by
  rw [← slabVariance_scale κ q r A hq hr, slabVariance_real_formula, slabVariance_real_formula]
  have hL := layerGreenConstant_pos.le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply (sq_le_sq₀
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (greenExponent_pos κ hκ hκ8).le)
      (Real.rpow_nonneg ((mul_pos hq hr).trans_le hqr).le _))
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (greenExponent_pos κ hκ hκ8).le)
      (Real.rpow_nonneg (mul_pos hq hr).le _))).mpr
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.sqrt_nonneg _) (greenExponent_pos κ hκ hκ8).le)
  exact Real.rpow_le_rpow_of_nonpos (mul_pos hq hr) hqr (neg_nonpos.mpr (codimension_pos κ hκ8).le)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma spatialRealMass_sub_eq_slab
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (ε r : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (hheight : ∀ z ∈ A, r ≤ z.im) (ω : a.samples) :
    spatialRealMass κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) ε A -
      spatialRealMass κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) r A =
      spatialSlabIncrement κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) A ε r := by
  exact (integral_sub (a.spatialGreenWeight_spatial_integrable hκ hκ8 ε hε A hA hfin
    (fun z hz => hεr.trans (hheight z hz)) ω)
    (a.spatialGreenWeight_spatial_integrable hκ hκ8 r (hε.trans_le hεr) A hA hfin hheight ω)).symm

 

end RegularSLEPresentation
end SLEExactGauge
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Assembly for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma window_prod_telescope {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, f i = 1 + ∑ i ∈ s, (f i - 1) * ∏ j ∈ s.filter (· < i), f j := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | @insert a s ha ih =>
    have hn : a ∉ s := fun h => (lt_irrefl a) (ha a h)
    have hfa : (insert a s).filter (· < a) = s := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hja⟩
        · exact (lt_irrefl _ hja).elim
        · exact hj
      · intro hj; exact ⟨Or.inr hj, ha j hj⟩
    have hf (i : ι) (hi : i ∈ s) :
        (insert a s).filter (· < i) = s.filter (· < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hji⟩
        · exact (not_lt_of_ge (ha i hi).le hji).elim
        · exact ⟨hj, hji⟩
      · exact fun ⟨hj, hji⟩ => ⟨Or.inr hj, hji⟩
    rw [Finset.prod_insert hn, Finset.sum_insert hn, hfa]
    simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (fun t => (f i-1)*∏j∈t,f j) (hf i hi))]
    rw [ih]
    ring

lemma window_integrable_bounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f P :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable (Eventually.of_forall hC)

lemma window_exp_secant {K θ x : ℝ} (hK : 0 < K) (hx : |x| ≤ K) :
    Real.exp (θ*x) ≤ Real.exp ((θ*K)^2/2) + Real.sinh (θ*K)/K*x := by
  let a := (K-x)/(2*K)
  let b := (K+x)/(2*K)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr (le_abs_self x |>.trans hx)) (by positivity)
  have hb : 0 ≤ b := div_nonneg (by linarith [neg_abs_le x]) (by positivity)
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have he := convexOn_exp.2 (x := -(θ*K)) (y := θ*K) (by trivial) (by trivial) ha hb hab
  have harg : a * -(θ*K) + b*(θ*K) = θ*x := by dsimp [a,b]; field_simp; ring
  simp only [smul_eq_mul, harg] at he
  have hid : a*Real.exp (-(θ*K)) + b*Real.exp (θ*K) =
      Real.cosh (θ*K) + Real.sinh (θ*K)/K*x := by
    rw [Real.cosh_eq, Real.sinh_eq]
    dsimp [a,b]
    field_simp
    ring
  rw [hid] at he
  exact he.trans (add_le_add (Real.cosh_le_exp_half_sq _) le_rfl)

lemma window_weighted_cond_mean {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X W : Ω → ℝ} (hX : Integrable X P) (hWX : Integrable (W*X) P)
    (hW : Measurable[m] W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hmean : P[X|m] ≤ᵐ[P] 0) :
    ∫ ω, W ω*X ω ∂P ≤ 0 := by
  have he := condExp_mul_of_stronglyMeasurable_left hW.stronglyMeasurable hWX hX
  calc
    _ = ∫ ω, P[W*X|m] ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, W ω*P[X|m] ω ∂P := integral_congr_ae he
    _ ≤ 0 := integral_nonpos_of_ae (hmean.mono fun ω h =>
      mul_nonpos_of_nonneg_of_nonpos (hW0 ω) h)

lemma window_weighted_hoeffding {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X W : Ω → ℝ} {K θ : ℝ} (hK : 0 < K) (hθ : 0 ≤ θ)
    (hX : Measurable[mΩ] X) (hXb : ∀ ω, |X ω| ≤ K)
    (hmean : P[X|m] ≤ᵐ[P] 0) (hW : Measurable[m] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω * Real.exp (θ*X ω) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp ((θ*K)^2/2) := by
  let : MeasurableSpace Ω := mΩ
  obtain ⟨M,hM⟩ := hWb
  have hWa : Measurable[mΩ] W := hW.mono hm le_rfl
  have hWi : Integrable W P := window_integrable_bounded hWa
    (fun ω => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hW0 ω)] using hM ω)
  have hXi : Integrable X P := window_integrable_bounded hX (by simpa only [Real.norm_eq_abs] using hXb)
  have hWXi : Integrable (fun ω => W ω*X ω) P := window_integrable_bounded (hWa.mul hX) (fun ω => by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hW0 ω)]
    exact mul_le_mul (hM ω) (hXb ω) (norm_nonneg _) (le_trans (hW0 ω) (hM ω)))
  have hc := window_weighted_cond_mean hm hXi hWXi hW hW0 hmean
  have hL : 0 ≤ Real.sinh (θ*K)/K := div_nonneg (by rw [Real.sinh_eq]; exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hθ hK.le]))) (by norm_num)) hK.le
  have hEi : Integrable (fun ω => W ω*Real.exp (θ*X ω)) P :=
    window_integrable_bounded (hWa.mul ((hX.const_mul θ).exp)) (fun ω => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hW0 ω), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hM ω) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (le_abs_self _ |>.trans (hXb ω)) hθ)) (Real.exp_pos _).le (le_trans (hW0 ω) (hM ω)))
  calc
    _ ≤ ∫ ω, W ω * (Real.exp ((θ*K)^2/2) + Real.sinh (θ*K)/K * X ω) ∂P := by
      apply integral_mono hEi
      · have hi := (hWi.mul_const (Real.exp ((θ*K)^2/2))).add
            (hWXi.const_mul (Real.sinh (θ*K)/K))
        convert hi using 1 <;> first | rfl | (ext ω; simp only [Pi.add_apply, mul_add]; ring)
      · intro ω
        exact mul_le_mul_of_nonneg_left (window_exp_secant hK (hXb ω)) (hW0 ω)
    _ = (∫ ω, W ω ∂P)*Real.exp ((θ*K)^2/2) +
        Real.sinh (θ*K)/K*(∫ ω, W ω*X ω ∂P) := by
      simp_rw [mul_add, show ∀ ω, W ω*(Real.sinh (θ*K)/K*X ω) =
        (Real.sinh (θ*K)/K)*(W ω*X ω) from fun _ => by ring]
      rw [integral_add (hWi.mul_const _) (hWXi.const_mul _), integral_mul_const, integral_const_mul]
    _ ≤ _ := by linarith [mul_nonpos_of_nonneg_of_nonpos hL hc]

lemma window_prod_before {Ω ι : Type*} [Fintype ι] [LinearOrder ι]
    (σ : ι → Ω → WithTop ℝ≥0) (ω : Ω) (f : ι → ℝ) :
    ∏ i, f i = 1 + ∑ i, (f i - 1) * ∏ j, if windowBefore σ j i ω then f j else 1 := by
  classical
  let key (i : ι) : Lex (WithTop ℝ≥0 × ι) := toLex (σ i ω, i)
  have hinj : Function.Injective key := fun i j h => congrArg Prod.snd h
  have hh := @window_prod_telescope ι (LinearOrder.lift' key hinj) Finset.univ f
  simp only [Finset.prod_filter] at hh
  change (∏ i, f i) = 1 + ∑ i, (f i-1)*∏j, if key j < key i then f j else 1 at hh
  rw [hh]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have he : key j < key i ↔ windowBefore σ j i ω := by
    simp only [key, Prod.Lex.toLex_lt_toLex, windowBefore]
  by_cases hb : windowBefore σ j i ω
  · rw [ite_eq_left hb, ite_eq_left (he.mpr hb)]
  · rw [ite_eq_right hb, ite_eq_right (mt he.mp hb)]

lemma window_before_measurable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [LinearOrder ι]
    {ℱ : Filtration ℝ≥0 mΩ} {σ : ι → Ω → WithTop ℝ≥0}
    (hs : ∀ i, IsStoppingTime ℱ (σ i)) (i j : ι) :
    MeasurableSet[(hs i).measurableSpace] {ω | windowBefore σ j i ω} := by
  have hlt : MeasurableSet[(hs i).measurableSpace] {ω | σ j ω < σ i ω} := by
    simpa only [compl_ofPred, not_le] using ((hs i).measurableSet_le_stopping_time (hs j)).compl
  have heq : MeasurableSet[(hs i).measurableSpace] {ω | σ j ω = σ i ω} := by
    simpa only [eq_comm] using (hs i).measurableSet_eq_stopping_time (hs j)
  by_cases hij : j < i
  · convert hlt.union heq using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [windowBefore, hij, and_true, mem_ofPred_eq, mem_union]
  · simpa only [windowBefore, hij, and_false, or_false] using hlt

lemma window_measurable_on_event {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ} {σ τ : Ω → WithTop ℝ≥0}
    (hs : IsStoppingTime ℱ σ) (ht : IsStoppingTime ℱ τ)
    {f : Ω → ℝ} (hf : Measurable[ht.measurableSpace] f)
    {E : Set Ω} (hE : MeasurableSet[hs.measurableSpace] E)
    (hle : ∀ ω ∈ E, τ ω ≤ σ ω) (c : ℝ) :
    Measurable[hs.measurableSpace] (fun ω => if ω ∈ E then f ω else c) := by
  classical
  intro B hB
  have hEB : MeasurableSet[hs.measurableSpace] (f ⁻¹' B ∩ E) := by
    have hh := ht.measurableSet_inter_le hs (f ⁻¹' B) (hf hB)
    have hh' : MeasurableSet[hs.measurableSpace] (f ⁻¹' B ∩ {ω | τ ω ≤ σ ω}) :=
      ((ht.min hs).measurableSpace_mono hs (fun _ => min_le_right _ _)) _ hh
    convert hh'.inter hE using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    exact ⟨fun ⟨h1,h2⟩ => ⟨⟨h1,hle ω h2⟩,h2⟩, fun ⟨⟨h1,_⟩,h2⟩ => ⟨h1,h2⟩⟩
  by_cases hc : c ∈ B
  · convert hEB.union hE.compl using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    by_cases hw : ω ∈ E <;> simp [hw, hc]
  · convert hEB using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    by_cases hw : ω ∈ E <;> simp [hw, hc]

lemma window_integrable_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Measurable f) (h0 : ∀ ω, 0 ≤ f ω)
    {C : ℝ} (hC : ∀ ω, f ω ≤ C) : Integrable f P :=
  window_integrable_bounded hf (fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ω)] using hC ω)

lemma window_weighted_normalized {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X W : Ω → ℝ} {K θ : ℝ} (hK : 0 < K) (hθ : 0 ≤ θ)
    (hX : Measurable[mΩ] X) (hXb : ∀ ω, |X ω| ≤ K)
    (hmean : P[X|m] ≤ᵐ[P] 0) (hW : Measurable[m] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω * (Real.exp (θ*X ω - (θ*K)^2/2)-1) ∂P) ≤ 0 := by
  let : MeasurableSpace Ω := mΩ
  obtain ⟨M,hM⟩ := hWb
  have hWa : Measurable[mΩ] W := hW.mono hm le_rfl
  have hWi : Integrable W P := window_integrable_nonneg hWa hW0 hM
  have hEi : Integrable (fun ω => W ω*Real.exp (θ*X ω)) P :=
    window_integrable_nonneg (hWa.mul ((hX.const_mul θ).exp))
      (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le) (fun ω =>
      mul_le_mul (hM ω) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (le_abs_self _ |>.trans (hXb ω)) hθ)) (Real.exp_pos _).le (le_trans (hW0 ω) (hM ω)))
  have h := window_weighted_hoeffding hm hK hθ hX hXb hmean hW hW0 ⟨M,hM⟩
  simp_rw [Real.exp_sub, mul_sub, mul_one, ← mul_div_assoc]
  rw [integral_sub (hEi.div_const _) hWi, integral_div]
  exact sub_nonpos.mpr ((div_le_iff₀ (Real.exp_pos _)).mpr h)



lemma window_cond_mean_at_infinity {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {σ : Ω → WithTop ℝ≥0} (hs : IsStoppingTime ℱ σ)
    {Y μ : Ω → ℝ} (hY : Integrable Y P)
    (hmean : ∀ᵐ ω ∂P, σ ω ≠ ⊤ → P[Y|hs.measurableSpace] ω ≤ μ ω)
    (hno : ∀ ω, σ ω = ⊤ → Y ω = 0 ∧ μ ω = 0) :
    P[Y|hs.measurableSpace] ≤ᵐ[P] μ := by
  have htop : IsStoppingTime ℱ (fun _ => (⊤ : WithTop ℝ≥0)) := by
    intro t
    simp
  have hE : MeasurableSet[hs.measurableSpace] {ω | σ ω = ⊤} :=
    hs.measurableSet_eq_stopping_time htop
  have he := condExp_indicator hY hE
  have hz : ({ω | σ ω = ⊤}.indicator Y) = 0 := by
    ext ω
    by_cases h : σ ω = ⊤
    · simpa [h] using (hno ω h).1
    · simp [h]
  rw [hz, condExp_zero] at he
  filter_upwards [hmean, he] with ω hm he
  by_cases h : σ ω = ⊤
  · have hy : P[Y|hs.measurableSpace] ω = 0 := by simpa [h] using he.symm
    rw [hy, (hno ω h).2]
  · exact hm h

lemma window_capped_cond_mean {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Y μ : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K) (hY : Measurable[mΩ] Y)
    (hYb : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ K) (hμ : Measurable[m] μ)
    (hμ0 : ∀ ω, 0 ≤ μ ω) (hmean : P[Y|m] ≤ᵐ[P] μ) :
    P[(fun ω => Y ω-min (μ ω) K)|m] ≤ᵐ[P] 0 := by
  let : MeasurableSpace Ω := mΩ
  have hYi : Integrable Y P := window_integrable_nonneg hY (fun ω => (hYb ω).1) (fun ω => (hYb ω).2)
  have hν : Measurable[m] (fun ω => min (μ ω) K) := hμ.min measurable_const
  have hνi : Integrable (fun ω => min (μ ω) K) P :=
    window_integrable_nonneg (hν.mono hm le_rfl) (fun ω => le_min (hμ0 ω) hK)
      (fun ω => min_le_right _ _)
  have hbound := condExp_mono hYi (integrable_const K) (Eventually.of_forall fun ω => (hYb ω).2) (m := m)
  rw [condExp_const hm] at hbound
  have he := condExp_sub hYi hνi m
  rw [condExp_of_stronglyMeasurable hm hν.stronglyMeasurable hνi] at he
  filter_upwards [he, hbound, hmean] with ω he hb hm
  simp only [Pi.sub_apply] at he
  have he' : P[(fun ω => Y ω-min (μ ω) K)|m] ω = P[Y|m] ω-min (μ ω) K := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
  rw [he']
  exact sub_nonpos.mpr (le_min hm hb)

lemma window_geometric_order {Ω ι : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {z : ι → ℂ} (hz : ∀ i j, i ≠ j → 2*R < dist (z i) (z j)) :
    ∀ i j ω, windowBefore (fun i => σ (z i)) j i ω → τ (z j) ω ≤ σ (z i) ω := by
  intro i j ω hpre
  by_contra hn
  have hne : σ (z i) ω ≠ ⊤ := ne_top_of_lt (lt_of_not_ge hn)
  have hji : j ≠ i := by
    intro he
    subst j
    rcases hpre with hlt | ⟨_,hlt⟩ <;> exact (lt_irrefl _ hlt)
  have hle : σ (z j) ω ≤ σ (z i) ω := hpre.elim le_of_lt (fun h => h.1.le)
  have hcoe : (((σ (z i) ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = σ (z i) ω :=
    by
      cases he : σ (z i) ω with
      | top => exact (hne he).elim
      | coe t => rfl
  have hconf := h.confined (z j) ω ((σ (z i) ω).untopD 0) (hcoe.symm ▸ hle)
    (hcoe.symm ▸ lt_of_not_ge hn)
  have hcont := h.contact (z i) ω hne
  have htri := dist_triangle (z j) (γ ((σ (z i) ω).untopD 0) ω) (z i)
  rw [dist_comm (z j) (γ ((σ (z i) ω).untopD 0) ω), hcont] at htri
  have := hz j i hji
  linarith [h.radius_le]

lemma window_integral_grid_1d {f : ℝ → ℝ} (hf : Measurable f)
    {C a : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (ha : 0 ≤ a) (n : ℕ) :
    (∫ x in Ioc 0 a, ∑ i : Fin n, f (x + a*i - 2)) =
      ∫ x in Ioc (-2) (a*n-2), f x := by
  have hfi (u v : ℝ) : IntegrableOn f (Ioc u v) :=
    window_integrable_bounded hf hC
  have hi (i : Fin n) : IntegrableOn (fun x => f (x+a*i-2)) (Ioc 0 a) :=
    window_integrable_bounded (hf.comp ((measurable_id.add_const _).sub_const _))
      (fun x => hC _)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have hpiece (i : Fin n) : (∫ x in Ioc 0 a, f (x+a*i-2)) =
      ∫ x in (a*(i:ℝ)-2)..(a*((i:ℝ)+1)-2), f x := by
    rw [← intervalIntegral.integral_of_le ha]
    have he := intervalIntegral.integral_comp_add_right f (a*i-2) (a := 0) (b := a)
    simp only [zero_add] at he
    have hend : a*((i:ℝ)+1)-2 = a+(a*i-2) := by ring
    simpa only [hend, add_sub_assoc] using he
  simp_rw [hpiece]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    ∫ x in (a*(k:ℝ)-2)..(a*((k:ℝ)+1)-2), f x) n]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => a*k-2) (n := n) (f := f) (μ := volume)
    (fun k hk => (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by have : (k:ℝ) ≤ k+1 := by linarith
          exact sub_le_sub_right (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ k) ha) 2)).mpr (hfi _ _))
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, zero_sub] at hsum
  rw [hsum, intervalIntegral.integral_of_le (by nlinarith [mul_nonneg ha (Nat.cast_nonneg n)])]

lemma window_grid_2d {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {C a : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (ha : 0 ≤ a) (n : ℕ) :
    (∫ p, ∑ ij : Fin n × Fin n,
      f (p.1+a*ij.1-2,p.2+a*ij.2-2) ∂windowSquare 0 a) =
      ∫ p, f p ∂windowSquare (-2) (a*n-2) := by
  let G (x : ℝ) := ∫ y in Ioc (-2) (a*n-2), f (x,y)
  have hG : Measurable G := (hf.stronglyMeasurable.integral_prod_right (f := fun x y => f (x,y))).measurable
  have hGb (x : ℝ) : ‖G x‖ ≤ C*(volume.restrict (Ioc (-2) (a*n-2))).real univ :=
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun y => hC (x,y))
  have hrow (x : ℝ) : (∫ y in Ioc 0 a, ∑ ij : Fin n × Fin n,
      f (x+a*ij.1-2,y+a*ij.2-2)) = ∑ i : Fin n, G (x+a*i-2) := by
    simp_rw [Fintype.sum_prod_type]
    rw [integral_finsetSum]
    · congr 1
      ext i
      exact window_integral_grid_1d (hf.comp (measurable_const.prodMk measurable_id))
        (fun y => hC _) ha n
    · intro i hi
      apply window_integrable_bounded (C := n*C)
      · exact Finset.measurable_sum _ (fun j hj => hf.comp (measurable_const.prodMk
          ((measurable_id.add_const _).sub_const _)))
      · intro y
        exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j hj => hC _).trans_eq (by simp))
  dsimp only [windowSquare]
  rw [integral_prod]
  · simp_rw [hrow]
    rw [window_integral_grid_1d hG hGb ha n]
    exact (integral_prod f (window_integrable_bounded hf hC)).symm
  · apply window_integrable_bounded (C := (n*n)*C)
    · apply Finset.measurable_sum
      intro ij hij
      exact hf.comp (((measurable_fst.add_const _).sub_const _).prodMk
        ((measurable_snd.add_const _).sub_const _))
    · intro p
      exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ij hij => hC _).trans_eq (by simp))

lemma windowSquare_mass {a : ℝ} (ha : 0 ≤ a) : windowSquare 0 a univ = ENNReal.ofReal (a^2) := by
  simp [windowSquare, Measure.prod_apply, Real.volume_Ioc, sq, ← ENNReal.ofReal_mul ha]

lemma windowShiftLaw_probability {a : ℝ} (ha : 0 < a) : IsProbabilityMeasure (windowShiftLaw a) := by
  apply isProbabilityMeasure_iff.mpr
  rw [windowShiftLaw, Measure.smul_apply, windowSquare_mass ha.le]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

lemma window_rectangle_integral {f : ℂ → ℝ} (_hf : Measurable f)
    (hz : ∀ z, z ∉ ball (0:ℂ) 1 → f z = 0) :
    (∫ p, f (Complex.measurableEquivRealProd.symm p) ∂windowSquare (-2) 2) = ∫ z, f z := by
  rw [windowSquare, Measure.prod_restrict]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact (Complex.volume_preserving_equiv_real_prod.symm).integral_comp' f
  · intro p hp
    apply hz
    intro hb
    apply hp
    have hn : ‖Complex.measurableEquivRealProd.symm p‖ < 1 := by simpa using hb
    have hr := Complex.abs_re_le_norm (Complex.measurableEquivRealProd.symm p)
    have hi := Complex.abs_im_le_norm (Complex.measurableEquivRealProd.symm p)
    change |p.1| ≤ _ at hr
    change |p.2| ≤ _ at hi
    exact ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
      ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩⟩

lemma window_grid_average {f : ℂ → ℝ} (hf : Measurable f)
    {C a : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) (ha : 0 < a) {n : ℕ} (han : a*n=4)
    (hz : ∀ z, z ∉ ball (0:ℂ) 1 → f z = 0) :
    (∫ ξ, a^2 * ∑ i : Fin n × Fin n, f (windowCenter a ξ i) ∂windowShiftLaw a) = ∫ z, f z := by
  rw [windowShiftLaw, integral_smul_measure, integral_const_mul]
  have he := window_grid_2d (hf.comp Complex.measurableEquivRealProd.symm.measurable)
    (fun p => hC _) ha.le n
  rw [han] at he
  norm_num only [Function.comp_apply] at he
  dsimp only [windowCenter]
  rw [he, window_rectangle_integral hf hz]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (sq_nonneg a), smul_eq_mul]
  field_simp

lemma window_nat_spacing (a : ℝ) (ha : 0 ≤ a) {i j : ℕ} (hne : i ≠ j) :
    a ≤ |a*i-a*j| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (i:ℝ)+1 ≤ j := by exact_mod_cast h
    have hle : a*i ≤ a*j := mul_le_mul_of_nonneg_left (by exact_mod_cast h.le) ha
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    nlinarith
  · have h' : (j:ℝ)+1 ≤ i := by exact_mod_cast h
    have hle : a*j ≤ a*i := mul_le_mul_of_nonneg_left (by exact_mod_cast h.le) ha
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    nlinarith

lemma window_centers_separated {a R : ℝ} (hsep : 2*R < a) (ha : 0 ≤ a)
    {n : ℕ} (ξ : ℝ × ℝ) (i j : Fin n × Fin n) (hne : i ≠ j) :
    2*R < dist (windowCenter a ξ i) (windowCenter a ξ j) := by
  rw [dist_eq_norm]
  rcases not_and_or.mp (mt Prod.ext_iff.mpr hne) with h | h
  · apply hsep.trans_le
    apply le_trans (window_nat_spacing a ha (mt Fin.ext h))
    have he : (windowCenter a ξ i - windowCenter a ξ j).re = a*(i.1:ℝ)-a*(j.1:ℝ) := by
      dsimp [windowCenter]
      ring
    rw [← he]
    exact Complex.abs_re_le_norm _
  · apply hsep.trans_le
    apply le_trans (window_nat_spacing a ha (mt Fin.ext h))
    have he : (windowCenter a ξ i - windowCenter a ξ j).im = a*(i.2:ℝ)-a*(j.2:ℝ) := by
      dsimp [windowCenter]
      ring
    rw [← he]
    exact Complex.abs_im_le_norm _

lemma window_choose_grid {R : ℝ} (hR : 0 < R) (hsmall : 3*R ≤ 1) :
    ∃ (n : ℕ) (a : ℝ), 0 < a ∧ a*n=4 ∧ 2*R<a ∧ a≤4*R := by
  let n := Nat.ceil (1/R)
  have hl := Nat.le_ceil (1/R)
  have hu := Nat.ceil_lt_add_one (a := 1/R) (by positivity)
  have hn : 0 < (n:ℝ) := (by positivity : 0 < 1/R).trans_le hl
  have hnr : 1 ≤ R*n := by
    exact (div_le_iff₀ hR).mp hl |>.trans_eq (mul_comm _ _)
  have hnr' : R*n < 1+R := by
    have H := mul_lt_mul_of_pos_right hu hR
    rw [add_mul, div_mul_cancel₀ _ hR.ne', one_mul] at H
    simpa only [mul_comm] using H
  refine ⟨n,4/n,by positivity,div_mul_cancel₀ 4 hn.ne',?_,?_⟩
  · apply (lt_div_iff₀ hn).mpr
    nlinarith
  · apply (div_le_iff₀ hn).mpr
    nlinarith
lemma window_jensen_mgf {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    {Q : Measure Ξ} [IsProbabilityMeasure Q] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Ξ → Ω → ℝ} (hF : Measurable (Function.uncurry F))
    {B θ A : ℝ} (hFb : ∀ ξ ω, ‖F ξ ω‖ ≤ B) (hθ : 0 ≤ θ)
    {W : Ω → ℝ} (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWb : ∃ M, ∀ ω, W ω ≤ M)
    (hmgf : ∀ ξ, (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤ A) :
    (∫ ω, W ω*Real.exp (θ*∫ ξ, F ξ ω ∂Q) ∂P) ≤ A := by
  obtain ⟨M,hM⟩ := hWb
  have hFi (ω : Ω) : Integrable (fun ξ => θ*F ξ ω) Q :=
    window_integrable_bounded ((hF.comp (measurable_id.prodMk measurable_const)).const_mul θ)
      (C := θ*B) (fun ξ => by rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hθ]
                              exact mul_le_mul_of_nonneg_left (hFb ξ ω) hθ)
  have hEi (ω : Ω) : Integrable (fun ξ => Real.exp (θ*F ξ ω)) Q :=
    window_integrable_nonneg ((hF.comp (measurable_id.prodMk measurable_const)).const_mul θ).exp
      (fun ξ => (Real.exp_pos _).le) (fun ξ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hFb ξ ω)) hθ))
  have hJ (ω : Ω) : Real.exp (θ*∫ ξ, F ξ ω ∂Q) ≤ ∫ ξ, Real.exp (θ*F ξ ω) ∂Q := by
    rw [← integral_const_mul]
    exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Eventually.of_forall fun _ => mem_univ _) (hFi ω) (hEi ω)
  have hZ : Measurable (fun ω => ∫ ξ, F ξ ω ∂Q) :=
    ((hF.comp measurable_swap).stronglyMeasurable.integral_prod_right (f := fun ω ξ => F ξ ω)).measurable
  have hZb (ω : Ω) : ‖∫ ξ, F ξ ω ∂Q‖ ≤ B := by
    simpa using norm_integral_le_of_norm_le_const (μ := Q) (Eventually.of_forall fun ξ => hFb ξ ω)
  have hleft : Integrable (fun ω => W ω*Real.exp (θ*∫ ξ, F ξ ω ∂Q)) P :=
    window_integrable_nonneg (hW.mul (hZ.const_mul θ).exp)
      (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le)
      (C := M*Real.exp (θ*B)) (fun ω => mul_le_mul (hM ω)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hZb ω)) hθ))
        (Real.exp_pos _).le ((hW0 ω).trans (hM ω)))
  have hjoint : Integrable (Function.uncurry (fun ξ ω => W ω*Real.exp (θ*F ξ ω))) (Q.prod P) :=
    window_integrable_nonneg ((hW.comp measurable_snd).mul (hF.const_mul θ).exp)
      (fun p => mul_nonneg (hW0 p.2) (Real.exp_pos _).le)
      (C := M*Real.exp (θ*B)) (fun p => mul_le_mul (hM p.2)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hFb p.1 p.2)) hθ))
        (Real.exp_pos _).le ((hW0 p.2).trans (hM p.2)))
  calc
    _ ≤ ∫ ω, ∫ ξ, W ω*Real.exp (θ*F ξ ω) ∂Q ∂P := by
      apply integral_mono hleft hjoint.integral_prod_right
      intro ω
      change W ω*Real.exp (θ*∫ ξ, F ξ ω ∂Q) ≤ ∫ ξ, W ω*Real.exp (θ*F ξ ω) ∂Q
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hJ ω) (hW0 ω)
    _ = ∫ ξ, ∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P ∂Q := (integral_integral_swap hjoint).symm
    _ ≤ ∫ _ξ, A ∂Q := integral_mono hjoint.integral_prod_left (integrable_const A) hmgf
    _ = A := by simp

lemma window_source_integral_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ) :
    Measurable (fun ω => ∫ z in D, (Y z ω-μ z ω)) :=
  ((h.joint_output.sub h.joint_mean).comp measurable_swap).stronglyMeasurable.integral_prod_right
    (f := fun ω z => Y z ω-μ z ω) |>.measurable

lemma window_source_integral_bounded {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ) :
    ∃ B : ℝ, ∀ ω, ‖∫ z in D, (Y z ω-μ z ω)‖ ≤ B := by
  have hfin : volume D ≠ ∞ := (isBounded_ball.subset h.bounded_D).measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hfin
  obtain ⟨M,hM⟩ := h.mean_bounded
  refine ⟨(K+M)*(volume.restrict D).real univ, fun ω => norm_integral_le_of_norm_le_const
    (Eventually.of_forall fun z => ?_)⟩
  calc
    _ ≤ ‖Y z ω‖+‖μ z ω‖ := norm_sub_le _ _
    _ = Y z ω+μ z ω := by rw [Real.norm_eq_abs, abs_of_nonneg (h.output_bound z ω).1,
      Real.norm_eq_abs, abs_of_nonneg (h.mean_nonneg z ω)]
    _ ≤ _ := add_le_add (h.output_bound z ω).2 (hM z ω)

end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_PhysicalMeshWindowCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Mesh Window Core for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable



lemma SourceWindowCore.attach {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {D : Set ℂ} {r R K : ℝ}
    {γ : ℝ≥0 → Ω → ℂ} {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceWindowCore ℱ D r R γ σ τ) (hK : 0 ≤ K)
    (hYm : ∀ z, Measurable[(h.finish z).measurableSpace] (Y z))
    (hμm : ∀ z, Measurable[(h.start z).measurableSpace] (μ z))
    (hY : ∀ z ω, 0 ≤ Y z ω ∧ Y z ω ≤ K)
    (hμ : ∀ z ω, 0 ≤ μ z ω) (hμb : ∃ M : ℝ, ∀ z ω, μ z ω ≤ M)
    (hmean : ∀ z, ∀ᵐ ω ∂P, σ z ω ≠ ⊤ → P[Y z | (h.start z).measurableSpace] ω ≤ μ z ω)
    (hns : ∀ z ω, σ z ω = ⊤ → Y z ω = 0 ∧ μ z ω = 0)
    (hne : ∀ z ω, τ z ω = ⊤ → Y z ω = 0)
    (hYj : Measurable (fun p : ℂ × Ω => Y p.1 p.2))
    (hμj : Measurable (fun p : ℂ × Ω => μ p.1 p.2)) :
    SourceDisjointWindows P ℱ D r R K γ σ τ Y μ :=
  ⟨h.measurable_D,h.bounded_D,h.radius_pos,h.radius_le,h.radius_small,hK,
    h.continuous_trace,h.adapted_trace,h.start,h.finish,h.time_le,h.contact,h.confined,
    hYm,hμm,hY,hμ,hμb,hmean,hns,hne,
    fun z hz ω => ⟨h.outside z hz ω,hns z ω (h.outside z hz ω)⟩,hYj,hμj⟩

lemma source_mesh_window_core
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (c : ℂ) (hDc : D ⊆ ball c 1)
    (ε r R : ℝ) (hr : 0 < r) (hrR : r < R) (hR : 3*R ≤ 1)
    (hy : ∀ z ∈ D, r ≤ z.im) :
    SourceWindowCore a.filtration ((fun z : ℂ => z+c) ⁻¹' D) r R
      (fun t (ω : a.samples) => γ ω t-c)
      (fun z (ω : a.samples) => sourceCollarStart D (γ ω) (z+c) r)
      (fun z (ω : a.samples) => sourceCollarFinish D (γ ω) (z+c) r ε R) := by
  have hd (x z : ℂ) : dist (x-c) z = dist x (z+c) := by
    simp only [dist_eq_norm]; congr 1; ring
  refine ⟨hD.preimage (measurable_id.add_const c),?_,hr,hrR.le,hR,
    fun ω => (a.trace_continuous ω).sub continuous_const,
    fun t => (a.trace_adapted t).sub_const c,
    fun z => source_collarStart_stopping a D r hy (z+c),
    fun z => source_collarFinish_stopping a D r ε R hy (z+c),?_,?_,?_,?_⟩
  · intro z hz
    have hh := hDc hz
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_right,sub_zero] using hh
  · intro z ω
    by_cases hz : z+c ∈ D
    · simpa only [sourceCollarStart,sourceCollarFinish,ite_eq_left hz] using
        source_window_start_le (a.trace_continuous ω) (z+c) r ε R
    · simp only [sourceCollarStart,sourceCollarFinish,ite_eq_right hz,le_refl]
  · intro z ω hn
    have hz : z+c ∈ D := by
      by_contra hh
      exact hn (by simp only [sourceCollarStart,ite_eq_right hh])
    simp only [sourceCollarStart,ite_eq_left hz] at hn ⊢
    obtain ⟨T,hT⟩ := WithTop.ne_top_iff_exists.mp hn
    rw [← hT,WithTop.untopD_coe,hd]
    exact (source_liveHit_mem (a.trace_continuous ω) (z+c) r
      (source_window_origin_bound a (z+c) r (hy (z+c) hz) ω) T hT.symm).2
  · intro z ω t hst htt
    have hz : z+c ∈ D := by
      by_contra hh
      simp only [sourceCollarStart,ite_eq_right hh] at hst
      exact (WithTop.not_top_le_coe t) hst
    simp only [sourceCollarStart,sourceCollarFinish,ite_eq_left hz] at hst htt
    rw [hd]
    exact (source_before_window (γ ω) (z+c) r ε R t hst htt).2.2
  · intro z hz ω
    exact ite_eq_right hz

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_if_bound {p : Prop} [Decidable p] {x K : ℝ}
    (hK : 0 ≤ K) (hx : p → 0 ≤ x ∧ x ≤ K) :
    0 ≤ (if p then x else 0) ∧ (if p then x else 0) ≤ K := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using hx hp
  · simp only [ite_eq_right hp,le_refl,true_and]; exact hK

lemma source_collar_HB_bounds (D : Set ℂ) (γ : ℝ≥0 → ℂ)
    (z : ℂ) (r ε R : ℝ) :
    (0 ≤ sourceCollarH D γ z r ε R ∧ sourceCollarH D γ z r ε R ≤ 1) ∧
    (0 ≤ sourceCollarB D γ z r ε R ∧ sourceCollarB D γ z r ε R ≤ 1) := by
  constructor
  · apply source_if_bound zero_le_one
    intro _; rcases (source_windowHB_range γ z r ε R).1 with h|h <;> simp [h]
  · apply source_if_bound zero_le_one
    intro _; rcases (source_windowHB_range γ z r ε R).2 with h|h <;> simp [h]

lemma source_collar_end_zero (D : Set ℂ) (γ : ℝ≥0 → ℂ)
    (z : ℂ) (r ε R : ℝ)
    (ht : sourceCollarFinish D γ z r ε R = ⊤) :
    sourceCollarH D γ z r ε R = 0 ∧ sourceCollarB D γ z r ε R = 0 := by
  by_cases hz : z ∈ D
  · simp only [sourceCollarFinish,ite_eq_left hz] at ht
    simp only [sourceCollarH,sourceCollarB,ite_eq_left hz,sourceSpatialWindowH,sourceSpatialWindowB,
      ht,ne_eq,not_true_eq_false,false_and,ite_false,and_self]
  · simp only [sourceCollarH,sourceCollarB,ite_eq_right hz,and_self]

lemma source_collar_start_zero (D : Set ℂ) {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ)
    (ht : sourceCollarStart D γ z r = ⊤) :
    sourceCollarH D γ z r ε R = 0 ∧ sourceCollarB D γ z r ε R = 0 := by
  apply source_collar_end_zero
  by_cases hz : z ∈ D
  · simp only [sourceCollarStart,ite_eq_left hz] at ht
    simp only [sourceCollarFinish,ite_eq_left hz]
    exact top_le_iff.mp (by simpa only [ht] using source_window_start_le hc z r ε R)
  · exact ite_eq_right hz

lemma source_collar_weight_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (D : Set ℂ) (r : ℝ) (hr : 0 < r)
    (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) (ω : a.samples) :
    0 ≤ (if z ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z r else 0) ∧
    (if z ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z r else 0) ≤ r^(-codimension κ) := by
  apply source_if_bound (Real.rpow_nonneg hr.le _)
  exact fun hz => (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _)
    hκ hκ8 hr z (hy z hz)

lemma source_collar_weight_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) (ω : a.samples)
    (hn : sourceCollarStart D (γ ω) z r = ⊤) :
    (if z ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z r else 0) = 0 := by
  by_cases hz : z ∈ D
  · simp only [sourceCollarStart,ite_eq_left hz] at hn
    rw [ite_eq_left hz]
    exact source_window_weight_zero a z r (hy z hz) ω hn
  · exact ite_eq_right hz

lemma source_collar_weight_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (r : ℝ) :
    Measurable (fun p : ℂ × a.samples =>
      if p.1 ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t p.2)
        (γ p.2) (a.G p.2) p.1 r else 0) :=
  Measurable.ite (hD.preimage measurable_fst) (a.spatialGreenWeight_measurable r) measurable_const

lemma source_collar_mean_transfer
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im)
    (f g : ℂ → a.samples → ℝ)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[f z | (source_liveHit_stopping a z r (hy z hz)).measurableSpace]
        ≤ᵐ[P.comap Subtype.val] g z) (z : ℂ) :
    (P.comap Subtype.val)[(fun ω => if z ∈ D then f z ω else 0) |
      (source_collarStart_stopping a D r hy z).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω => if z ∈ D then g z ω else 0) := by
  by_cases hz : z ∈ D
  · simp only [ite_eq_left hz]
    have hs := source_stop_space_congr (source_collarStart_stopping a D r hy z)
      (source_liveHit_stopping a z r (hy z hz))
      (funext fun ω => by simp only [sourceCollarStart,ite_eq_left hz])
    rw [hs]
    exact hmean z hz
  · simp only [ite_eq_right hz]
    change (P.comap Subtype.val)[(0 : a.samples → ℝ) |
      (source_collarStart_stopping a D r hy z).measurableSpace] ≤ᵐ[P.comap Subtype.val] 0
    rw [condExp_zero]

lemma source_window_scaled_bound {p q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    r^p * (q*r)^(-p) = q^(-p) := by
  rw [Real.mul_rpow hq.le hr.le]
  calc
    r^p * (q^(-p)*r^(-p)) = q^(-p)*(r^p*r^(-p)) := by ring
    _ = q^(-p) := by rw [← Real.rpow_add hr,add_neg_cancel,Real.rpow_zero,mul_one]

lemma source_collar_V_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (D : Set ℂ) (q r R : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) (ω : a.samples) :
    0 ≤ r^codimension κ * spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z (q*r) * sourceCollarH D (γ ω) z r (q*r) R ∧
    r^codimension κ * spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
      (γ ω) (a.G ω) z (q*r) * sourceCollarH D (γ ω) z r (q*r) R ≤ q^(-codimension κ) := by
  by_cases hz : z ∈ D
  · have hw := (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _)
      hκ hκ8 (mul_pos hq hr) z ((show q*r ≤ r by nlinarith).trans (hy z hz))
    have hH := (source_collar_HB_bounds D (γ ω) z r (q*r) R).1
    have hnon := mul_nonneg (Real.rpow_nonneg hr.le (codimension κ)) hw.1
    refine ⟨mul_nonneg hnon hH.1,?_⟩
    calc
      _ ≤ r^codimension κ * (q*r)^(-codimension κ) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw.2 (Real.rpow_nonneg hr.le _)) hH.2 hH.1
          (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg (mul_pos hq hr).le _))
      _ = _ := by rw [mul_one,source_window_scaled_bound hq hr]
  · simp only [sourceCollarH,ite_eq_right hz,mul_zero,le_refl,true_and]
    exact Real.rpow_nonneg hq.le _

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_H_window
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L C : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hR : 3*(L*r) ≤ 1) (hC : 0 ≤ C)
    (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[(fun ω : a.samples => sourceSpatialWindowH (γ ω) z r (q*r) (L*r)) |
        (source_liveHit_stopping a z r (hy z hz)).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω : a.samples => C*(q*r)^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r)) :
    SourceDisjointWindows (P.comap Subtype.val) a.filtration
      ((fun z : ℂ => z+c₀) ⁻¹' D) r (L*r) 1
      (fun t (ω : a.samples) => γ ω t-c₀)
      (fun z (ω : a.samples) => sourceCollarStart D (γ ω) (z+c₀) r)
      (fun z (ω : a.samples) => sourceCollarFinish D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => sourceCollarH D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => C*(q*r)^codimension κ*
        (if z+c₀ ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
          (γ ω) (a.G ω) (z+c₀) r else 0)) := by
  let core := source_mesh_window_core a D hD c₀ hDc (q*r) r (L*r) hr (by nlinarith) hR hy
  have hs : q*r ≤ r := by nlinarith
  have hfac : 0 ≤ C*(q*r)^codimension κ := mul_nonneg hC (Real.rpow_nonneg (mul_pos hq hr).le _)
  apply core.attach zero_le_one
  · intro z
    exact (source_collarHBV_stopped a D r (q*r) (L*r) hs hy (z+c₀)).1
  · intro z
    exact (source_collarWeight_stopped a D r hy (z+c₀)).const_mul _
  · intro z ω
    exact (source_collar_HB_bounds D (γ ω) (z+c₀) r (q*r) (L*r)).1
  · intro z ω
    exact mul_nonneg hfac (source_collar_weight_bounds a hκ hκ8 D r hr hy (z+c₀) ω).1
  · refine ⟨C*(q*r)^codimension κ*r^(-codimension κ),?_⟩
    intro z ω
    exact mul_le_mul_of_nonneg_left (source_collar_weight_bounds a hκ hκ8 D r hr hy (z+c₀) ω).2 hfac
  · intro z
    have hh := source_collar_mean_transfer a D r hy
      (fun z (ω : a.samples) => sourceSpatialWindowH (γ ω) z r (q*r) (L*r))
      (fun z (ω : a.samples) => C*(q*r)^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r) hmean (z+c₀)
    have hg : (fun ω : a.samples => if z+c₀ ∈ D then C*(q*r)^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (z+c₀) r else 0) =
        (fun ω : a.samples => C*(q*r)^codimension κ*(if z+c₀ ∈ D then spatialGreenWeight κ
          (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (z+c₀) r else 0)) := by
      funext ω; rw [mul_ite,mul_zero]
    rw [hg] at hh
    exact hh.mono (fun _ h _ => h)
  · intro z ω hn
    exact ⟨(source_collar_start_zero D (a.trace_continuous ω) (z+c₀) r (q*r) (L*r) hn).1,
      by rw [source_collar_weight_zero a D r hy (z+c₀) ω hn,mul_zero]⟩
  · intro z ω hn
    exact (source_collar_end_zero D (γ ω) (z+c₀) r (q*r) (L*r) hn).1
  · exact (source_collarHB_joint a D hD r (q*r) (L*r) hy).1.comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)
  · exact ((source_collar_weight_joint a D hD r).const_mul (C*(q*r)^codimension κ)).comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_collar_V_mean
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (q r L : ℝ) (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[(fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*
        sourceSpatialWindowH (γ ω) z r (q*r) (L*r)) |
        (source_liveHit_stopping a z r (hy z hz)).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r)) (z : ℂ) :
    (P.comap Subtype.val)[(fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceCollarH D (γ ω) z r (q*r) (L*r)) |
      (source_collarStart_stopping a D r hy z).measurableSpace] ≤ᵐ[P.comap Subtype.val]
    (fun ω : a.samples => r^codimension κ*(if z ∈ D then spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r else 0)) := by
  have hh := source_collar_mean_transfer a D r hy
    (fun z (ω : a.samples) => r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceSpatialWindowH (γ ω) z r (q*r) (L*r))
    (fun z (ω : a.samples) => r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r) hmean z
  have hf : (fun ω : a.samples => if z ∈ D then r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceSpatialWindowH (γ ω) z r (q*r) (L*r) else 0) =
      (fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceCollarH D (γ ω) z r (q*r) (L*r)) := by
    funext ω; simp only [sourceCollarH,mul_ite,mul_zero]
  have hg : (fun ω : a.samples => if z ∈ D then r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r else 0) =
      (fun ω : a.samples => r^codimension κ*(if z ∈ D then spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r else 0)) := by
    funext ω; rw [mul_ite,mul_zero]
  rw [hf,hg] at hh
  exact hh.mono (fun _ h => h)

lemma source_collar_V_joint
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (q r L : ℝ)
    (hy : ∀ z ∈ D, r ≤ z.im) :
    Measurable (fun p : ℂ × a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t p.2) (γ p.2) (a.G p.2) (p.1+c₀) (q*r)*
        sourceCollarH D (γ p.2) (p.1+c₀) r (q*r) (L*r)) := by
  have hj := (((a.spatialGreenWeight_measurable (q*r)).const_mul (r^codimension κ)).mul
      (source_collarHB_joint a D hD r (q*r) (L*r) hy).1)
  have ht : Measurable (fun p : ℂ × a.samples => (p.1+c₀,p.2)) :=
    (measurable_fst.add_const c₀).prodMk measurable_snd
  have hh := hj.comp ht
  dsimp only [Function.comp_def] at hh
  exact hh

lemma source_mesh_V_window
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hR : 3*(L*r) ≤ 1)
    (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[(fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*
        sourceSpatialWindowH (γ ω) z r (q*r) (L*r)) |
        (source_liveHit_stopping a z r (hy z hz)).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω : a.samples => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r)) :
    SourceDisjointWindows (P.comap Subtype.val) a.filtration
      ((fun z : ℂ => z+c₀) ⁻¹' D) r (L*r) (q^(-codimension κ))
      (fun t (ω : a.samples) => γ ω t-c₀)
      (fun z (ω : a.samples) => sourceCollarStart D (γ ω) (z+c₀) r)
      (fun z (ω : a.samples) => sourceCollarFinish D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (z+c₀) (q*r)*
        sourceCollarH D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => r^codimension κ*
        (if z+c₀ ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω)
          (γ ω) (a.G ω) (z+c₀) r else 0)) := by
  let core := source_mesh_window_core a D hD c₀ hDc (q*r) r (L*r) hr (by nlinarith) hR hy
  have hs : q*r ≤ r := by nlinarith
  have hfac : 0 ≤ r^codimension κ := Real.rpow_nonneg hr.le _
  apply core.attach (Real.rpow_nonneg hq.le _)
  · intro z
    simpa only [mul_assoc] using (source_collarHBV_stopped a D r (q*r) (L*r) hs hy (z+c₀)).2.2.const_mul (r^codimension κ)
  · intro z
    exact (source_collarWeight_stopped a D r hy (z+c₀)).const_mul _
  · intro z ω
    exact source_collar_V_bounds a hκ hκ8 D q r (L*r) hq hq1 hr hy (z+c₀) ω
  · intro z ω
    exact mul_nonneg hfac (source_collar_weight_bounds a hκ hκ8 D r hr hy (z+c₀) ω).1
  · refine ⟨r^codimension κ*r^(-codimension κ),?_⟩
    intro z ω
    exact mul_le_mul_of_nonneg_left (source_collar_weight_bounds a hκ hκ8 D r hr hy (z+c₀) ω).2 hfac
  · intro z
    exact (source_collar_V_mean a D q r L hy hmean (z+c₀)).mono (fun _ h _ => h)
  · intro z ω hn
    refine ⟨?_,?_⟩
    · rw [(source_collar_start_zero D (a.trace_continuous ω) (z+c₀) r (q*r) (L*r) hn).1,mul_zero]
    · rw [source_collar_weight_zero a D r hy (z+c₀) ω hn,mul_zero]
  · intro z ω hn
    rw [(source_collar_end_zero D (γ ω) (z+c₀) r (q*r) (L*r) hn).1,mul_zero]
  · exact source_collar_V_joint a D hD c₀ q r L hy
  · exact ((source_collar_weight_joint a D hD r).const_mul (r^codimension κ)).comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_B_window
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L Cbad c : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hR : 3*(L*r) ≤ 1) (hCb : 0 ≤ Cbad)
    (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      (P.comap Subtype.val)[(fun ω : a.samples => sourceSpatialWindowB (γ ω) z r (q*r) (L*r)) |
        (source_liveHit_stopping a z r (hy z hz)).measurableSpace] ≤ᵐ[P.comap Subtype.val]
      (fun ω : a.samples => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1))) :
    SourceDisjointWindows (P.comap Subtype.val) a.filtration
      ((fun z : ℂ => z+c₀) ⁻¹' D) r (L*r) 1
      (fun t (ω : a.samples) => γ ω t-c₀)
      (fun z (ω : a.samples) => sourceCollarStart D (γ ω) (z+c₀) r)
      (fun z (ω : a.samples) => sourceCollarFinish D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => sourceCollarB D (γ ω) (z+c₀) r (q*r) (L*r))
      (fun z (ω : a.samples) => Cbad*L^(-c)*
        (if sourceCollarStart D (γ ω) (z+c₀) r = ⊤ then 0 else 1)) := by
  let core := source_mesh_window_core a D hD c₀ hDc (q*r) r (L*r) hr (by nlinarith) hR hy
  have hs : q*r ≤ r := by nlinarith
  have hfac : 0 ≤ Cbad*L^(-c) := mul_nonneg hCb (Real.rpow_nonneg (by linarith) _)
  apply core.attach zero_le_one
  · intro z
    exact (source_collarHBV_stopped a D r (q*r) (L*r) hs hy (z+c₀)).2.1
  · intro z
    exact (Measurable.ite (measurableSet_eq_fun
      (source_collarStart_stopping a D r hy (z+c₀)).measurable measurable_const)
      measurable_const measurable_const).const_mul _
  · intro z ω
    exact (source_collar_HB_bounds D (γ ω) (z+c₀) r (q*r) (L*r)).2
  · intro z ω
    exact mul_nonneg hfac (by split_ifs <;> norm_num)
  · refine ⟨Cbad*L^(-c),?_⟩
    intro z ω
    exact (mul_le_mul_of_nonneg_left (show (if sourceCollarStart D (γ ω) (z+c₀) r = ⊤ then (0:ℝ) else 1) ≤ 1 by split_ifs <;> norm_num) hfac).trans_eq (mul_one _)
  · intro z
    have hh := source_collar_mean_transfer a D r hy
      (fun z (ω : a.samples) => sourceSpatialWindowB (γ ω) z r (q*r) (L*r))
      (fun z (ω : a.samples) => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1)) hmean (z+c₀)
    have hg : (fun ω : a.samples => if z+c₀ ∈ D then Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) (z+c₀) r = ⊤ then 0 else 1) else 0) =
        (fun ω : a.samples => Cbad*L^(-c)*(if sourceCollarStart D (γ ω) (z+c₀) r = ⊤ then 0 else 1)) := by
      funext ω; by_cases hz : z+c₀ ∈ D <;> simp [sourceCollarStart,hz]
    rw [hg] at hh
    exact hh.mono (fun _ h _ => h)
  · intro z ω hn
    exact ⟨(source_collar_start_zero D (a.trace_continuous ω) (z+c₀) r (q*r) (L*r) hn).2,
      by rw [ite_eq_left hn,mul_zero]⟩
  · intro z ω hn
    exact (source_collar_end_zero D (γ ω) (z+c₀) r (q*r) (L*r) hn).2
  · exact (source_collarHB_joint a D hD r (q*r) (L*r) hy).2.comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)
  · exact ((Measurable.ite (measurableSet_eq_fun
      (source_collarStart_joint a D hD r hy) measurable_const)
      measurable_const measurable_const).const_mul (Cbad*L^(-c))).comp
      ((measurable_fst.add_const c₀).prodMk measurable_snd)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma window_finite_mgf_at_starts {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {σ τ : ι → Ω → WithTop ℝ≥0}
    (hs : ∀ i, IsStoppingTime ℱ (σ i)) (ht : ∀ i, IsStoppingTime ℱ (τ i))
    (horder : ∀ i j ω, windowBefore σ j i ω → τ j ω ≤ σ i ω)
    {X : ι → Ω → ℝ} {K θ : ℝ} (hK : 0 < K) (hθ : 0 ≤ θ)
    (hX : ∀ i, Measurable[(ht i).measurableSpace] (X i))
    (hXb : ∀ i ω, |X i ω| ≤ K)
    (hmean : ∀ i, P[X i|(hs i).measurableSpace] ≤ᵐ[P] 0)
    {W : Ω → ℝ} (hWa : Measurable[mΩ] W) (hWstart : ∀ i, Measurable[(hs i).measurableSpace] W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω * Real.exp (θ*∑ i, X i ω) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (Fintype.card ι * (θ*K)^2/2) := by
  classical
  let q := (θ*K)^2/2
  let g (i : ι) (ω : Ω) := Real.exp (θ*X i ω-q)
  let pre (i : ι) (ω : Ω) := ∏ j, if windowBefore σ j i ω then g j ω else 1
  have hg (i : ι) : Measurable[(ht i).measurableSpace] (g i) :=
    (((hX i).const_mul θ).sub_const q).exp
  have hga (i : ι) : Measurable[mΩ] (g i) := (hg i).mono (ht i).measurableSpace_le le_rfl
  have hg0 (i : ι) (ω : Ω) : 0 ≤ g i ω := (Real.exp_pos _).le
  have hgB (i : ι) (ω : Ω) : g i ω ≤ Real.exp (θ*K) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hXb i ω)) hθ
    dsimp [q]
    nlinarith [sq_nonneg (θ*K)]
  have hp (i : ι) : Measurable[(hs i).measurableSpace] (pre i) := by
    apply Finset.measurable_prod
    intro j hj
    exact window_measurable_on_event (hs i) (ht j) (hg j)
      (window_before_measurable hs i j) (fun ω hω => horder i j ω hω) 1
  have hp0 (i : ι) (ω : Ω) : 0 ≤ pre i ω := by
    apply Finset.prod_nonneg
    intro j hj
    split_ifs <;> positivity
  have hpB (i : ι) (ω : Ω) : pre i ω ≤ Real.exp (θ*K)^Fintype.card ι := by
    calc
      _ ≤ ∏ _j : ι, Real.exp (θ*K) := by
        apply Finset.prod_le_prod
        · intro j hj; split_ifs <;> positivity
        · intro j hj; split_ifs
          · exact hgB j ω
          · exact Real.one_le_exp (mul_nonneg hθ hK.le)
      _ = _ := by simp
  obtain ⟨M,hM⟩ := hWb
  have hWi : Integrable W P := window_integrable_nonneg hWa hW0 hM
  have hHi (i : ι) : Integrable (fun ω => W ω*pre i ω*(g i ω-1)) P := by
    apply window_integrable_bounded (C := (M*Real.exp (θ*K)^Fintype.card ι)*(Real.exp (θ*K)+1)) (((hWa.mul ((hp i).mono (hs i).measurableSpace_le le_rfl))).mul
      ((hga i).sub_const 1))
    intro ω
    change ‖W ω*pre i ω*(g i ω-1)‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hW0 ω),
      Real.norm_eq_abs, abs_of_nonneg (hp0 i ω)]
    apply mul_le_mul
    · exact mul_le_mul (hM ω) (hpB i ω) (hp0 i ω) ((hW0 ω).trans (hM ω))
    · calc
        _ ≤ ‖g i ω‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
        _ = g i ω + 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 i ω), norm_one]
        _ ≤ _ := add_le_add (hgB i ω) le_rfl
    · exact norm_nonneg _
    · exact mul_nonneg ((hW0 ω).trans (hM ω)) (by positivity)
  have hHi0 (i : ι) : (∫ ω, W ω*pre i ω*(g i ω-1) ∂P) ≤ 0 := by
    exact window_weighted_normalized (hs i).measurableSpace_le hK hθ
      ((hX i).mono (ht i).measurableSpace_le le_rfl) (hXb i) (hmean i)
      ((hWstart i).mul (hp i)) (fun ω => mul_nonneg (hW0 ω) (hp0 i ω))
      ⟨M*Real.exp (θ*K)^Fintype.card ι, fun ω =>
        mul_le_mul (hM ω) (hpB i ω) (hp0 i ω) ((hW0 ω).trans (hM ω))⟩
  have hnorm : (∫ ω, W ω * ∏ i, g i ω ∂P) ≤ ∫ ω, W ω ∂P := by
    have hid (ω : Ω) := window_prod_before σ ω (fun i => g i ω)
    simp_rw [hid, mul_add, mul_one, Finset.mul_sum]
    change (∫ ω, W ω + ∑ i, W ω*((g i ω-1)*pre i ω) ∂P) ≤ _
    simp_rw [show ∀ i ω, W ω*((g i ω-1)*pre i ω) = W ω*pre i ω*(g i ω-1)
      from fun _ _ => by ring]
    rw [integral_add hWi (integrable_finsetSum _ (fun i hi => hHi i)), integral_finsetSum]
    · exact add_le_of_nonpos_right (Finset.sum_nonpos fun i hi => hHi0 i)
    · exact fun i hi => hHi i
  have hprod (ω : Ω) : (∏ i, g i ω) =
      Real.exp (θ*∑ i, X i ω) / Real.exp (Fintype.card ι * q) := by
    change (∏ i, Real.exp (θ*X i ω-q)) = _
    rw [← Real.exp_sum]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    exact Real.exp_sub _ _
  simp only [hprod, ← mul_div_assoc] at hnorm
  rw [integral_div] at hnorm
  simpa only [q, mul_div_assoc] using (div_le_iff₀ (Real.exp_pos _)).mp hnorm

 

lemma window_source_finite_mgf_at_starts {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [LinearOrder ι] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {z : ι → ℂ} (hz : ∀ i j, i ≠ j → 2*R < dist (z i) (z j))
    {θ : ℝ} (hθ : 0 ≤ θ) {W : Ω → ℝ} (hWa : Measurable[mΩ] W) (hWs : ∀ i, Measurable[(h.start (z i)).measurableSpace] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) (hK : 0 < K) :
    (∫ ω, W ω * Real.exp (θ*∑ i, (Y (z i) ω-μ (z i) ω)) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (Fintype.card ι * (θ*K)^2/2) := by
  let X (i : ι) (ω : Ω) := Y (z i) ω-min (μ (z i) ω) K
  have hYa (i : ι) : Measurable[mΩ] (Y (z i)) :=
    (h.output_measurable (z i)).mono (h.finish (z i)).measurableSpace_le le_rfl
  have hμa (i : ι) : Measurable[mΩ] (μ (z i)) :=
    (h.mean_measurable (z i)).mono (h.start (z i)).measurableSpace_le le_rfl
  have hX (i : ι) : Measurable[(h.finish (z i)).measurableSpace] (X i) :=
    (h.output_measurable (z i)).sub (((h.mean_measurable (z i)).mono
      ((h.start (z i)).measurableSpace_mono (h.finish (z i)) (h.time_le (z i))) le_rfl).min measurable_const)
  have hXb (i : ι) (ω : Ω) : |X i ω| ≤ K := by
    rw [abs_le]
    have := h.output_bound (z i) ω
    have := le_min (h.mean_nonneg (z i) ω) hK.le
    have := min_le_right (μ (z i) ω) K
    dsimp [X]
    constructor <;> linarith
  have hm (i : ι) : P[X i|(h.start (z i)).measurableSpace] ≤ᵐ[P] 0 :=
    window_capped_cond_mean (h.start (z i)).measurableSpace_le hK.le (hYa i)
      (h.output_bound (z i)) (h.mean_measurable (z i)) (h.mean_nonneg (z i))
      (window_cond_mean_at_infinity (h.start (z i))
        (window_integrable_nonneg (hYa i) (fun ω => (h.output_bound (z i) ω).1)
          (fun ω => (h.output_bound (z i) ω).2)) (h.upper_mean (z i)) (h.no_start (z i)))
  have ht := window_finite_mgf_at_starts (fun i => h.start (z i)) (fun i => h.finish (z i))
    (window_geometric_order h hz) hK hθ hX hXb hm hWa hWs hW0 hWb
  apply le_trans _ ht
  obtain ⟨M,hM⟩ := hWb
  obtain ⟨L,hL⟩ := h.mean_bounded
  have hib (f : ι → Ω → ℝ) (hf : ∀ i, Measurable[mΩ] (f i))
      (hb : ∀ i ω, f i ω ≤ K) : Integrable (fun ω => W ω*Real.exp (θ*∑ i, f i ω)) P :=
    window_integrable_nonneg (C := M*Real.exp (θ*(Fintype.card ι*K))) (hWa.mul ((Finset.measurable_sum _ (fun i _ => hf i)).const_mul θ).exp)
      (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le)
      (fun ω => mul_le_mul (hM ω) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum fun i hi => hb i ω).trans_eq (by simp)) hθ))
        (Real.exp_pos _).le ((hW0 ω).trans (hM ω)))
  apply integral_mono
  · exact hib (fun i ω => Y (z i) ω-μ (z i) ω) (fun i => (hYa i).sub (hμa i))
      (fun i ω => sub_le_self _ (h.mean_nonneg (z i) ω) |>.trans (h.output_bound (z i) ω).2)
  · exact hib X (fun i => (hX i).mono (h.finish (z i)).measurableSpace_le le_rfl)
      (fun i ω => le_abs_self _ |>.trans (hXb i ω))
  · intro ω
    apply mul_le_mul_of_nonneg_left _ (hW0 ω)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hθ
    exact Finset.sum_le_sum fun i hi => sub_le_sub_left (min_le_left _ _) _

lemma window_source_mgf_pos_at_starts {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    {θ : ℝ} (hθ : 0 ≤ θ) {W : Ω → ℝ} (hWa : Measurable[mΩ] W) (hWs : ∀ z, Measurable[(h.start z).measurableSpace] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) (hK : 0 < K) :
    (∫ ω, W ω * Real.exp (θ*∫ z in D, (Y z ω-μ z ω)) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (128*K^2*θ^2*R^2) := by
  obtain ⟨n,a,ha,han,hsep,haR⟩ := window_choose_grid (h.radius_pos.trans_le h.radius_le) h.radius_small
  let : LinearOrder (Fin n × Fin n) := LinearOrder.lift' toLex toLex.injective
  let F (ξ : ℝ × ℝ) (ω : Ω) := a^2 * ∑ i : Fin n × Fin n,
    (Y (windowCenter a ξ i) ω - μ (windowCenter a ξ i) ω)
  have hcenter (i : Fin n × Fin n) : Measurable (fun ξ => windowCenter a ξ i) :=
    Complex.measurableEquivRealProd.symm.measurable.comp
      (((measurable_fst.add_const _).sub_const _).prodMk ((measurable_snd.add_const _).sub_const _))
  have hmeas : Measurable (Function.uncurry F) := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (h.joint_output.sub h.joint_mean).comp
      (((hcenter i).comp measurable_fst).prodMk measurable_snd)
  obtain ⟨L,hL⟩ := h.mean_bounded
  have hnorm (z : ℂ) (ω : Ω) : ‖Y z ω-μ z ω‖ ≤ K+L := by
    calc
      _ ≤ ‖Y z ω‖+‖μ z ω‖ := norm_sub_le _ _
      _ = Y z ω+μ z ω := by rw [Real.norm_eq_abs, abs_of_nonneg (h.output_bound z ω).1,
        Real.norm_eq_abs, abs_of_nonneg (h.mean_nonneg z ω)]
      _ ≤ _ := add_le_add (h.output_bound z ω).2 (hL z ω)
  have hFb (ξ : ℝ × ℝ) (ω : Ω) : ‖F ξ ω‖ ≤ a^2*((n:ℝ)^2*(K+L)) := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i hi => hnorm _ ω).trans_eq (by simp [sq]; ring))
  have havg (ω : Ω) : (∫ ξ, F ξ ω ∂windowShiftLaw a) = ∫ z in D, (Y z ω-μ z ω) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      obtain ⟨_,hy,hμ⟩ := h.outside z hz ω
      simp only [hy,hμ,sub_self])]
    exact window_grid_average ((h.joint_output.sub h.joint_mean).comp
      (measurable_id.prodMk measurable_const)) (fun z => hnorm z ω) ha han
      (fun z hz => by
        obtain ⟨_,hy,hμ⟩ := h.outside z (fun hzD => hz (h.bounded_D hzD)) ω
        change Y z ω-μ z ω=0
        simp only [hy,hμ,sub_self])
  let : IsProbabilityMeasure (windowShiftLaw a) := windowShiftLaw_probability ha
  have hfinite (ξ : ℝ × ℝ) :
      (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤
      (∫ ω, W ω ∂P) * Real.exp (128*K^2*θ^2*R^2) := by
    have ht := window_source_finite_mgf_at_starts h (window_centers_separated (n := n) hsep ha.le ξ)
      (mul_nonneg hθ (sq_nonneg a)) hWa (fun i => hWs _) hW0 hWb hK
    have he : (Fintype.card (Fin n × Fin n) : ℝ)*((θ*a^2)*K)^2/2 ≤ 128*K^2*θ^2*R^2 := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      have hs : a^2 ≤ 16*R^2 := by nlinarith [h.radius_pos.trans_le h.radius_le]
      calc
        _ = (a*n)^2*a^2*θ^2*K^2/2 := by ring
        _ = 8*a^2*θ^2*K^2 := by rw [han]; ring
        _ ≤ 8*(16*R^2)*θ^2*K^2 := by gcongr
        _ = _ := by ring
    have ht' : (∫ ω, W ω*Real.exp (θ*F ξ ω) ∂P) ≤
        (∫ ω, W ω ∂P) * Real.exp ((Fintype.card (Fin n × Fin n) : ℝ)*((θ*a^2)*K)^2/2) := by
      simpa only [F, mul_assoc] using ht
    exact ht'.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (integral_nonneg hW0))
  have ht := window_jensen_mgf (Q := windowShiftLaw a) hmeas hFb hθ hWa hW0 hWb hfinite
  simpa only [havg] using ht

lemma window_source_weighted_tail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ}
    (h : SourceDisjointWindows P ℱ D r R K γ σ τ Y μ)
    (hK : 0 < K) {b : ℝ} (hb : 0 < b)
    {W : Ω → ℝ} (hWa : Measurable[mΩ] W)
    (hWs : ∀ z, Measurable[(h.start z).measurableSpace] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω*(if b < ∫ z in D, (Y z ω-μ z ω) then (1:ℝ) else 0) ∂P) ≤
      (∫ ω, W ω ∂P)*Real.exp (-(1/512:ℝ)*b^2/(K^2*R^2)) := by
  classical
  let X (ω : Ω) := ∫ z in D, (Y z ω-μ z ω)
  let θ := b/(256*K^2*R^2)
  have hR : 0 < R := h.radius_pos.trans_le h.radius_le
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hXm : Measurable X := window_source_integral_measurable h
  obtain ⟨M,hM⟩ := hWb
  obtain ⟨B,hB⟩ := window_source_integral_bounded h
  have hEi : Integrable (fun ω => W ω*Real.exp (θ*X ω)) P :=
    window_integrable_nonneg (hWa.mul (hXm.const_mul θ).exp)
      (fun ω => mul_nonneg (hW0 ω) (Real.exp_pos _).le)
      (fun ω => mul_le_mul (hM ω) (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans (hB ω)) hθ))
        (Real.exp_pos _).le ((hW0 ω).trans (hM ω)))
  have hIi : Integrable (fun ω => W ω*(if b<X ω then (1:ℝ) else 0)) P :=
    window_integrable_nonneg (hWa.mul (Measurable.ite (measurableSet_lt measurable_const hXm)
      measurable_const measurable_const))
      (fun ω => mul_nonneg (hW0 ω) (by split_ifs <;> norm_num))
      (fun ω => by split_ifs <;> simp only [mul_one,mul_zero]; exact hM ω; exact (hW0 ω).trans (hM ω))
  have hpoint (ω : Ω) : W ω*(if b<X ω then (1:ℝ) else 0) ≤
      Real.exp (-θ*b)*(W ω*Real.exp (θ*X ω)) := by
    rw [mul_left_comm,← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (hW0 ω)
    by_cases hh : b<X ω
    · rw [ite_eq_left hh]
      apply Real.one_le_exp
      nlinarith [mul_nonneg hθ (sub_nonneg.mpr hh.le)]
    · rw [ite_eq_right hh]
      exact (Real.exp_pos _).le
  have hmgf := window_source_mgf_pos_at_starts h hθ hWa hWs hW0 ⟨M,hM⟩ hK
  calc
    _ ≤ ∫ ω, Real.exp (-θ*b)*(W ω*Real.exp (θ*X ω)) ∂P :=
      integral_mono hIi (hEi.const_mul _) hpoint
    _ = Real.exp (-θ*b)*(∫ ω, W ω*Real.exp (θ*X ω) ∂P) := integral_const_mul _ _
    _ ≤ Real.exp (-θ*b)*((∫ ω, W ω ∂P)*Real.exp (128*K^2*θ^2*R^2)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      dsimp [θ]
      field_simp
      ring

end
end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_PhysicalMeshPast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Mesh Past for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_shift_integral (c : ℂ) (D : Set ℂ) (f : ℂ → ℝ) :
    (∫ z in ((fun z : ℂ => z+c) ⁻¹' D), f (z+c)) = ∫ z in D, f z := by
  exact (measurePreserving_add_right volume c).setIntegral_preimage_emb
    (MeasurableEquiv.addRight c).measurableEmbedding f D

lemma source_mesh_shifted_weighted_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ} (c : ℂ)
    (h : SourceDisjointWindows P ℱ ((fun z : ℂ => z+c) ⁻¹' D) r R K γ
      (fun z => σ (z+c)) (fun z => τ (z+c)) (fun z => Y (z+c)) (fun z => μ (z+c)))
    (hs : ∀ z, IsStoppingTime ℱ (σ z))
    (hK : 0 < K) {b : ℝ} (hb : 0 < b)
    {W : Ω → ℝ} (hWa : Measurable[mΩ] W)
    (hWs : ∀ z, Measurable[(hs z).measurableSpace] W)
    (hW0 : ∀ ω, 0 ≤ W ω) (hWb : ∃ M, ∀ ω, W ω ≤ M) :
    (∫ ω, W ω*(if b < ∫ z in D, (Y z ω-μ z ω) then (1:ℝ) else 0) ∂P) ≤
      (∫ ω, W ω ∂P)*Real.exp (-(1/512:ℝ)*b^2/(K^2*R^2)) := by
  have hh := window_source_weighted_tail h hK hb hWa (fun z => hWs (z+c)) hW0 hWb
  have he (ω : Ω) : (∫ z in ((fun z : ℂ => z+c) ⁻¹' D), (Y (z+c) ω-μ (z+c) ω)) =
      ∫ z in D, (Y z ω-μ z ω) := source_mesh_shift_integral c D (fun z => Y z ω-μ z ω)
  simpa only [he] using hh

lemma source_mesh_center_before
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (c : ℂ) (hD : D ⊆ ball c 1) (η r : ℝ)
    (hη : 0 < η) (hr : r < η/2) (hc : 1+η ≤ c.im)
    (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) (ω : a.samples) :
    spatialHitTime (γ ω) c (1+η/2) ≤ sourceCollarStart D (γ ω) z r := by
  by_cases hz : z ∈ D
  · simp only [sourceCollarStart,ite_eq_left hz]
    by_cases hn : liveSpatialHitTime (γ ω) z r = ⊤
    · rw [hn]; exact le_top
    obtain ⟨T,hT⟩ := WithTop.ne_top_iff_exists.mp hn
    have hcontact := (source_liveHit_mem (a.trace_continuous ω) z r
      (source_window_origin_bound a z r (hy z hz) ω) T hT.symm).2
    have hd : dist (γ ω T) c < 1+η/2 := by
      have hz' := hD hz
      change dist z c < 1 at hz'
      have ht := dist_triangle (γ ω T) z c
      linarith
    have hstart : 1+η/2 ≤ dist (γ ω 0) c := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have hi : c.im ≤ ‖c‖ := (le_abs_self _).trans (Complex.abs_im_le_norm c)
      linarith
    rw [← hT]
    exact (spatialHitTime_lt_of_dist_lt (a.trace_continuous ω) c _ hstart T hd).le
  · rw [sourceCollarStart,ite_eq_right hz]
    exact le_top

lemma source_mesh_center_stopping
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (c : ℂ) (η : ℝ) :
    IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) c (1+η/2)) := by
  let X (t : ℝ≥0) (ω : a.samples) := dist (γ ω t) c - (1+η/2)
  have ha : Adapted a.filtration X := by
    intro t
    let : MeasurableSpace a.samples := a.filtration t
    exact ((a.trace_adapted t).dist measurable_const).sub_const _
  exact continuous_zero_hit_stopping a.filtration X ha
    (fun ω => ((a.trace_continuous ω).dist continuous_const).sub continuous_const) 0

lemma source_mesh_free_im {γ : ℝ≥0 → ℂ} {s : ℝ≥0} {c : ℂ} {η : ℝ}
    (hη : 0 < η) (hfree : closedBall c (1+η) ⊆ survivingDomain γ s) :
    1+η < c.im := by
  let z := c-((1+η:ℝ):ℂ)*Complex.I
  have hz : z ∈ closedBall c (1+η) := by
    rw [mem_closedBall,dist_eq_norm]
    simp only [z,sub_sub_cancel_left,norm_neg,norm_mul,Complex.norm_real,Complex.norm_I,mul_one]
    rw [Real.norm_eq_abs,abs_of_pos (by linarith)]
  have hi := (hfree hz).1.1
  change 0 < z.im at hi
  simpa [z] using hi

lemma source_mesh_free_before_center {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (s : ℝ≥0) (c : ℂ) (η : ℝ) (hη : 0 < η)
    (hfree : closedBall c (1+η) ⊆ survivingDomain γ s) :
    (s : WithTop ℝ≥0) ≤ spatialHitTime γ c (1+η/2) := by
  by_contra! hn
  obtain ⟨t,ht,hcontact⟩ := (spatialHitTime_le_iff hγ c (1+η/2) s).mp hn.le
  have hin : γ t ∈ closedBall c (1+η) := by
    rw [mem_closedBall,hcontact]; linarith
  exact (hfree hin).1.2 (mem_image_of_mem γ ht)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_integrated_step
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (W W' I I' H V B : X → ℝ) (p q r C A b : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hp : 0 < p)
    (_hW : Integrable W ν) (hW' : Integrable W' ν)
    (_hI : Integrable I ν) (hI' : Integrable I' ν)
    (hH : Integrable H ν) (hV : Integrable V ν) (hB : Integrable B ν)
    (hb : 0 ≤ b)
    (hmissI : ∀ᵐ z ∂ν, I' z ≤ H z+B z)
    (hmissW : ∀ᵐ z ∂ν, W' z ≤ r^(-p)*V z+(q*r)^(-p)*B z)
    (hmeanH : (∫ z, H z ∂ν) ≤ C*(q*r)^p*(∫ z, W z ∂ν)+b)
    (hmeanV : (∫ z, V z ∂ν) ≤ r^p*(∫ z, W z ∂ν)+b)
    (hmeanB : (∫ z, B z ∂ν) ≤ A*(∫ z, I z ∂ν)+b) :
    (∫ z, W' z ∂ν) ≤ (∫ z, W z ∂ν)+(A*q^(-p))*(r^(-p)*(∫ z, I z ∂ν))+
       (2*q^(-p))*r^(-p)*b ∧
    (q*r)^(-p)*(∫ z, I' z ∂ν) ≤ C*(∫ z, W z ∂ν)+
       (A*q^(-p))*(r^(-p)*(∫ z, I z ∂ν))+(2*q^(-p))*r^(-p)*b := by
  have hrp : 0 ≤ r^(-p) := (Real.rpow_pos_of_pos hr _).le
  have hqp : 0 ≤ (q*r)^(-p) := (Real.rpow_pos_of_pos (mul_pos hq hr) _).le
  have hq1p : 1 ≤ q^(-p) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq hq1.le (neg_nonpos.mpr hp.le)
  have hcancel : r^(-p)*r^p = 1 := by rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  have hcancelq : (q*r)^(-p)*(q*r)^p = 1 := by rw [←Real.rpow_add (mul_pos hq hr),neg_add_cancel,Real.rpow_zero]
  have hmul : (q*r)^(-p) = q^(-p)*r^(-p) := Real.mul_rpow hq.le hr.le
  constructor
  · calc
      _ ≤ ∫ z, (r^(-p)*V z+(q*r)^(-p)*B z) ∂ν :=
        integral_mono_ae hW' ((hV.const_mul _).add (hB.const_mul _)) hmissW
      _ = r^(-p)*(∫ z, V z ∂ν)+(q*r)^(-p)*(∫ z, B z ∂ν) := by
        rw [integral_add (hV.const_mul _) (hB.const_mul _),integral_const_mul,integral_const_mul]
      _ ≤ r^(-p)*(r^p*(∫ z, W z ∂ν)+b)+(q*r)^(-p)*(A*(∫ z,I z ∂ν)+b) :=
        add_le_add (mul_le_mul_of_nonneg_left hmeanV hrp) (mul_le_mul_of_nonneg_left hmeanB hqp)
      _ ≤ _ := by rw [mul_add,←mul_assoc,hcancel,one_mul,hmul]; nlinarith [mul_nonneg (sub_nonneg.mpr hq1p) (mul_nonneg hrp hb)]
  · calc
      _ ≤ (q*r)^(-p)*(∫ z, (H z+B z) ∂ν) := mul_le_mul_of_nonneg_left
        (integral_mono_ae hI' (hH.add hB) hmissI) hqp
      _ = (q*r)^(-p)*((∫ z,H z ∂ν)+(∫ z,B z ∂ν)) := by rw [integral_add hH hB]
      _ ≤ (q*r)^(-p)*(C*(q*r)^p*(∫ z,W z ∂ν)+b+(A*(∫ z,I z ∂ν)+b)) :=
        mul_le_mul_of_nonneg_left (add_le_add hmeanH hmeanB) hqp
      _ = _ := by
        calc
          _ = C*((q*r)^(-p)*(q*r)^p)*(∫ z,W z ∂ν)+(q*r)^(-p)*(A*(∫ z,I z ∂ν))+2*(q*r)^(-p)*b := by ring
          _ = _ := by rw [hcancelq,hmul]; ring

lemma source_collar_missed
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (D : Set ℂ) (q r L : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hL : 1 < L)
    (hy : ∀ z ∈ D, r ≤ z.im) (ω : a.samples) (z : ℂ) (hz : z ∈ D) :
    (if sourceCollarStart D (γ ω) z (q*r) = ⊤ then (0:ℝ) else 1) ≤
      sourceCollarH D (γ ω) z r (q*r) (L*r)+sourceCollarB D (γ ω) z r (q*r) (L*r) ∧
    spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r) ≤
      r^(-codimension κ)*(r^codimension κ*spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z (q*r)*sourceCollarH D (γ ω) z r (q*r) (L*r))+
      (q*r)^(-codimension κ)*sourceCollarB D (γ ω) z r (q*r) (L*r) := by
  have hh := sourceSpatialWindowGeometry_proved (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) (a.F ω) ((a.continuous_B ω).const_mul _) (a.witness ω) κ hκ hκ8
    z (q*r) r (L*r) (mul_pos hq hr) (by nlinarith) (by nlinarith) (hy z hz)
  simp only [sourceCollarStart,sourceCollarH,sourceCollarB,ite_eq_left hz]
  refine ⟨hh.2.2.2.2.2.2.2.2.2.2.1,?_⟩
  have he : r^(-codimension κ)*r^codimension κ = 1 := by
    rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  simpa only [←mul_assoc,he,one_mul] using hh.2.2.2.2.2.2.2.2.2.2.2

lemma source_mesh_bounded_integrable {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] {f : X → ℝ} {K : ℝ}
    (hm : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ K) : Integrable f ν := by
  apply Integrable.of_bound hm.aestronglyMeasurable K
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb x).1] using (hb x).2)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_shifted_integral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ} (c : ℂ)
    (h : SourceDisjointWindows P ℱ ((fun z : ℂ => z+c) ⁻¹' D) r R K γ
      (fun z => σ (z+c)) (fun z => τ (z+c)) (fun z => Y (z+c)) (fun z => μ (z+c))) :
    Measurable (fun ω => ∫ z in D, (Y z ω-μ z ω)) := by
  have hm := window_source_integral_measurable h
  have he (ω : Ω) : (∫ z in ((fun z : ℂ => z+c) ⁻¹' D), (Y (z+c) ω-μ (z+c) ω)) =
      ∫ z in D, (Y z ω-μ z ω) := source_mesh_shift_integral c D (fun z => Y z ω-μ z ω)
  simpa only [he] using hm

lemma source_mesh_shifted_restricted_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} {D : Set ℂ} {r R K : ℝ} {γ : ℝ≥0 → Ω → ℂ}
    {σ τ : ℂ → Ω → WithTop ℝ≥0} {Y μ : ℂ → Ω → ℝ} (c : ℂ)
    (h : SourceDisjointWindows P ℱ ((fun z : ℂ => z+c) ⁻¹' D) r R K γ
      (fun z => σ (z+c)) (fun z => τ (z+c)) (fun z => Y (z+c)) (fun z => μ (z+c)))
    (hs : ∀ z, IsStoppingTime ℱ (σ z))
    (hK : 0 < K) {b : ℝ} (hb : 0 < b)
    (E : Set Ω) (hE : MeasurableSet[mΩ] E) (hEs : ∀ z, MeasurableSet[(hs z).measurableSpace] E) :
    (P.restrict E) {ω | b < ∫ z in D, (Y z ω-μ z ω)} ≤
      ENNReal.ofReal (P.real E*Real.exp (-(1/512:ℝ)*b^2/(K^2*R^2))) := by
  let F := {ω | b < ∫ z in D, (Y z ω-μ z ω)}
  have hF : MeasurableSet F := measurableSet_lt measurable_const (source_mesh_shifted_integral_measurable c h)
  have hWm : Measurable (fun ω => if ω ∈ E then (1:ℝ) else 0) :=
    Measurable.ite hE measurable_const measurable_const
  have hWs : ∀ z, Measurable[(hs z).measurableSpace] (fun ω => if ω ∈ E then (1:ℝ) else 0) :=
    fun z => Measurable.ite (hEs z) measurable_const measurable_const
  have hh := source_mesh_shifted_weighted_tail c h hs hK hb hWm hWs
    (fun ω => by split_ifs <;> norm_num) ⟨1,fun ω => by split_ifs <;> norm_num⟩
  have hi : (fun ω => (if ω ∈ E then (1:ℝ) else 0)*(if ω ∈ F then (1:ℝ) else 0)) =
      (F∩E).indicator 1 := by
    funext ω; by_cases he : ω ∈ E <;> by_cases hf : ω ∈ F <;> simp [he,hf]
  change (∫ ω, (if ω ∈ E then (1:ℝ) else 0)*(if ω ∈ F then (1:ℝ) else 0) ∂P) ≤ _ at hh
  rw [hi,integral_indicator_one (hF.inter hE)] at hh
  have hiE : (fun ω => if ω ∈ E then (1:ℝ) else 0) = E.indicator 1 := rfl
  rw [hiE,integral_indicator_one hE] at hh
  rw [Measure.restrict_apply hF]
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr hh

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_I_integrable
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) [IsFiniteMeasure (volume.restrict D)]
    (v : ℝ) (hy : ∀ z ∈ D, v ≤ z.im) (ω : a.samples) :
    IntegrableOn (fun z => if sourceCollarStart D (γ ω) z v = ⊤ then (0:ℝ) else 1) D := by
  have hm : Measurable (fun p : ℂ × a.samples =>
      if sourceCollarStart D (γ p.2) p.1 v = ⊤ then (0:ℝ) else 1) :=
    Measurable.ite (measurableSet_eq_fun (source_collarStart_joint a D hD v hy) measurable_const)
      measurable_const measurable_const
  exact source_mesh_bounded_integrable (K := 1)
    (hm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℂ => ω)))) (fun z => by split_ifs <;> norm_num)

lemma source_mesh_integral_recurrences
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L C Cbad c b : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hb : 0 ≤ b) (hy : ∀ z ∈ D, r ≤ z.im) (ω : a.samples) :
    let p := codimension κ
    let W := fun v z => spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
    let Ic := fun v z => if sourceCollarStart D (γ ω) z v = ⊤ then (0:ℝ) else 1
    let H := fun z => sourceCollarH D (γ ω) z r (q*r) (L*r)
    let B := fun z => sourceCollarB D (γ ω) z r (q*r) (L*r)
    let V := fun z => r^p*W (q*r) z*H z
    let μH := fun z => C*(q*r)^p*(if z ∈ D then W r z else 0)
    let μV := fun z => r^p*(if z ∈ D then W r z else 0)
    let μB := fun z => Cbad*L^(-c)*Ic r z
    (∫ z in D, (H z-μH z)) ≤ b → (∫ z in D, (V z-μV z)) ≤ b → (∫ z in D, (B z-μB z)) ≤ b →
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (q*r) D ≤
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r D+
        (Cbad*L^(-c)*q^(-p))*sourceMeshCount p D (γ ω) r+(2*q^(-p))*r^(-p)*b ∧
      sourceMeshCount p D (γ ω) (q*r) ≤
        C*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r D+
        (Cbad*L^(-c)*q^(-p))*sourceMeshCount p D (γ ω) r+(2*q^(-p))*r^(-p)*b := by
  intro p W Ic H B V μH μV μB hFH hFV hFB
  change (∫ z in D, W (q*r) z) ≤ (∫ z in D, W r z)+
    (Cbad*L^(-c)*q^(-p))*(r^(-p)*(∫ z in D, Ic r z))+(2*q^(-p))*r^(-p)*b ∧
    (q*r)^(-p)*(∫ z in D, Ic (q*r) z) ≤ C*(∫ z in D, W r z)+
    (Cbad*L^(-c)*q^(-p))*(r^(-p)*(∫ z in D, Ic r z))+(2*q^(-p))*r^(-p)*b
  have hp : 0 < p := by dsimp [p,codimension,dimension]; linarith
  have hfin : volume D ≠ ∞ := ne_top_of_le_ne_top (by finiteness : volume (ball c₀ 1) ≠ ∞) (measure_mono hDc)
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hqr : q*r ≤ r := (mul_le_mul_of_nonneg_right hq1.le hr.le).trans_eq (one_mul _)
  have hWi (v : ℝ) (hv : 0 < v) (hvr : v ≤ r) : IntegrableOn (fun z => W v z) D :=
    a.spatialGreenWeight_spatial_integrable hκ hκ8 v hv D hD hfin (fun z hz => hvr.trans (hy z hz)) ω
  have hIi (v : ℝ) (hvr : v ≤ r) : IntegrableOn (fun z => Ic v z) D :=
    source_mesh_I_integrable a D hD v (fun z hz => hvr.trans (hy z hz)) ω
  have hHi : IntegrableOn (fun z => H z) D := source_mesh_bounded_integrable
    ((source_collarHB_joint a D hD r (q*r) (L*r) hy).1.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℂ => ω))))
    (fun z => (source_collar_HB_bounds D (γ ω) z r (q*r) (L*r)).1)
  have hBi : IntegrableOn (fun z => B z) D := source_mesh_bounded_integrable
    ((source_collarHB_joint a D hD r (q*r) (L*r) hy).2.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℂ => ω))))
    (fun z => (source_collar_HB_bounds D (γ ω) z r (q*r) (L*r)).2)
  have hVm : Measurable (fun p : ℂ × a.samples => r^codimension κ*spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t p.2) (γ p.2) (a.G p.2) p.1 (q*r)*sourceCollarH D (γ p.2) p.1 r (q*r) (L*r)) := by
    simpa only [add_zero] using source_collar_V_joint a D hD 0 q r L hy
  have hmsec : Measurable (fun z : ℂ => (z,ω)) := measurable_id.prodMk measurable_const
  have hVsec := hVm.comp hmsec
  simp only [Function.comp_def] at hVsec
  have hVi : IntegrableOn V D := source_mesh_bounded_integrable hVsec
    (fun z => source_collar_V_bounds a hκ hκ8 D q r (L*r) hq hq1 hr hy z ω)
  have hWceq : (fun z => if z ∈ D then W r z else 0) =ᵐ[volume.restrict D] (fun z => W r z) := by
    filter_upwards [ae_restrict_mem hD] with z hz; simp only [ite_eq_left hz]
  have hWci : IntegrableOn (fun z => if z ∈ D then W r z else 0) D := (hWi r hr le_rfl).congr hWceq.symm
  have hiH : (∫ z in D, μH z) = C*(q*r)^p*(∫ z in D, W r z) := by
    rw [show (∫ z in D, μH z) = C*(q*r)^p*(∫ z in D, if z ∈ D then W r z else 0) from integral_const_mul _ _,integral_congr_ae hWceq]
  have hiV : (∫ z in D, μV z) = r^p*(∫ z in D, W r z) := by
    rw [show (∫ z in D, μV z) = r^p*(∫ z in D, if z ∈ D then W r z else 0) from integral_const_mul _ _,integral_congr_ae hWceq]
  have hiB : (∫ z in D, μB z) = Cbad*L^(-c)*(∫ z in D, Ic r z) := integral_const_mul _ _
  rw [integral_sub hHi (hWci.const_mul _),hiH] at hFH
  rw [integral_sub hVi (hWci.const_mul _),hiV] at hFV
  rw [integral_sub hBi ((hIi r le_rfl).const_mul _),hiB] at hFB
  have hmiss : ∀ᵐ z ∂volume.restrict D,
      Ic (q*r) z ≤ H z+B z ∧ W (q*r) z ≤ r^(-p)*V z+(q*r)^(-p)*B z := by
    filter_upwards [ae_restrict_mem hD] with z hz
    exact source_collar_missed a hκ hκ8 D q r L hq hq1 hr hL hy ω z hz
  exact source_mesh_integrated_step (volume.restrict D) (fun z => W r z) (fun z => W (q*r) z)
    (fun z => Ic r z) (fun z => Ic (q*r) z) (fun z => H z) (fun z => V z) (fun z => B z)
    p q r C (Cbad*L^(-c)) b hq hq1 hr hp (hWi r hr le_rfl) (hWi (q*r) (mul_pos hq hr) hqr)
    (hIi r le_rfl) (hIi (q*r) hqr) hHi hVi hBi hb (hmiss.mono fun _ h => h.1) (hmiss.mono fun _ h => h.2)
    (sub_le_iff_le_add'.mp hFH) (sub_le_iff_le_add'.mp hFV) (sub_le_iff_le_add'.mp hFB)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_step
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (q r L C Cbad c b : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r)
    (hL : 1 < L) (hR : 3*(L*r) ≤ 1) (hC : 0 ≤ C) (hCb : 0 ≤ Cbad) (hb : 0 < b)
    (hy : ∀ z ∈ D, r ≤ z.im)
    (hmean : ∀ z (hz : z ∈ D),
      let μ := P.comap (Subtype.val : a.samples → Ω)
      let W := fun v (ω : a.samples) => spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
      let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r (q*r) (L*r)
      let B := fun ω : a.samples => sourceSpatialWindowB (γ ω) z r (q*r) (L*r)
      let hs := source_liveHit_stopping a z r (hy z hz)
      μ[H | hs.measurableSpace] ≤ᵐ[μ] (fun ω => C*(q*r)^codimension κ*W r ω) ∧
      μ[(fun ω => r^codimension κ*W (q*r) ω*H ω) | hs.measurableSpace] ≤ᵐ[μ]
        (fun ω => r^codimension κ*W r ω) ∧
      μ[B | hs.measurableSpace] ≤ᵐ[μ]
        (fun ω => Cbad*L^(-c)*(if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1)))
    (E : Set a.samples) (hE : MeasurableSet E)
    (hEs : ∀ z, MeasurableSet[(source_collarStart_stopping a D r hy z).measurableSpace] E) :
    ∃ F : Set a.samples, MeasurableSet F ∧
      ((P.comap Subtype.val).restrict E) F ≤ ENNReal.ofReal
        (3*(P.comap Subtype.val).real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-codimension κ))^2*(L*r)^2))) ∧
      ∀ ω ∉ F,
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (q*r) D ≤
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r D+
        (Cbad*L^(-c)*q^(-codimension κ))*sourceMeshCount (codimension κ) D (γ ω) r+
        (2*q^(-codimension κ))*r^(-codimension κ)*b ∧
      sourceMeshCount (codimension κ) D (γ ω) (q*r) ≤
        C*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r D+
        (Cbad*L^(-c)*q^(-codimension κ))*sourceMeshCount (codimension κ) D (γ ω) r+
        (2*q^(-codimension κ))*r^(-codimension κ)*b := by
  let p := codimension κ
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let W (v : ℝ) (z : ℂ) (ω : a.samples) := spatialGreenWeight κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
  let Ic (v : ℝ) (z : ℂ) (ω : a.samples) : ℝ := if sourceCollarStart D (γ ω) z v = ⊤ then 0 else 1
  let H (z : ℂ) (ω : a.samples) := sourceCollarH D (γ ω) z r (q*r) (L*r)
  let B (z : ℂ) (ω : a.samples) := sourceCollarB D (γ ω) z r (q*r) (L*r)
  let V (z : ℂ) (ω : a.samples) := r^p*W (q*r) z ω*H z ω
  let μH (z : ℂ) (ω : a.samples) := C*(q*r)^p*(if z ∈ D then W r z ω else 0)
  let μV (z : ℂ) (ω : a.samples) := r^p*(if z ∈ D then W r z ω else 0)
  let μB (z : ℂ) (ω : a.samples) := Cbad*L^(-c)*Ic r z ω
  let FH := {ω | b < ∫ z in D, (H z ω-μH z ω)}
  let FV := {ω | b < ∫ z in D, (V z ω-μV z ω)}
  let FB := {ω | b < ∫ z in D, (B z ω-μB z ω)}
  let σ := fun z (ω : a.samples) => sourceCollarStart D (γ ω) z r
  let τ := fun z (ω : a.samples) => sourceCollarFinish D (γ ω) z r (q*r) (L*r)
  have hWinH := source_mesh_H_window a hκ hκ8 D hD c₀ hDc q r L C hq hq1 hr hL hR hC hy (fun z hz => (hmean z hz).1)
  have hWinV := source_mesh_V_window a hκ hκ8 D hD c₀ hDc q r L hq hq1 hr hL hR hy (fun z hz => (hmean z hz).2.1)
  have hWinB := source_mesh_B_window a D hD c₀ hDc q r L Cbad c hq hq1 hr hL hR hCb hy (fun z hz => (hmean z hz).2.2)
  have hmH : MeasurableSet FH := measurableSet_lt measurable_const (source_mesh_shifted_integral_measurable (σ := σ) (τ := τ) (Y := H) (μ := μH) c₀ hWinH)
  have hmV : MeasurableSet FV := measurableSet_lt measurable_const (source_mesh_shifted_integral_measurable (σ := σ) (τ := τ) (Y := V) (μ := μV) c₀ hWinV)
  have hmB : MeasurableSet FB := measurableSet_lt measurable_const (source_mesh_shifted_integral_measurable (σ := σ) (τ := τ) (Y := B) (μ := μB) c₀ hWinB)
  have hp : 0 < p := by dsimp [p,codimension,dimension]; linarith
  have hK1 : 1 ≤ q^(-p) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq hq1.le (neg_nonpos.mpr hp.le)
  have hK : 0 < q^(-p) := Real.rpow_pos_of_pos hq _
  have hTailH := source_mesh_shifted_restricted_tail (σ := σ) (τ := τ) (Y := H) (μ := μH) c₀ hWinH
    (source_collarStart_stopping a D r hy) zero_lt_one hb E hE hEs
  have hTailV := source_mesh_shifted_restricted_tail (σ := σ) (τ := τ) (Y := V) (μ := μV) c₀ hWinV
    (source_collarStart_stopping a D r hy) hK hb E hE hEs
  have hTailB := source_mesh_shifted_restricted_tail (σ := σ) (τ := τ) (Y := B) (μ := μB) c₀ hWinB
    (source_collarStart_stopping a D r hy) zero_lt_one hb E hE hEs
  have hexp : Real.exp (-(1/512:ℝ)*b^2/(1^2*(L*r)^2)) ≤
      Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2)) := by
    apply Real.exp_le_exp.mpr
    have hr0 : 0 < L*r := mul_pos (by linarith) hr
    have hden : (L*r)^2 ≤ (q^(-p))^2*(L*r)^2 := by nlinarith [sq_nonneg (q^(-p)-1),sq_nonneg (L*r)]
    have hh := div_le_div_of_nonneg_left (show 0 ≤ (1/512:ℝ)*b^2 by positivity) (sq_pos_of_pos hr0) hden
    simpa only [one_pow,one_mul,neg_mul,neg_div] using neg_le_neg hh
  have hTail (F : Set a.samples) (hh : (μ.restrict E) F ≤ ENNReal.ofReal
      (μ.real E*Real.exp (-(1/512:ℝ)*b^2/(1^2*(L*r)^2)))) :
      (μ.restrict E) F ≤ ENNReal.ofReal (μ.real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2))) :=
    hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp (measureReal_nonneg)))
  refine ⟨FH∪FV∪FB,(hmH.union hmV).union hmB,?_,?_⟩
  · calc
      _ ≤ (μ.restrict E) FH+(μ.restrict E) FV+(μ.restrict E) FB :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal (μ.real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2)))+
           ENNReal.ofReal (μ.real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2)))+
           ENNReal.ofReal (μ.real E*Real.exp (-(1/512:ℝ)*b^2/((q^(-p))^2*(L*r)^2))) :=
        add_le_add (add_le_add (hTail FH hTailH) hTailV) (hTail FB hTailB)
      _ = _ := by rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · intro ω hω
    have hFH : (∫ z in D, (H z ω-μH z ω)) ≤ b := le_of_not_gt (fun hh => hω (Or.inl (Or.inl hh)))
    have hFV : (∫ z in D, (V z ω-μV z ω)) ≤ b := le_of_not_gt (fun hh => hω (Or.inl (Or.inr hh)))
    have hFB : (∫ z in D, (B z ω-μB z ω)) ≤ b := le_of_not_gt (fun hh => hω (Or.inr hh))
    exact source_mesh_integral_recurrences a hκ hκ8 D hD c₀ hDc q r L C Cbad c b
      hq hq1 hr hL hb.le hy ω hFH hFV hFB

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_mesh_scale_cancel {p r δ : ℝ} (hr : 0 < r) (_hδ : 0 < δ) (n : ℕ) :
    r^(-p)*(δ^(-p)*r^p/(n+1:ℝ)^2) = δ^(-p)/(n+1:ℝ)^2 := by
  have he : r^(-p)*r^p = 1 := by rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  calc
    _ = δ^(-p)*(r^(-p)*r^p)/(n+1:ℝ)^2 := by ring
    _ = _ := by rw [he,mul_one]

lemma source_mesh_radius_bound {q u L r δ : ℝ} (hq : 0 < q) (hu : 0 < u)
    (huq : u*q ≤ 1) (hL : 0 < L) (hr : 0 < r) (hrδ : r ≤ δ) (n : ℕ) :
    (L*u^n)*(r*q^n) ≤ L*δ := by
  have hh : (u*q)^n ≤ 1 := pow_le_one₀ (mul_nonneg hu.le hq.le) huq
  calc
    _ = (L*r)*(u*q)^n := by rw [mul_pow]; ring
    _ ≤ (L*r)*1 := mul_le_mul_of_nonneg_left hh (mul_nonneg hL.le hr.le)
    _ ≤ L*δ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hrδ hL.le

lemma source_mesh_alpha {c u L : ℝ} (hL : 0 < L) (hu : 0 < u) (n : ℕ) :
    (L*u^n)^(-c) = L^(-c)*(u^(-c))^n := by
  rw [Real.mul_rpow hL.le (pow_nonneg hu.le _),Real.rpow_pow_comm hu.le]

lemma source_mesh_failure_exponent {p q u L r δ K : ℝ}
    (hp1 : p < 1) (hq : 0 < q) (hu : 0 < u) (hL : 0 < L)
    (hr : 0 < r) (hrδ : r ≤ δ) (_hK : 0 < K) (n : ℕ) :
    δ^(-2:ℝ)/(K^2*L^2)*((q^p/(u*q))^2)^n/(n+1:ℝ)^4 ≤
    (δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)^2/(K^2*((L*u^n)*(r*q^n))^2) := by
  have hδ : 0 < δ := hr.trans_le hrδ
  have hn : 0 < (n+1:ℝ) := by positivity
  have hR : 0 < (L*u^n)*(r*q^n) := by positivity
  have hrq : 0 < r*q^n := by positivity
  have hid : (δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)/((L*u^n)*(r*q^n)) =
      (δ^(-p)*r^(p-1))/L*(q^p/(u*q))^n/(n+1:ℝ)^2 := by
    rw [Real.mul_rpow hr.le (pow_nonneg hq.le _),←Real.rpow_pow_comm hq.le,
      Real.rpow_sub hr,Real.rpow_one,div_pow,mul_pow]
    field_simp
  have hant := Real.rpow_le_rpow_of_nonpos hr hrδ (by linarith : p-1 ≤ 0)
  have hc : δ⁻¹ ≤ δ^(-p)*r^(p-1) := by
    calc
      δ⁻¹ = δ^(-p)*δ^(p-1) := by rw [←Real.rpow_add hδ]; ring_nf; rw [Real.rpow_neg_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hant (Real.rpow_nonneg hδ.le _)
  have ratio : δ⁻¹/L*(q^p/(u*q))^n/(n+1:ℝ)^2 ≤
      (δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)/((L*u^n)*(r*q^n)) := by
    rw [hid]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hc hL.le) (by positivity)) (by positivity)
  have hleft : 0 ≤ δ⁻¹/L*(q^p/(u*q))^n/(n+1:ℝ)^2 := by positivity
  have hsq : (δ⁻¹/L*(q^p/(u*q))^n/(n+1:ℝ)^2)^2 ≤
      ((δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)/((L*u^n)*(r*q^n)))^2 := by nlinarith
  calc
    _ = (δ⁻¹/L*(q^p/(u*q))^n/(n+1:ℝ)^2)^2/K^2 := by
      rw [Real.rpow_neg hδ.le,Real.rpow_two]
      simp only [div_pow,mul_pow,inv_pow,←pow_mul]
      ring
    _ ≤ ((δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)/((L*u^n)*(r*q^n)))^2/K^2 :=
      div_le_div_of_nonneg_right hsq (sq_nonneg K)
    _ = _ := by rw [div_pow]; ring

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_mesh_select_start {q rf δ : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hf : 0 < rf) (hfδ : rf ≤ δ) :
    ∃ r : ℝ, ∃ n : ℕ, 0 < r ∧ q*δ ≤ r ∧ r ≤ δ ∧ rf = r*q^n := by
  have hδ : 0 < δ := hf.trans_le hfδ
  obtain ⟨n,hn1,hn2⟩ := exists_nat_pow_near_of_lt_one (div_pos hf hδ)
    ((div_le_one₀ hδ).mpr hfδ) hq hq1
  have hqn : 0 < q^n := pow_pos hq _
  refine ⟨rf/q^n,n,div_pos hf hqn,?_,?_,?_⟩
  · apply (le_div_iff₀ hqn).mpr
    have hh := (lt_div_iff₀ hδ).mp hn1
    rw [pow_succ] at hh
    nlinarith
  · apply (div_le_iff₀ hqn).mpr
    have hh := (div_le_iff₀ hδ).mp hn2
    nlinarith
  · symm; exact div_mul_cancel₀ _ hqn.ne'

lemma source_mesh_height {z c : ℂ} {η r : ℝ} (hc : 1+η ≤ c.im)
    (hz : z ∈ ball c 1) (hr : r < η) : r < z.im := by
  have hdist : abs (z.im-c.im) ≤ dist z c := by
    simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-c)
  have hz' : dist z c < 1 := hz
  have hh := neg_abs_le (z.im-c.im)
  linarith

lemma source_mesh_count_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ) (hD : MeasurableSet D) (hfin : volume D ≠ ∞)
    (p r : ℝ) (hr : 0 < r) (hy : ∀ z ∈ D, r ≤ z.im) (ω : a.samples) :
    0 ≤ r^(-p)*(∫ z in D, if sourceCollarStart D (γ ω) z r = ⊤ then (0:ℝ) else 1) ∧
    r^(-p)*(∫ z in D, if sourceCollarStart D (γ ω) z r = ⊤ then (0:ℝ) else 1) ≤
      (volume D).toReal*r^(-p) := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hi : IntegrableOn (fun z => if sourceCollarStart D (γ ω) z r = ⊤ then (0:ℝ) else 1) D := by
    apply source_mesh_bounded_integrable (K := 1)
    · have hm : Measurable (fun p : ℂ × a.samples => if sourceCollarStart D (γ p.2) p.1 r = ⊤ then (0:ℝ) else 1) :=
        Measurable.ite (measurableSet_eq_fun (source_collarStart_joint a D hD r hy) measurable_const) measurable_const measurable_const
      exact hm.comp (measurable_id.prodMk measurable_const)
    · intro z; split_ifs <;> norm_num
  have hb : (∫ z in D, if sourceCollarStart D (γ ω) z r = ⊤ then (0:ℝ) else 1) ≤ (volume D).toReal := by
    calc
      _ ≤ ∫ _z in D, (1:ℝ) := integral_mono hi (integrable_const _) (fun z => by split_ifs <;> norm_num)
      _ = _ := by simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,measureReal_def]
  refine ⟨mul_nonneg (Real.rpow_nonneg hr.le _) (integral_nonneg (fun z => by split_ifs <;> norm_num)),?_⟩
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hr.le (-p))

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_mesh_grid_exponent {p q u L r δ K : ℝ}
    (hp1 : p < 1) (hq : 0 < q) (hu : 0 < u) (hL : 0 < L)
    (hr : 0 < r) (hrδ : r ≤ δ) (hK : 0 < K) (n : ℕ) :
    -(1/512:ℝ)*(δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)^2/(K^2*((L*u^n)*(r*q^n))^2) ≤
      -(1/(512*K^2*L^2))*δ^(-2:ℝ)*(((q^p/(u*q))^2)^n/(n+1:ℝ)^4) := by
  have hh := source_mesh_failure_exponent hp1 hq hu hL hr hrδ hK n
  calc
    _ = -(1/512:ℝ)*((δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2)^2/(K^2*((L*u^n)*(r*q^n))^2)) := by ring
    _ ≤ -(1/512:ℝ)*(δ^(-2:ℝ)/(K^2*L^2)*((q^p/(u*q))^2)^n/(n+1:ℝ)^4) :=
      mul_le_mul_of_nonpos_left hh (by norm_num)
    _ = _ := by ring

lemma source_mesh_grid_error {p q r δ E : ℝ} (hq : 0 < q) (hr : 0 < r) (hδ : 0 < δ) (n : ℕ) :
    E*(r*q^n)^(-p)*(δ^(-p)*(r*q^n)^p/(n+1:ℝ)^2) = E*δ^(-p)/(n+1:ℝ)^2 := by
  rw [mul_assoc,source_mesh_scale_cancel (mul_pos hr (pow_pos hq _)) hδ]
  ring

lemma source_mesh_grid_coefficient {c u L Cbad q p : ℝ} (hL : 0 < L) (hu : 0 < u) (n : ℕ) :
    Cbad*(L*u^n)^(-c)*q^(-p) = (Cbad*L^(-c)*q^(-p))*(u^(-c))^n := by
  rw [source_mesh_alpha hL hu]; ring

lemma source_mesh_initial_scale {p q r δ : ℝ} (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ)
    (hr : q*δ ≤ r) : r^(-p) ≤ q^(-p)*δ^(-p) := by
  rw [←Real.mul_rpow hq.le hδ.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos hq hδ) hr (neg_nonpos.mpr hp.le)

lemma source_mesh_ball_volume (c : ℂ) : volume (ball c 1) = volume (ball (0:ℂ) 1) := by
  rw [Complex.volume_ball,Complex.volume_ball]
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_mesh_choose_delta (η L : ℝ) (hη : 0 < η) (hL : 0 < L) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < η/2 ∧ δ₀ ≤ 1 ∧ 3*L*δ₀ ≤ 1 := by
  let δ₀ := min (min (η/4) (1/2)) (1/(6*L))
  have hpos : 0 < δ₀ := by dsimp [δ₀]; positivity
  refine ⟨δ₀,hpos,?_,?_,?_⟩
  · have := (min_le_left (min (η/4) (1/2)) (1/(6*L))).trans (min_le_left _ _)
    change δ₀ ≤ η/4 at this
    linarith
  · exact ((min_le_left _ _).trans (min_le_right _ _)).trans (by norm_num)
  · have hh : δ₀ ≤ 1/(6*L) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 6*L)).mp hh
    nlinarith
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_grid_step
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 4 < κ) (hκ8 : κ < 8) (m : SourceMeshParameters κ)
    (D : Set ℂ) (hD : MeasurableSet D) (c₀ : ℂ) (hDc : D ⊆ ball c₀ 1)
    (r δ : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) (hR : 3*m.L*δ ≤ 1)
    (hy : ∀ z ∈ D, δ < z.im) (n : ℕ)
    (E : Set a.samples) (hE : MeasurableSet E)
    (hEs : ∀ z, MeasurableSet[(source_collarStart_stopping a D (r*m.q^n)
      (fun z hz => (source_mesh_grid_radius_le m.hq m.hq1 hr hrδ n).trans (hy z hz).le) z).measurableSpace] E) :
    ∃ F : Set a.samples, MeasurableSet F ∧
      ((P.comap Subtype.val).restrict E) F ≤ ENNReal.ofReal
        (3*(P.comap Subtype.val).real E*Real.exp (-(1/(512*(m.q^(-codimension κ))^2*m.L^2))*
          δ^(-2:ℝ)*(((m.q^codimension κ/(m.u*m.q))^2)^n/(n+1:ℝ)^4))) ∧
      ∀ ω ∉ F,
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^(n+1)) D ≤
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^n) D+
        ((m.Cbad*m.L^(-m.c)*m.q^(-codimension κ))*(m.u^(-m.c))^n)*sourceMeshCount (codimension κ) D (γ ω) (r*m.q^n)+
        (2*m.q^(-codimension κ))*δ^(-codimension κ)/(n+1:ℝ)^2 ∧
      sourceMeshCount (codimension κ) D (γ ω) (r*m.q^(n+1)) ≤
        m.C*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^n) D+
        ((m.Cbad*m.L^(-m.c)*m.q^(-codimension κ))*(m.u^(-m.c))^n)*sourceMeshCount (codimension κ) D (γ ω) (r*m.q^n)+
        (2*m.q^(-codimension κ))*δ^(-codimension κ)/(n+1:ℝ)^2 := by
  have hp1 : codimension κ < 1 := by dsimp [codimension,dimension]; linarith
  have hk : 0 < κ := by linarith
  have hδ : 0 < δ := hr.trans_le hrδ
  have hL : 0 < m.L := lt_trans zero_lt_one m.hL
  have hu : 0 < m.u := lt_trans zero_lt_one m.hu
  have hrn : 0 < r*m.q^n := mul_pos hr (pow_pos m.hq _)
  have hy' (z : ℂ) (hz : z ∈ D) : r*m.q^n < z.im :=
    (source_mesh_grid_radius_le m.hq m.hq1 hr hrδ n).trans_lt (hy z hz)
  have hLn : 1 < m.L*m.u^n := m.hL.trans_le
    (by simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ m.hu.le) hL.le)
  have hRn : 3*((m.L*m.u^n)*(r*m.q^n)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (source_mesh_radius_bound m.hq hu m.huq.le hL hr hrδ n) (by norm_num)).trans (by simpa only [mul_assoc] using hR)
  obtain ⟨F,hFm,hFt,hFg⟩ := source_mesh_step a hk hκ8 D hD c₀ hDc m.q (r*m.q^n) (m.L*m.u^n)
    m.C m.Cbad m.c (δ^(-codimension κ)*(r*m.q^n)^codimension κ/(n+1:ℝ)^2)
    m.hq m.hq1 hrn hLn hRn m.hC.le m.hCb.le (by positivity) (fun z hz => (hy' z hz).le)
    (fun z hz => by
      obtain ⟨hs,hH,hV,hB⟩ := m.means Ω ‹MeasurableSpace Ω› P inferInstance γ a z
        (m.q*(r*m.q^n)) (r*m.q^n) (m.L*m.u^n) (mul_pos m.hq hrn) le_rfl (hy' z hz) hLn
      exact ⟨hH,hV,hB⟩) E hE hEs
  refine ⟨F,hFm,hFt.trans ?_,?_⟩
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact source_mesh_grid_exponent hp1 m.hq hu hL hr hrδ (Real.rpow_pos_of_pos m.hq _) n
  · intro ω hω
    have hh := hFg ω hω
    have hrnext : m.q*(r*m.q^n) = r*m.q^(n+1) := by rw [pow_succ]; ring
    rwa [hrnext,source_mesh_grid_coefficient hL hu,
      source_mesh_grid_error m.hq hr hδ] at hh
end
end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window Propagation for chordal SLE. -/

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma geometric_over_quartic_ge_linear {β : ℝ} (hβ : 1 < β) :
    ∃ k : ℝ, 0 < k ∧ ∀ n : ℕ, k*(n+1:ℝ) ≤ β^n/(n+1:ℝ)^4 := by
  have hβ0 : 0 < β := by linarith
  have hir : 0 < β⁻¹ := inv_pos.mpr hβ0
  have hi1 : β⁻¹ < 1 := (inv_lt_one₀ hβ0).mpr hβ
  have hnorm : ‖β⁻¹‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_pos hir] using hi1
  have hs := summable_pow_mul_geometric_of_norm_lt_one 5 hnorm
  have hss := ((summable_nat_add_iff 1).mpr hs).div_const (β⁻¹)
  have hseq : Summable (fun n : ℕ => (n+1:ℝ)^5/β^n) := by
    apply hss.congr
    intro n
    simp only [Nat.cast_add,Nat.cast_one,pow_succ,inv_pow]
    field_simp [ne_of_gt hβ0]
  let T : ℝ := ∑' n : ℕ, (n+1:ℝ)^5/β^n
  have hn (n : ℕ) : (n+1:ℝ)^5/β^n ≤ T :=
    hseq.le_tsum n (fun j _ => by positivity)
  have hT : 0 < T := by have := hn 0; norm_num at this; linarith
  refine ⟨T⁻¹,inv_pos.mpr hT,fun n => ?_⟩
  have hn0 : 0 < (n+1:ℝ) := by positivity
  have hp0 : 0 < β^n := pow_pos hβ0 _
  have hn' : (n+1:ℝ)^5 ≤ T*β^n := (div_le_iff₀ hp0).mp (hn n)
  apply (le_div_iff₀ (pow_pos hn0 4)).mpr
  apply (mul_le_mul_iff_right₀ hT).mp
  calc
    T * (T⁻¹ * (n+1:ℝ) * (n+1:ℝ)^4) = (n+1:ℝ)^5 := by field_simp
    _ ≤ T * β^n := hn'

lemma all_levels_exceptional_sum {b β : ℝ} (hb : 0 < b) (hβ : 1 < β) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ D T : ℝ, 0 ≤ D → 1 ≤ T →
      (∑' n : ℕ, ENNReal.ofReal (D*Real.exp (-b*T*(β^n/(n+1:ℝ)^4)))) ≤
        ENNReal.ofReal (D*C*Real.exp (-c*T)) := by
  obtain ⟨k,hk,hkn⟩ := geometric_over_quartic_ge_linear hβ
  let c := b*k
  have hc : 0 < c := mul_pos hb hk
  let r := Real.exp (-c)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := (Real.exp_lt_one_iff).mpr (neg_neg_of_pos hc)
  refine ⟨(1-r)⁻¹,c,inv_pos.mpr (sub_pos.mpr hr1),hc,?_⟩
  intro D T hD hT
  have hT0 : 0 ≤ T := by linarith
  have hn (n : ℕ) : D*Real.exp (-b*T*(β^n/(n+1:ℝ)^4)) ≤
      (D*Real.exp (-c*T))*r^n := by
    have hbound := mul_le_mul_of_nonneg_left (hkn n) (mul_nonneg hb.le hT0)
    have hneg : -b*T*(β^n/(n+1:ℝ)^4) ≤ -c*T + (n:ℝ)*(-c) := by
      have hh : c*(T-1)*(n:ℝ) ≥ 0 := by positivity
      dsimp [c] at *
      nlinarith
    calc
      _ ≤ D*Real.exp (-c*T + (n:ℝ)*(-c)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) hD
      _ = _ := by rw [Real.exp_add,Real.exp_nat_mul]; ring
  have hsum := (hasSum_geometric_of_lt_one hr.le hr1).mul_left (D*Real.exp (-c*T))
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((D*Real.exp (-c*T))*r^n) :=
      ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal (hn n))
    _ = ENNReal.ofReal ((D*Real.exp (-c*T))*(1-r)⁻¹) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable,hsum.tsum_eq]
    _ = _ := by congr 1; ring

 
lemma reciprocal_square_partial_sum_strong (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), 1/(j+1:ℝ)^2) ≤ 2 - 1/(n+1:ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : 0 < (n+1:ℝ) := by positivity
    have hn2 : 0 < (n+2:ℝ) := by positivity
    have hp : 1/(n+2:ℝ)^2 ≤ 1/(n+1:ℝ) - 1/(n+2:ℝ) := by
      calc
        _ ≤ 1/((n+1:ℝ)*(n+2:ℝ)) := by
          apply one_div_le_one_div_of_le (mul_pos hn hn2)
          nlinarith
        _ = _ := by field_simp; ring
    simp only [Nat.cast_add,Nat.cast_one] at *
    rw [show (n:ℝ)+1+1 = n+2 by ring]
    linarith

lemma reciprocal_square_partial_sum_le_two (n : ℕ) :
    (∑ j ∈ Finset.range n, 1/(j+1:ℝ)^2) ≤ 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    have := reciprocal_square_partial_sum_strong n
    have : 0 ≤ 1/(n+1:ℝ) := by positivity
    linarith [reciprocal_square_partial_sum_strong n]

lemma discrete_gronwall_exp (U α e : ℕ → ℝ) (hU : 0 ≤ U 0)
    (hα : ∀ n, 0 ≤ α n) (he : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, U (n+1) ≤ (1+α n)*U n+e n) :
    ∀ n, U n ≤ (U 0 + ∑ j ∈ Finset.range n, e j) *
      Real.exp (∑ j ∈ Finset.range n, α j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have hV : 0 ≤ U 0 + ∑ j ∈ Finset.range n, e j :=
      add_nonneg hU (Finset.sum_nonneg (fun j _ => he j))
    have hsum : 0 ≤ (∑ j ∈ Finset.range n, α j) + α n :=
      add_nonneg (Finset.sum_nonneg (fun j _ => hα j)) (hα n)
    have hExp : 1 ≤ Real.exp ((∑ j ∈ Finset.range n, α j)+α n) :=
      Real.one_le_exp_iff.mpr hsum
    have hfac : 1+α n ≤ Real.exp (α n) := by linarith [Real.add_one_le_exp (α n)]
    calc
      U (n+1) ≤ (1+α n)*U n+e n := hrec n
      _ ≤ (1+α n)*((U 0+∑ j ∈ Finset.range n,e j)*
          Real.exp (∑ j ∈ Finset.range n,α j))+e n :=
        by
          gcongr
          · linarith [hα n]
      _ ≤ (U 0+∑ j ∈ Finset.range n,e j)*
          Real.exp ((∑ j ∈ Finset.range n,α j)+α n) +
          e n*Real.exp ((∑ j ∈ Finset.range n,α j)+α n) := by
        apply add_le_add
        · rw [Real.exp_add]
          nlinarith [mul_le_mul_of_nonneg_right hfac
            (mul_nonneg hV (Real.exp_pos (∑ j ∈ Finset.range n,α j)).le)]
        · exact le_mul_of_one_le_right (he n) hExp
      _ = _ := by ring

lemma two_recurrences_normalized (S A α e : ℕ → ℝ) (C₁ K : ℝ)
    (hC : 0 ≤ C₁) (hK : 1 ≤ K) (hCK : C₁ ≤ K)
    (hnonneg : ∀ n, 0 ≤ S n ∧ 0 ≤ A n)
    (hα : ∀ n, 0 ≤ α n) (he : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, S (n+1) ≤ S n+α n*A n+e n ∧
      A (n+1) ≤ C₁*S n+α n*A n+e n) :
    ∀ n, max (S (n+1)) (A (n+1)/K) ≤
      (1+K*α n)*max (S n) (A n/K)+e n := by
  have hK0 : 0 < K := by linarith
  intro n
  let U := max (S n) (A n/K)
  have hS : S n ≤ U := le_max_left _ _
  have hA : A n ≤ K*U := by
    have := (div_le_iff₀ hK0).mp (le_max_right (S n) (A n/K))
    simpa only [mul_comm] using this
  have hU : 0 ≤ U := (hnonneg n).1.trans hS
  apply max_le
  · calc
      S (n+1) ≤ S n+α n*A n+e n := (hrec n).1
      _ ≤ U+α n*(K*U)+e n := by gcongr; exact hα n
      _ = _ := by ring
  · apply (div_le_iff₀ hK0).mpr
    calc
      A (n+1) ≤ C₁*S n+α n*A n+e n := (hrec n).2
      _ ≤ K*U+K*(K*α n*U)+K*e n := by
        apply add_le_add
        · apply add_le_add
          · exact (mul_le_mul_of_nonneg_left hS hC).trans
              (mul_le_mul_of_nonneg_right hCK hU)
          · calc
              α n*A n ≤ α n*(K*U) := mul_le_mul_of_nonneg_left hA (hα n)
              _ = K*α n*U := by ring
              _ ≤ K*(K*α n*U) := le_mul_of_one_le_left (mul_nonneg (mul_nonneg hK0.le (hα n)) hU) hK
        · exact le_mul_of_one_le_left (he n) hK
      _ = _ := by ring

lemma window_recurrences_uniform (C₀ C₁ E θ a d : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hE : 0 ≤ E)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hd : 0 < d) (S A : ℕ → ℝ)
    (hnonneg : ∀ n, 0 ≤ S n ∧ 0 ≤ A n)
    (hini : S 0 ≤ C₀*d ∧ A 0 ≤ C₀*d)
    (hrec : ∀ n, S (n+1) ≤ S n+(a*θ^n)*A n+E*d/(n+1:ℝ)^2 ∧
      A (n+1) ≤ C₁*S n+(a*θ^n)*A n+E*d/(n+1:ℝ)^2) :
    ∀ n, S n ≤ ((C₀+2*E)*Real.exp ((max 1 (2*C₁))/2/(1-θ)))*d := by
  let K := max 1 (2*C₁)
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hCK : C₁ ≤ K := (by linarith : C₁ ≤ 2*C₁).trans (le_max_right _ _)
  let U := fun n => max (S n) (A n/K)
  let α := fun n : ℕ => a*θ^n
  let e := fun n : ℕ => E*d/(n+1:ℝ)^2
  have hα (n : ℕ) : 0 ≤ α n := mul_nonneg ha (pow_nonneg hθ _)
  have he (n : ℕ) : 0 ≤ e n := by dsimp [e]; positivity
  have hU0 : 0 ≤ U 0 := (hnonneg 0).1.trans (le_max_left _ _)
  have hrecU := two_recurrences_normalized S A α e C₁ K hC₁ hK hCK hnonneg hα he hrec
  have hG := discrete_gronwall_exp U (fun n => K*α n) e hU0
    (fun n => mul_nonneg hK0.le (hα n)) he hrecU
  have hIni : U 0 ≤ C₀*d := by
    apply max_le hini.1
    apply (div_le_iff₀ hK0).mpr
    exact hini.2.trans (le_mul_of_one_le_right (mul_nonneg hC₀ hd.le) hK)
  have hGeom := hasSum_geometric_of_lt_one hθ hθ1
  intro n
  have hsum_geom : (∑ j ∈ Finset.range n, θ^j) ≤ (1-θ)⁻¹ := by
    rw [← hGeom.tsum_eq]
    exact hGeom.summable.sum_le_tsum _ (fun j _ => pow_nonneg hθ j)
  have he_sum : (∑ j ∈ Finset.range n, e j) ≤ 2*E*d := by
    calc
      _ = (E*d)*(∑ j ∈ Finset.range n, 1/(j+1:ℝ)^2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; dsimp [e]; ring
      _ ≤ (E*d)*2 := mul_le_mul_of_nonneg_left
        (reciprocal_square_partial_sum_le_two n) (mul_nonneg hE hd.le)
      _ = _ := by ring
  have hα_sum : (∑ j ∈ Finset.range n, K*α j) ≤ K/2/(1-θ) := by
    calc
      _ = (K*a)*(∑ j ∈ Finset.range n, θ^j) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; dsimp [α]; ring
      _ ≤ (K*a)*(1-θ)⁻¹ := mul_le_mul_of_nonneg_left hsum_geom (mul_nonneg hK0.le ha)
      _ ≤ (K*(1/2))*(1-θ)⁻¹ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha1 hK0.le) (inv_nonneg.mpr (sub_pos.mpr hθ1).le)
      _ = _ := by ring
  calc
    S n ≤ U n := le_max_left _ _
    _ ≤ (U 0+∑ j ∈ Finset.range n,e j)*Real.exp (∑ j ∈ Finset.range n,K*α j) := hG n
    _ ≤ (C₀*d+2*E*d)*Real.exp (K/2/(1-θ)) := by
      apply mul_le_mul (add_le_add hIni he_sum) (Real.exp_le_exp.mpr hα_sum)
      · exact (Real.exp_pos _).le
      · positivity
    _ = _ := by dsimp [K]; ring

universe u


end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_mesh_finite_measure_propagation (p C₀ C₁ E b θ β : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hE : 0 ≤ E)
    (hb : 0 < b) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hβ : 1 < β) :
    ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (ν : Measure Ω) (v δ a : ℝ),
      0 ≤ v → 0 < δ → δ ≤ 1 → 0 ≤ a → a ≤ 1/2 →
      ∀ (S A : ℕ → Ω → ℝ) (B : ℕ → Set Ω),
      (∀ n ω, 0 ≤ S n ω ∧ 0 ≤ A n ω) →
      (∀ ω, S 0 ω ≤ C₀*δ^(-p) ∧ A 0 ω ≤ C₀*δ^(-p)) →
      (∀ n, ν (B n) ≤ ENNReal.ofReal
        (3*v*Real.exp (-b*δ^(-2:ℝ)*(β^n/(n+1:ℝ)^4)))) →
      (∀ n ω, ω ∉ B n →
        S (n+1) ω ≤ S n ω + (a*θ^n)*A n ω + E*δ^(-p)/(n+1:ℝ)^2 ∧
        A (n+1) ω ≤ C₁*S n ω + (a*θ^n)*A n ω + E*δ^(-p)/(n+1:ℝ)^2) →
      ν {ω | ∃ n, M*δ^(-p) < S n ω} ≤ ENNReal.ofReal (v*C*Real.exp (-c*δ^(-2:ℝ))) := by
  obtain ⟨C,c,hC,hc,hseries⟩ := all_levels_exceptional_sum hb hβ
  let M₀ := (C₀+2*E)*Real.exp ((max 1 (2*C₁))/2/(1-θ))
  have hM₀ : 0 ≤ M₀ := mul_nonneg (by linarith) (Real.exp_pos _).le
  refine ⟨M₀+1,3*C,c,by linarith,by positivity,hc,?_⟩
  intro Ω m ν v δ a hv hδ hδ1 ha ha1 S A B hnonneg hini hfail hrec
  have hd : 0 < δ^(-p) := Real.rpow_pos_of_pos hδ _
  have hT : 1 ≤ δ^(-2:ℝ) := by
    rw [Real.rpow_neg hδ.le,Real.rpow_two]
    exact one_le_inv₀ (sq_pos_of_pos hδ) |>.mpr (by nlinarith)
  have hsubset : {ω | ∃ n, (M₀+1)*δ^(-p) < S n ω} ⊆ ⋃ n, B n := by
    intro ω hω
    by_contra hnot
    have hgood (n : ℕ) : ω ∉ B n := fun hn => hnot (mem_iUnion.mpr ⟨n,hn⟩)
    have hbound := window_recurrences_uniform C₀ C₁ E θ a (δ^(-p))
      hC₀ hC₁ hE hθ hθ1 ha ha1 hd (fun n => S n ω) (fun n => A n ω)
      (fun n => hnonneg n ω) (hini ω) (fun n => hrec n ω (hgood n))
    obtain ⟨n,hn⟩ := hω
    have hn' : S n ω ≤ M₀*δ^(-p) := hbound n
    nlinarith
  calc
    _ ≤ ν (⋃ n, B n) := measure_mono hsubset
    _ ≤ ∑' n, ν (B n) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal
        (3*v*Real.exp (-b*δ^(-2:ℝ)*(β^n/(n+1:ℝ)^4))) := ENNReal.tsum_le_tsum hfail
    _ ≤ ENNReal.ofReal (3*v*C*Real.exp (-c*δ^(-2:ℝ))) := hseries (3*v) _ (by positivity) hT
    _ = _ := by congr 1; ring

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_mesh_uniform_past_tail (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8)
    (m : SourceMeshParameters κ) :
    ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
      (c₀ : ℂ) (r δ : ℝ), 0 < r → m.q*δ ≤ r → r ≤ δ → δ ≤ 1 → 3*m.L*δ ≤ 1 →
      (hy : ∀ z ∈ ball c₀ 1, δ < z.im) →
      ∀ (E : Set a.samples), MeasurableSet E →
      (∀ (v : ℝ) (_hv : 0 < v) (hvd : v ≤ δ) (z : ℂ),
        MeasurableSet[(source_collarStart_stopping a (ball c₀ 1) v
          (fun z hz => hvd.trans (hy z hz).le) z).measurableSpace] E) →
      ((P.comap Subtype.val).restrict E) {ω | ∃ n : ℕ, M*δ^(-codimension κ) <
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^n) (ball c₀ 1)} ≤
        ENNReal.ofReal ((P.comap Subtype.val).real E*C*Real.exp (-c*δ^(-2:ℝ))) := by
  let p := codimension κ
  let K := m.q^(-p)
  let b := 1/(512*K^2*m.L^2)
  let θ := m.u^(-m.c)
  let β := (m.q^p/(m.u*m.q))^2
  have hk : 0 < κ := by linarith
  have hp : 0 < p := by dsimp [p,codimension,dimension]; linarith
  have hp1 : p < 1 := by dsimp [p,codimension,dimension]; linarith
  have hK : 0 < K := Real.rpow_pos_of_pos m.hq _
  have hL : 0 < m.L := zero_lt_one.trans m.hL
  have hu : 0 < m.u := zero_lt_one.trans m.hu
  have hb : 0 < b := by dsimp [b]; positivity
  have hθ : 0 < θ := Real.rpow_pos_of_pos hu _
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg m.hu (neg_neg_of_pos m.hc)
  have hβ : 1 < β := by dsimp [β]; nlinarith [m.hratio]
  obtain ⟨M,C,c,hM,hC,hc,hprop⟩ := source_mesh_finite_measure_propagation p
    ((volume (ball (0:ℂ) 1)).toReal*K) m.C (2*K) b θ β hp hp1 (by positivity) m.hC.le
    (by positivity) hb hθ.le hθ1 hβ
  refine ⟨M,C,c,hM,hC,hc,?_⟩
  intro Ω ms P hP γ a c₀ r δ hr hqr hrδ hδ1 hR hy E hE hEs
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  have hδ : 0 < δ := hr.trans_le hrδ
  let S (n : ℕ) (ω : a.samples) := spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) (r*m.q^n) (ball c₀ 1)
  let A (n : ℕ) (ω : a.samples) := sourceMeshCount p (ball c₀ 1) (γ ω) (r*m.q^n)
  have hrn (n : ℕ) : 0 < r*m.q^n := mul_pos hr (pow_pos m.hq _)
  have hyr (n : ℕ) (z : ℂ) (hz : z ∈ ball c₀ 1) : r*m.q^n ≤ z.im :=
    (source_mesh_grid_radius_le m.hq m.hq1 hr hrδ n).trans (hy z hz).le
  have hfin : volume (ball c₀ 1) ≠ ∞ := by finiteness
  have hnonneg (n : ℕ) (ω : a.samples) : 0 ≤ S n ω ∧ 0 ≤ A n ω :=
    ⟨(a.spatialRealMass_bound hk hκ8 _ (hrn n) _ measurableSet_ball hfin (hyr n) ω).1,
      (source_mesh_count_bound a _ measurableSet_ball hfin p _ (hrn n) (hyr n) ω).1⟩
  have hini (ω : a.samples) : S 0 ω ≤ ((volume (ball (0:ℂ) 1)).toReal*K)*δ^(-p) ∧
      A 0 ω ≤ ((volume (ball (0:ℂ) 1)).toReal*K)*δ^(-p) := by
    have hs := (a.spatialRealMass_bound hk hκ8 r hr _ measurableSet_ball hfin
      (fun z hz => hrδ.trans (hy z hz).le) ω).2
    have ha := (source_mesh_count_bound a _ measurableSet_ball hfin p r hr
      (fun z hz => hrδ.trans (hy z hz).le) ω).2
    have hbound : (volume (ball c₀ 1)).toReal*r^(-p) ≤ ((volume (ball (0:ℂ) 1)).toReal*K)*δ^(-p) := by
      rw [source_mesh_ball_volume c₀]
      calc
        _ ≤ (volume (ball (0:ℂ) 1)).toReal*(m.q^(-p)*δ^(-p)) :=
          mul_le_mul_of_nonneg_left (source_mesh_initial_scale hp m.hq hδ hqr) ENNReal.toReal_nonneg
        _ = _ := by ring
    constructor
    · simpa only [S,pow_zero,mul_one] using hs.trans hbound
    · change (r*m.q^0)^(-p)*(∫ z in ball c₀ 1, if sourceCollarStart (ball c₀ 1) (γ ω) z (r*m.q^0) = ⊤ then (0:ℝ) else 1) ≤ _
      rw [pow_zero,mul_one]
      exact ha.trans hbound
  have hstep (n : ℕ) := source_mesh_grid_step a hκ hκ8 m (ball c₀ 1) measurableSet_ball c₀
    subset_rfl r δ hr hrδ hR hy n E hE
    (hEs _ (hrn n) (source_mesh_grid_radius_le m.hq m.hq1 hr hrδ n))
  choose F hFm hFt hFg using hstep
  exact hprop a.samples inferInstance (μ.restrict E) (μ.real E) δ (m.Cbad*m.L^(-m.c)*K)
    measureReal_nonneg hδ hδ1 (mul_nonneg (mul_nonneg m.hCb.le (Real.rpow_nonneg hL.le _)) hK.le) m.halpha S A F hnonneg hini hFt hFg
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_conditional_indicator_bound_on
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) (B F : Set Ω)
    (hB : MeasurableSet[m] B) (hF : MeasurableSet F) (G : ℝ) (hG : 0 ≤ G)
    (ht : ∀ A : Set Ω, MeasurableSet[m] A →
      (μ.restrict (A∩B)) F ≤ ENNReal.ofReal (μ.real (A∩B)*G)) :
    ∀ᵐ ω ∂μ, ω ∈ B → μ[(fun ω => if ω ∈ F then (1:ℝ) else 0) | m] ω ≤ G := by
  let f : Ω → ℝ := fun ω => if ω ∈ F then 1 else 0
  have hf : Integrable f μ := by
    exact (integrable_const (1:ℝ)).indicator hF
  have hBm : MeasurableSet B := hm _ hB
  have hfg : μ[B.indicator f | m] ≤ᵐ[μ] B.indicator (fun _ => G) := by
    apply source_condExp_le_of_setIntegral_le hm (hf.indicator hBm)
      ((integrable_const _).indicator hBm) (stronglyMeasurable_const.indicator hB)
    intro A hA
    rw [setIntegral_indicator hBm,setIntegral_indicator hBm]
    change (∫ ω in A∩B, F.indicator (fun _ => (1:ℝ)) ω ∂μ) ≤ _
    have he : (∫ ω in A∩B, F.indicator (fun _ => (1:ℝ)) ω ∂μ) = (μ.restrict (A∩B)).real F := by
      exact integral_indicator_one hF
    rw [he]
    have hh := (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity : 0 ≤ μ.real (A∩B)*G)).mp (ht A hA)
    simpa only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,measureReal_def] using hh
  filter_upwards [hfg,condExp_indicator hf hB] with ω hg he
  intro hω
  rw [he,Set.indicator_of_mem hω,Set.indicator_of_mem hω] at hg
  exact hg
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable


theorem sourcePhysicalMeshTail_proved : SourcePhysicalMeshTailTarget := by
  intro κ hκ hκ8 η hη
  obtain ⟨m⟩ := source_mesh_parameters κ hκ hκ8
  obtain ⟨M,C,c,hM,hC,hc,htail⟩ := source_mesh_uniform_past_tail κ hκ hκ8 m
  obtain ⟨δ₀,hδ₀,hδη,hδ1,hδR⟩ := source_mesh_choose_delta η m.L hη (zero_lt_one.trans m.hL)
  let CT := max M C
  have hCT : 0 < CT := hM.trans_le (le_max_left _ _)
  refine ⟨CT,c,δ₀,hCT,hc,hδ₀,by linarith,?_⟩
  intro Ω ms P hP γ a ρ hρ z₀ rf δ hf hfδ hδsmall μ F
  let : IsProbabilityMeasure P := hP
  have hδ : 0 < δ := hf.trans_le hfδ
  have hδh : δ < η/2 := hδsmall.trans_lt hδη
  by_cases hz : 1+η ≤ z₀.im
  · obtain ⟨r,n,hr,hqr,hrδ,hfr⟩ := source_mesh_select_start m.hq m.hq1 hf hfδ
    have hy (z : ℂ) (hz' : z ∈ ball z₀ 1) : δ < z.im :=
      source_mesh_height hz hz' (by linarith)
    let τ (ω : a.samples) := spatialHitTime (γ ω) z₀ (1+η/2)
    have hτ : IsStoppingTime a.filtration τ := source_mesh_center_stopping a z₀ η
    let B := {ω : a.samples | ρ ω ≤ τ ω}
    have hB : MeasurableSet[hρ.measurableSpace] B := hρ.measurableSet_le_stopping_time hτ
    have hF : MeasurableSet F := measurableSet_lt measurable_const (a.spatialRealMass_measurable (ball z₀ 1) rf)
    have hbound : ∀ᵐ ω ∂μ, ω ∈ B →
        μ[(fun ω => if ω ∈ F then (1:ℝ) else 0) | hρ.measurableSpace] ω ≤ CT*Real.exp (-c*δ^(-2:ℝ)) := by
      apply source_conditional_indicator_bound_on hρ.measurableSpace_le B F hB hF _ (by positivity)
      intro A hA
      have hE : MeasurableSet (A∩B) := hρ.measurableSpace_le _ (hA.inter hB)
      have hEτ : MeasurableSet[hτ.measurableSpace] (A∩B) :=
        ((hρ.min hτ).measurableSpace_mono hτ (fun ω => min_le_right _ _)) _ (hρ.measurableSet_inter_le hτ A hA)
      have hEs (v : ℝ) (hv : 0 < v) (hvd : v ≤ δ) (z : ℂ) :
          MeasurableSet[(source_collarStart_stopping a (ball z₀ 1) v
            (fun z hz => hvd.trans (hy z hz).le) z).measurableSpace] (A∩B) := by
        apply (hτ.measurableSpace_mono (source_collarStart_stopping a (ball z₀ 1) v
          (fun z hz => hvd.trans (hy z hz).le) z) _ ) _ hEτ
        intro ω
        exact source_mesh_center_before a (ball z₀ 1) z₀ subset_rfl η v hη
          (hvd.trans_lt hδh) hz (fun z hz => hvd.trans (hy z hz).le) z ω
      have hR : 3*m.L*δ ≤ 1 := (mul_le_mul_of_nonneg_left hδsmall (mul_nonneg (by norm_num) (zero_lt_one.trans m.hL).le)).trans hδR
      have ht := htail Ω ms P hP γ a z₀ r δ hr hqr hrδ (hδsmall.trans hδ1) hR hy (A∩B) hE hEs
      have hsub : F ⊆ {ω : a.samples | ∃ k : ℕ, M*δ^(-codimension κ) <
          spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^k) (ball z₀ 1)} := by
        intro ω hω
        refine ⟨n,?_⟩
        have hh : M*δ^(-codimension κ) ≤ CT*δ^(-codimension κ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hδ.le _)
        change CT*δ^(-codimension κ) < spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1) at hω
        rw [hfr] at hω
        exact hh.trans_lt hω
      calc
        _ ≤ ((P.comap Subtype.val).restrict (A∩B)) {ω : a.samples | ∃ k : ℕ, M*δ^(-codimension κ) <
            spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*m.q^k) (ball z₀ 1)} := measure_mono hsub
        _ ≤ _ := ht.trans (ENNReal.ofReal_le_ofReal (by
          have hh := mul_le_mul_of_nonneg_left (le_max_right M C) (measureReal_nonneg (μ := μ) (s := A∩B))
          have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-c*δ^(-2:ℝ))).le
          simpa only [mul_assoc] using hh'))
    filter_upwards [hbound] with ω hω
    intro hρfin hfree
    apply hω
    change ρ ω ≤ spatialHitTime (γ ω) z₀ (1+η/2)
    obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hρfin
    rw [←hs] at hfree ⊢
    simp only [WithTop.untopD_coe] at hfree
    exact source_mesh_free_before_center (a.trace_continuous ω) s z₀ η hη hfree
  · exact Eventually.of_forall fun ω _ hfree => False.elim (hz (source_mesh_free_im hη hfree).le)
end
end SLEExactGauge
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RetainedSeedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Seed Moments for chordal SLE. -/


section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_first_sphere_free {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hy : r ≤ z.im) (hs : r ≤ dist (γ 0) z)
    (s : ℝ≥0) (hfirst : spatialHitTime γ z r = s) :
    ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 s) := by
  intro w hw
  refine ⟨ball_subset_upperHalfPlane hy hw,?_⟩
  rintro ⟨u,hu,rfl⟩
  have hh := spatialHitTime_lt_of_dist_lt hc z r hs u hw
  rw [hfirst] at hh
  exact (not_lt_of_ge hu.2) (WithTop.coe_lt_coe.mp hh)

lemma source_live_hit_spatial_eq {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z)
    (s : ℝ≥0) (hh : liveSpatialHitTime γ z r = s) :
    spatialHitTime γ z r = s := by
  rw [liveSpatialHitTime_eq hc z r hs] at hh
  split_ifs at hh with ht hl
  · exact (WithTop.coe_ne_top hh.symm).elim
  · exact hh
  · exact (WithTop.coe_ne_top hh.symm).elim

lemma source_live_collar_free {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (hy : 4 ≤ z.im) (hs : 3 ≤ dist (γ 0) z)
    (s : ℝ≥0) (hh : liveSpatialHitTime γ z 3 = s) :
    closedBall z 2 ⊆ survivingDomain γ s := by
  have hm := source_liveHit_mem hc z 3 hs s hh
  have hball := ball_subset_survivingDomain (by norm_num : (0:ℝ)<3) hm.1
    (source_first_sphere_free hc z 3 (by linarith) hs s
      (source_live_hit_spatial_eq hc z 3 hs s hh))
  exact fun w hw => hball (by change dist w z < 3; have : dist w z ≤ 2 := hw; linarith)

lemma source_enter_implies_live_contact {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (hy : 4 ≤ z.im) (t : ℝ≥0) (ht : dist (γ t) z < 3) :
    liveSpatialHitTime γ z 3 ≠ ⊤ := by
  have hs : 3 ≤ dist (γ 0) z := by
    rw [h.2.1,dist_zero_left]
    have := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
    linarith
  have hh := spatialHitTime_lt_of_dist_lt h.1 z 3 hs t ht
  have hn : spatialHitTime γ z 3 ≠ ⊤ := ne_of_lt (hh.trans_le le_top)
  obtain ⟨s,he⟩ := WithTop.ne_top_iff_exists.mp hn
  have hst : s ≤ t := (WithTop.coe_lt_coe.mp (he ▸ hh)).le
  have hfree := source_first_sphere_free h.1 z 3 (by linarith) hs s he.symm
  have hl := h.surviving_of_free_ball_future_tip s t hst z 3 (by norm_num) hfree ht
  have hm := spatialHitTime_mem h.1 z 3 s he.symm
  exact ne_of_lt ((source_liveHit_le γ z 3 s hl hm.le).trans_lt (WithTop.coe_lt_top s))

lemma source_weight_zero_no_unit_entrance {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    (κ : ℝ) (z₀ : ℂ) (hy : 4 ≤ z₀.im) (rf : ℝ) (hf1 : rf ≤ 1)
    (hn : liveSpatialHitTime γ z₀ 3 = ⊤) (z : ℂ) (hz : z ∈ ball z₀ 1) :
    spatialGreenWeight κ U γ G z rf = 0 := by
  unfold spatialGreenWeight
  split_ifs with hb
  · rfl
  · have hn' : spatialHitTime γ z rf ≠ ⊤ := fun hh => hb hh
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn'
    have hm := spatialHitTime_mem h.1 z rf t ht.symm
    have hd : dist (γ t) z₀ < 3 := by
      have hz' : dist z z₀ < 1 := hz
      have hh := dist_triangle (γ t) z z₀
      linarith
    exact (source_enter_implies_live_contact h z₀ hy t hd hn).elim
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_event_bound_from_past {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) (A E : Set Ω)
    (hA : MeasurableSet[m] A) (hE : MeasurableSet E) (hEA : E ⊆ A)
    (K : ℝ) (hK : 0 ≤ K)
    (ht : ∀ᵐ ω ∂μ, ω ∈ A → μ[(fun ω => if ω ∈ E then (1:ℝ) else 0) | m] ω ≤ K) :
    μ E ≤ ENNReal.ofReal (μ.real A*K) := by
  have hi : Integrable (fun ω => if ω ∈ E then (1:ℝ) else 0) μ :=
    (integrable_const (1:ℝ)).indicator hE
  have hb := setIntegral_mono_ae_restrict (s := A) integrable_condExp.integrableOn
    (integrable_const K).integrableOn ((ae_restrict_iff' (hm _ hA)).mpr ht)
  rw [setIntegral_condExp hm hi hA] at hb
  change (∫ ω in A, E.indicator (fun _ => (1:ℝ)) ω ∂μ) ≤ _ at hb
  rw [setIntegral_indicator hE,inter_eq_right.mpr hEA,setIntegral_const,setIntegral_const] at hb
  simp only [smul_eq_mul,mul_one] at hb
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (mul_nonneg ENNReal.toReal_nonneg hK)).mpr hb

lemma source_live_unit_mesh_tail (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∃ C c δ₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 4 ≤ z₀.im →
    ∀ (rf δ : ℝ), 0 < rf → rf ≤ δ → δ ≤ δ₀ →
      (P.comap Subtype.val) {ω : a.samples | C*δ^(-codimension κ) <
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)} ≤
      ENNReal.ofReal ((P.comap Subtype.val).real {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤} *
        (C*Real.exp (-c*δ^(-2:ℝ)))) := by
  obtain ⟨C,c,δ₀,hC,hc,hδ,hδ1,ht⟩ := sourcePhysicalMeshTail_proved κ hκ hκ8 1 (by norm_num)
  refine ⟨C,c,δ₀,hC,hc,hδ,hδ1,?_⟩
  intro Ω m P hP γ a z₀ hz rf δ hf hfd hd
  let : IsProbabilityMeasure P := hP
  let ρ := fun ω : a.samples => liveSpatialHitTime (γ ω) z₀ 3
  have hρ : IsStoppingTime a.filtration ρ := source_liveHit_stopping a z₀ 3 (by linarith)
  let A := {ω : a.samples | ρ ω ≠ ⊤}
  have hA : MeasurableSet[hρ.measurableSpace] A := (measurableSet_eq_fun hρ.measurable measurable_const).compl
  apply source_event_bound_from_past hρ.measurableSpace_le A _ hA
    (measurableSet_lt measurable_const (a.spatialRealMass_measurable _ _))
  · intro ω hω
    by_contra hn
    have htop : liveSpatialHitTime (γ ω) z₀ 3 = ⊤ := by simpa only [A,ρ,mem_ofPred_eq,not_not] using hn
    have hzX : spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz'
      exact source_weight_zero_no_unit_entrance (a.witness ω) κ z₀ hz rf (hfd.trans (hd.trans hδ1.le)) htop z hz'
    change C*δ^(-codimension κ) < _ at hω
    rw [hzX] at hω
    exact (not_lt_of_ge (mul_nonneg hC.le (Real.rpow_nonneg (hf.trans_le hfd).le _))) hω
  · positivity
  · have hh := ht Ω m P hP γ a ρ hρ z₀ rf δ hf hfd hd
    filter_upwards [hh] with ω hω
    intro hωA
    apply hω hωA
    have hs : 3 ≤ dist (γ ω 0) z₀ := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
      linarith
    have he : liveSpatialHitTime (γ ω) z₀ 3 = ((ρ ω).untopD 0 : ℝ≥0) := by
      change ρ ω = _
      obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hωA
      rw [← ht]
      rfl
    change closedBall z₀ (1+1) ⊆ _
    convert source_live_collar_free (a.trace_continuous ω) z₀ hz hs ((ρ ω).untopD 0) he using 1
    all_goals try with_reducible_and_instances rfl
    norm_num

lemma source_live_entrance_bound {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 4 ≤ z₀.im) (hsmall : 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4))) :
    (P.comap Subtype.val).real {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤} ≤
      (uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ)*initialGreen κ z₀ := by
  apply le_trans (measureReal_mono (show {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤} ⊆
      {ω | ∃ t : ℝ≥0, dist (γ ω t) z₀ < 4} from ?_))
  · have hh := euclidean_approach a.brownian κ hκ hκ8 (fun ω : a.samples => γ ω) a.G a.F
      (Eventually.of_forall a.witness) z₀ (by change 0 < z₀.im; linarith) 4 (by norm_num) hz hsmall
    change ((P.comap Subtype.val) {ω : a.samples | ∃ t : ℝ≥0, dist (γ ω t) z₀ < 4}).toReal ≤ _
    calc
      _ ≤ _ := hh
      _ = _ := by ring
  · intro ω hω
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hω
    have hs : 3 ≤ dist (γ ω 0) z₀ := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
      linarith
    exact ⟨t,by rw [(source_liveHit_mem (a.trace_continuous ω) z₀ 3 hs t ht.symm).2]; norm_num⟩
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_mesh_tail_to_stretched {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (p C c δ₀ v rf a : ℝ) (hp : 0 < p)
    (_hC : 0 < C) (_hc : 0 < c) (hδ : 0 < δ₀) (hv : 0 ≤ v) (_hf : 0 < rf) (_ha : 0 ≤ a)
    (hbound : ∀ ω, X ω ≤ v*rf^(-p))
    (ht : ∀ δ : ℝ, rf ≤ δ → δ ≤ δ₀ → μ {ω | C*δ^(-p) < X ω} ≤
      ENNReal.ofReal (a*(C*Real.exp (-c*δ^(-2:ℝ))))) :
    ∀ u : ℝ, 1 ≤ u →
      μ {ω | max C v*δ₀^(-p)*u < X ω} ≤
        ENNReal.ofReal (a*C*Real.exp (-(c*δ₀^(-2:ℝ))*u^(2/p))) := by
  intro u hu1
  have hu : 0 < u := zero_lt_one.trans_le hu1
  let δ := δ₀*u^(-1/p)
  have he0 : -1/p ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le
  have hδp : 0 < δ := mul_pos hδ (Real.rpow_pos_of_pos hu _)
  have hδd : δ ≤ δ₀ := by
    dsimp [δ]
    exact mul_le_of_le_one_right hδ.le (Real.rpow_le_one_of_one_le_of_nonpos hu1 he0)
  have he : δ^(-p) = δ₀^(-p)*u := by
    dsimp [δ]
    rw [Real.mul_rpow hδ.le (Real.rpow_nonneg hu.le _),← Real.rpow_mul hu.le]
    have he : (-1/p)*(-p) = 1 := by field_simp
    rw [he,Real.rpow_one]
  have hex : δ^(-2:ℝ) = δ₀^(-2:ℝ)*u^(2/p) := by
    dsimp [δ]
    rw [Real.mul_rpow hδ.le (Real.rpow_nonneg hu.le _),← Real.rpow_mul hu.le]
    congr 2
    ring
  have hn (b : ℝ) (hb : b ≤ max C v) : b*δ^(-p) ≤ max C v*δ₀^(-p)*u := by
    rw [he,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hδ.le _)) hu.le
  by_cases hfd : rf ≤ δ
  · apply (measure_mono (show {ω | max C v*δ₀^(-p)*u < X ω} ⊆
        {ω | C*δ^(-p) < X ω} from fun ω hω => (hn C (le_max_left _ _)).trans_lt hω)).trans
    calc
      _ ≤ _ := ht δ hfd hδd
      _ = _ := by
        rw [hex]
        have he : -c*(δ₀^(-2:ℝ)*u^(2/p)) = -(c*δ₀^(-2:ℝ))*u^(2/p) := by ring
        rw [he,mul_assoc]
  · have hx (ω : Ω) : X ω ≤ max C v*δ₀^(-p)*u := by
      calc
        X ω ≤ v*rf^(-p) := hbound ω
        _ ≤ v*δ^(-p) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hδp (le_of_not_ge hfd) (by linarith)) hv
        _ ≤ _ := hn v (le_max_right _ _)
    have he : {ω | max C v*δ₀^(-p)*u < X ω} = ∅ := by
      ext ω; simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]; exact not_lt_of_ge (hx ω)
    rw [he,measure_empty]
    exact bot_le
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section


theorem sourceLiveEntranceTail_proved : SourceLiveEntranceTailTarget := by
  intro κ hκ hκ8
  obtain ⟨C,c,δ₀,hC,hc,hδ,hδ1,ht⟩ := source_live_unit_mesh_tail κ hκ hκ8
  let v := (volume (ball (0:ℂ) 1)).toReal
  let M := max C v*δ₀^(-codimension κ)
  let b := c*δ₀^(-2:ℝ)
  let A := uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ
  have hk : 0 < κ := by linarith
  have hp : 0 < codimension κ := codimension_pos κ hκ8
  have hM : 0 < M := mul_pos (hC.trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos hδ _)
  have hb : 0 < b := mul_pos hc (Real.rpow_pos_of_pos hδ _)
  have hA : 0 < A := mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hk hκ8 zero_lt_one)
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨M,A*C,b,hM,mul_pos hA hC,hb,?_⟩
  intro Ω m P hP γ a z₀ hz hsmall rf u hf hf1 hu
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hx (ω : a.samples) : X ω ≤ v*rf^(-codimension κ) := by
    have hh := (a.spatialRealMass_bound hk hκ8 rf hf (ball z₀ 1) measurableSet_ball
      (measure_ball_lt_top (μ := volume) (x := z₀) (r := 1)).ne (fun z hz' => ?_) ω).2
    · simpa only [v,Complex.volume_ball] using hh
    · have hd : abs (z.im-z₀.im) ≤ dist z z₀ := by
        simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
      have hh : dist z z₀ < 1 := hz'
      have ha := neg_abs_le (z.im-z₀.im)
      linarith
  have ht' := source_mesh_tail_to_stretched μ X (codimension κ) C c δ₀ v rf
    (μ.real {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤}) hp hC hc hδ
    ENNReal.toReal_nonneg hf ENNReal.toReal_nonneg hx
    (fun δ hfd hd => ht Ω m P hP γ a z₀ hz rf δ hf hfd hd) u hu
  apply ht'.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (A*initialGreen κ z₀)*C*Real.exp (-b*u^(2/codimension κ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (source_live_entrance_bound a hk hκ8 z₀ hz hsmall) hC.le) (Real.exp_pos _).le
    _ = _ := by ring
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_scaled_radius_hit_iff (c : ℝ≥0) (hc : 0 < c)
    (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (t : ℝ≥0) :
    dist (sourceScaleTrace c γ t) ((c : ℂ) * z) - (c : ℝ) * r = 0 ↔
      dist (γ (sourceScaleTime c t)) z - r = 0 := by
  have hcR : 0 < (c : ℝ) := hc
  rw [sourceScaleTrace, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hcR, ← dist_eq_norm, ← mul_sub]
  exact mul_eq_zero.trans (or_iff_right hcR.ne')

lemma source_scale_spatial_hit (c : ℝ≥0) (hc : 0 < c)
    (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) :
    spatialHitTime (sourceScaleTrace c γ) ((c : ℂ) * z) ((c : ℝ) * r) =
      WithTop.map (fun t : ℝ≥0 => c ^ 2 * t) (spatialHitTime γ z r) := by
  classical
  let S : Set ℝ≥0 := {t | dist (γ t) z - r = 0}
  let Sc : Set ℝ≥0 := {t | dist (sourceScaleTrace c γ t) ((c : ℂ) * z) - (c : ℝ) * r = 0}
  let e : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (c ^ 2) (pow_pos hc 2)
  have he (x : ℝ≥0) : e x = c ^ 2 * x := rfl
  have htime (x : ℝ≥0) : sourceScaleTime c (c ^ 2 * x) = x := by
    simp [sourceScaleTime, hc.ne']
  have hset : e '' S = Sc := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (source_scaled_radius_hit_iff c hc γ z r _).2 (by simpa only [he, htime] using (show dist (γ u) z - r = 0 from hu))
    · intro ht
      refine ⟨sourceScaleTime c t, (source_scaled_radius_hit_iff c hc γ z r t).1 ht, ?_⟩
      simp [he, sourceScaleTime, mul_div_cancel₀ _ (pow_ne_zero 2 hc.ne')]
  unfold spatialHitTime hittingAfter
  simp only [zero_le, true_and, Set.mem_singleton_iff]
  change (if Sc.Nonempty then ((sInf Sc : ℝ≥0) : WithTop ℝ≥0) else ⊤) =
    WithTop.map (fun t : ℝ≥0 => c^2*t) (if S.Nonempty then ((sInf S : ℝ≥0) : WithTop ℝ≥0) else ⊤)
  have hh : Sc.Nonempty ↔ S.Nonempty := by rw [← hset]; exact Set.image_nonempty
  by_cases hS : S.Nonempty
  · rw [ite_eq_left hS, ite_eq_left (hh.mpr hS), WithTop.map_coe]
    congr 1
    rw [← he, e.map_csInf' hS (OrderBot.bddBelow S), hset]
  · rw [ite_eq_right hS, ite_eq_right (mt hh.mp hS), WithTop.map_top]

lemma source_scale_spatial_hit_top (c : ℝ≥0) (hc : 0 < c)
    (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) :
    spatialHitTime (sourceScaleTrace c γ) ((c : ℂ) * z) ((c : ℝ) * r) = ⊤ ↔
      spatialHitTime γ z r = ⊤ := by
  rw [source_scale_spatial_hit c hc]
  simp

lemma source_scale_spatial_hit_value (c : ℝ≥0) (hc : 0 < c)
    (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) :
    (spatialHitTime (sourceScaleTrace c γ) ((c : ℂ) * z) ((c : ℝ) * r)).untopD 0 =
      c ^ 2 * (spatialHitTime γ z r).untopD 0 := by
  rw [source_scale_spatial_hit c hc]
  cases hh : spatialHitTime γ z r
  · simp
  · rfl

lemma source_scale_chart_deriv (c : ℝ≥0) (hc : 0 < c)
    (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) :
    deriv (sourceScaleChart c G t) ((c : ℂ) * z) = deriv (G (sourceScaleTime c t)) z := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  change deriv (fun w : ℂ => (c : ℂ) * G (sourceScaleTime c t) (w / (c : ℂ))) _ = _
  rw [deriv_const_mul_field]
  simp_rw [div_eq_mul_inv, mul_comm _ ((c : ℂ)⁻¹)]
  rw [deriv_comp_mul_left]
  simp only [smul_eq_mul]
  simp [hcC]

lemma source_scale_fullRadius (c : ℝ≥0) (hc : 0 < c)
    (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) :
    fullRadius (sourceScaleChart c G) t ((c : ℂ) * z) =
      (c : ℝ) * fullRadius G (sourceScaleTime c t) z := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold fullRadius
  rw [source_scale_chart_deriv c hc]
  simp only [sourceScaleChart, mul_div_cancel_left₀ _ hcC, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  ring

lemma source_scale_greenDensity (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ) :
    greenDensity κ (fun u => (c : ℝ) * U (sourceScaleTime c u))
      (sourceScaleTrace c γ) (sourceScaleChart c G) t ((c : ℂ) * z) =
    ((c : ℝ) ^ (-codimension κ)) * greenDensity κ U γ G (sourceScaleTime c t) z := by
  have hcR : 0 < (c : ℝ) := hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hlive : (c : ℂ) * z ∈ survivingDomain (sourceScaleTrace c γ) t ↔
      z ∈ survivingDomain γ (sourceScaleTime c t) := by
    simpa [hcC] using source_scale_domain_iff c t hc γ ((c : ℂ) * z)
  by_cases hz : z ∈ survivingDomain γ (sourceScaleTime c t)
  · simp only [greenDensity,ite_eq_left hz,ite_eq_left (hlive.mpr hz)]
    rw [source_scale_fullRadius c hc]
    have hR : 0 ≤ fullRadius G (sourceScaleTime c t) z := by
      exact div_nonneg (mul_nonneg (by norm_num) (hw.2.2.2.2.2.1 _ hz).le) (norm_nonneg _)
    rw [Real.mul_rpow hcR.le hR]
    simp only [sourceScaleChart, mul_div_cancel_left₀ _ hcC, Complex.ofReal_mul, ← mul_sub]
    rw [Complex.arg_real_mul _ hcR]
    ring
  · simp only [greenDensity,ite_eq_right hz,ite_eq_right (mt hlive.mp hz),mul_zero]
lemma source_scale_spatial_greenWeight (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (z : ℂ) (r : ℝ) :
    spatialGreenWeight κ (fun u => (c : ℝ) * U (sourceScaleTime c u))
      (sourceScaleTrace c γ) (sourceScaleChart c G) ((c : ℂ) * z) ((c : ℝ) * r) =
    ((c : ℝ) ^ (-codimension κ)) * spatialGreenWeight κ U γ G z r := by
  unfold spatialGreenWeight
  simp only [source_scale_spatial_hit_top c hc]
  split_ifs with ht
  · simp
  · rw [source_scale_greenDensity κ c hc U γ G F hw, source_scale_spatial_hit_value c hc]
    simp [sourceScaleTime, hc.ne']

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_scale_initialGreen (κ : ℝ) (c : ℝ≥0) (hc : 0 < c) (z : ℂ) (hz : 0 ≤ z.im) :
    initialGreen κ ((c:ℂ)*z) = (c:ℝ)^(-codimension κ)*initialGreen κ z := by
  have hcR : 0 < (c:ℝ) := hc
  unfold initialGreen
  rw [Complex.arg_real_mul _ hcR]
  have him : 2*((c:ℂ)*z).im = (c:ℝ)*(2*z.im) := by simp [Complex.mul_im]; ring
  rw [him,Real.mul_rpow hcR.le (mul_nonneg (by norm_num) hz),mul_assoc]
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_scale_area_real_integral (c : ℝ≥0) (hc : 0 < c)
    (f : ℂ → ℝ) (K : Set ℂ) :
    (∫ z in (fun z : ℂ => (c : ℂ) * z) '' K, f z) =
      ((c : ℝ)^2) * ∫ z in K, f ((c : ℂ) * z) := by
  have hcR : 0 < (c : ℝ) := hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let e := Homeomorph.mulLeft₀ (c : ℂ) hcC
  have he (z : ℂ) : e z = (c : ℂ) * z := rfl
  have hvol (s : Set ℂ) : volume (e ⁻¹' s) =
      ENNReal.ofReal (((c : ℝ)^2)⁻¹) * volume s := by
    change volume ((fun z : ℂ => (c : ℂ) * z) ⁻¹' s) = _
    simpa only [Complex.real_smul, smul_eq_mul, Complex.finrank_real_complex,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (c : ℝ)))] using
      (volume : Measure ℂ).addHaar_preimage_smul hcR.ne' s
  have hp : MeasurePreserving e (ENNReal.ofReal ((c : ℝ)^2) • (volume : Measure ℂ)) volume := by
    refine ⟨e.continuous.measurable, ?_⟩
    apply Measure.ext
    intro s hs
    rw [e.measurableEmbedding.map_apply, Measure.smul_apply, smul_eq_mul, hvol, ← mul_assoc,
      ← ENNReal.ofReal_mul (sq_nonneg (c : ℝ)), mul_inv_cancel₀ (pow_ne_zero 2 hcR.ne'),
      ENNReal.ofReal_one, one_mul]
  have hh := hp.setIntegral_image_emb e.measurableEmbedding f K
  rw [Measure.restrict_smul,integral_smul_measure] at hh
  simpa only [he,ENNReal.toReal_ofReal (sq_nonneg (c:ℝ)),smul_eq_mul] using hh

lemma source_scale_spatialRealMass (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (r : ℝ) (K : Set ℂ) :
    spatialRealMass κ (fun t => (c:ℝ)*U (sourceScaleTime c t))
      (sourceScaleTrace c γ) (sourceScaleChart c G) ((c:ℝ)*r)
      ((fun z : ℂ => (c:ℂ)*z) '' K) =
      (c:ℝ)^dimension κ*spatialRealMass κ U γ G r K := by
  unfold spatialRealMass
  rw [source_scale_area_real_integral c hc]
  simp_rw [source_scale_spatial_greenWeight κ c hc U γ G F hw]
  rw [integral_const_mul,←mul_assoc]
  congr 1
  rw [←Real.rpow_natCast (c:ℝ) 2,←Real.rpow_add (show 0 < (c:ℝ) from hc)]
  congr 1
  simp [codimension]

lemma source_scale_ball (c : ℝ≥0) (hc : 0 < c) (z : ℂ) (r : ℝ) :
    (fun w : ℂ => (c:ℂ)*w) '' Metric.ball z r = Metric.ball ((c:ℂ)*z) ((c:ℝ)*r) := by
  have hcR : 0 < (c:ℝ) := hc
  simpa only [Complex.real_smul,smul_eq_mul,Real.norm_eq_abs,abs_of_pos hcR] using
    Metric.smul_image_ball (α := ℝ) hcR.ne' z r

lemma RegularSLEPresentation.sourceScaled_mass {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (c : ℝ≥0) (hc : 0 < c) (z : ℂ) (r rf : ℝ) (ω : a.samples) :
    spatialRealMass κ (fun t => Real.sqrt κ*(a.sourceScaled c hc).B t ω)
      (sourceScaleTrace c (γ ω)) ((a.sourceScaled c hc).G ω) ((c:ℝ)*rf)
      (Metric.ball ((c:ℂ)*z) ((c:ℝ)*r)) =
      (c:ℝ)^dimension κ*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z r) := by
  rw [←source_scale_ball c hc]
  simpa only [RegularSLEPresentation.sourceScaled,mul_left_comm (Real.sqrt κ) (c:ℝ)] using
    source_scale_spatialRealMass κ c hc (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (a.F ω) (a.witness ω) rf (Metric.ball z r)
end
end SLEExactGauge
end

 
section
open Set MeasureTheory
lemma source_tail_threshold_normalize {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (M C A b q K : ℝ)
    (hM : 0 < M) (hC : 0 < C) (_hA : 0 < A) (hb : 0 < b) (hq : 0 < q) (hK : 0 ≤ K)
    (hzero : μ {ω | 0 < X ω} ≤ ENNReal.ofReal (A*K))
    (ht : ∀ u : ℝ, 1 ≤ u → μ {ω | M*u < X ω} ≤ ENNReal.ofReal (C*K*Real.exp (-b*u^q)))
    (u : ℝ) (hu : 1 ≤ u) :
    μ {ω | u < X ω} ≤ ENNReal.ofReal
      ((max C A*Real.exp b)*K*Real.exp (-(b/(max M 1)^q)*u^q)) := by
  let R := max M 1
  have hR : 0 < R := hM.trans_le (le_max_left _ _)
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have he : -(b/R^q)*u^q = -b*(u/R)^q := by
    rw [Real.div_rpow hu0.le hR.le]
    ring
  rw [he]
  by_cases hbig : R ≤ u
  · have hv : 1 ≤ u/R := (le_div_iff₀ hR).mpr (by simpa using hbig)
    have hth : M*(u/R) ≤ u := by
      calc
        _ ≤ R*(u/R) := mul_le_mul_of_nonneg_right (le_max_left _ _) (div_nonneg hu0.le hR.le)
        _ = _ := by field_simp
    apply (measure_mono (show {ω | u < X ω} ⊆ {ω | M*(u/R) < X ω} from
      fun ω hω => hth.trans_lt hω)).trans (ht (u/R) hv |>.trans _)
    apply ENNReal.ofReal_le_ofReal
    gcongr
    calc
      C ≤ max C A := le_max_left _ _
      _ ≤ max C A*Real.exp b := le_mul_of_one_le_right (hC.le.trans (le_max_left _ _))
        (Real.one_le_exp_iff.mpr hb.le)
  · have hv : 0 ≤ u/R := div_nonneg hu0.le hR.le
    have hv1 : u/R ≤ 1 := (div_le_one hR).mpr (le_of_not_ge hbig)
    have hp : (u/R)^q ≤ 1 := Real.rpow_le_one hv hv1 hq.le
    have hexp : 1 ≤ Real.exp b*Real.exp (-b*(u/R)^q) := by
      rw [←Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      nlinarith
    apply (measure_mono (show {ω | u < X ω} ⊆ {ω | 0 < X ω} from
      fun ω hω => hu0.trans hω)).trans (hzero.trans _)
    apply ENNReal.ofReal_le_ofReal
    calc
      A*K ≤ max C A*K := mul_le_mul_of_nonneg_right (le_max_right _ _) hK
      _ ≤ (max C A*K)*(Real.exp b*Real.exp (-b*(u/R)^q)) :=
        le_mul_of_one_le_right (mul_nonneg (hC.le.trans (le_max_left _ _)) hK) hexp
      _ = _ := by ring
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_live_entrance_all_tail (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ),
    4 ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4)) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ 1 → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)} ≤
      ENNReal.ofReal (C*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ))) := by
  obtain ⟨M,C,b,hM,hC,hb,ht⟩ := sourceLiveEntranceTail_proved κ hκ hκ8
  let A := uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ
  have hk : 0 < κ := by linarith
  have hA : 0 < A := mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hk hκ8 zero_lt_one)
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨max C A*Real.exp b,b/(max M 1)^(2/codimension κ),
    mul_pos (hC.trans_le (le_max_left _ _)) (Real.exp_pos _),
    div_pos hb (Real.rpow_pos_of_pos (hM.trans_le (le_max_left _ _)) _),?_⟩
  intro Ω m P hP γ a z₀ hz hsmall rf u hf hf1 hu
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hK : 0 < initialGreen κ z₀ := initialGreen_pos κ z₀ (by change 0 < z₀.im; linarith)
  have hzero : μ {ω | 0 < X ω} ≤ ENNReal.ofReal (A*initialGreen κ z₀) := by
    apply le_trans (measure_mono (show {ω | 0 < X ω} ⊆
      {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤} from ?_))
    · apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (mul_pos hA hK).le).mpr
      exact source_live_entrance_bound a hk hκ8 z₀ hz hsmall
    · intro ω hω hn
      have hx : X ω = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro z hz'
        exact source_weight_zero_no_unit_entrance (a.witness ω) κ z₀ hz rf hf1 hn z hz'
      change 0 < X ω at hω
      rw [hx] at hω
      exact (lt_irrefl 0) hω
  exact source_tail_threshold_normalize μ X M C A b (2/codimension κ) (initialGreen κ z₀)
    hM hC hA hb (div_pos (by norm_num) (codimension_pos κ hκ8)) hK.le hzero
    (fun v hv => ht Ω m P hP γ a z₀ hz hsmall rf v hf hf1 hv) u hu
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section


theorem sourcePhysicalBallAllTail_proved : SourcePhysicalBallAllTailTarget := by
  intro κ hκ hκ8
  obtain ⟨C,b,hC,hb,ht⟩ := source_live_entrance_all_tail κ hκ hκ8
  refine ⟨C,b,hC,hb,?_⟩
  intro Ω m P hP γ a z r hr hz hsmall rf u hf hfr hu
  let : IsProbabilityMeasure P := hP
  let c : ℝ≥0 := ⟨r⁻¹,(inv_pos.mpr hr).le⟩
  have hc : 0 < c := inv_pos.mpr hr
  have hcR : (c:ℝ) = r⁻¹ := rfl
  let a' := a.sourceScaled c hc
  have him : ((c:ℂ)*z).im = r⁻¹*z.im := by simp [hcR,Complex.mul_im]
  have hcr : (c:ℝ)*r = 1 := by rw [hcR,inv_mul_cancel₀ hr.ne']
  have hheight : 4 ≤ ((c:ℂ)*z).im := by
    rw [him,mul_comm,←div_eq_mul_inv]
    exact (le_div_iff₀ hr).mpr hz
  have hsmall' : 1 ≤ Real.log ((2*((c:ℂ)*z).im)/((128*Real.pi)*4)) := by
    have he : (2*((c:ℂ)*z).im)/((128*Real.pi)*4) = (2*z.im)/((128*Real.pi)*(4*r)) := by
      rw [him]
      field_simp
    rwa [he]
  have hf' : 0 < (c:ℝ)*rf := mul_pos hc hf
  have hfr' : (c:ℝ)*rf ≤ 1 := by rw [←hcr]; exact mul_le_mul_of_nonneg_left hfr hc.le
  have htail := ht Ω m P hP (fun ω => sourceScaleTrace c (γ ω)) a' ((c:ℂ)*z)
    hheight hsmall' ((c:ℝ)*rf) u hf' hfr' hu
  change (P.comap (Subtype.val : a.samples → Ω)) {ω : a.samples | u < spatialRealMass κ
      (fun t => Real.sqrt κ*a'.B t ω) (sourceScaleTrace c (γ ω)) (a'.G ω)
      ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1)} ≤
      ENNReal.ofReal (C*initialGreen κ ((c:ℂ)*z)*Real.exp (-b*u^(2/codimension κ))) at htail
  have hp : 0 < (c:ℝ)^dimension κ := Real.rpow_pos_of_pos hc _
  have hrp : 0 < r^dimension κ := Real.rpow_pos_of_pos hr _
  have hmr : (c:ℝ)^dimension κ*(r^dimension κ*u) = u := by
    rw [hcR,Real.inv_rpow hr.le]
    field_simp
  have hx (ω : a.samples) : spatialRealMass κ (fun t => Real.sqrt κ*a'.B t ω)
      (sourceScaleTrace c (γ ω)) (a'.G ω) ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1) =
      (c:ℝ)^dimension κ*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z r) := by
    simpa only [hcr] using a.sourceScaled_mass c hc z r rf ω
  have he : {ω : a.samples | u < spatialRealMass κ (fun t => Real.sqrt κ*a'.B t ω)
      (sourceScaleTrace c (γ ω)) (a'.G ω) ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1)} =
      {ω : a.samples | r^dimension κ*u < spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) rf (ball z r)} := by
    ext ω
    change (u < _) ↔ _
    rw [hx ω]
    conv_lhs => rw [←hmr]
    exact mul_lt_mul_iff_right₀ hp
  rw [he] at htail
  have hg : initialGreen κ ((c:ℂ)*z) = r^codimension κ*initialGreen κ z := by
    rw [source_scale_initialGreen κ c hc z (by nlinarith),hcR,Real.inv_rpow hr.le,Real.rpow_neg hr.le,inv_inv]
  rw [hg] at htail
  convert htail using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring
end
end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RetainedDyadicGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained Dyadic Geometry for chordal SLE. -/


section
open Set Filter Metric Complex
open scoped Topology
namespace SLEExactGauge
noncomputable section
lemma source_dyadic_side_eq (k : ℕ) : (2:ℝ)^(-(k:ℝ)) = (1/2:ℝ)^k := by
  rw [Real.rpow_neg (by norm_num),Real.rpow_natCast,←inv_pow]
  norm_num
lemma source_dyadic_side_pos (k : ℕ) : 0 < (2:ℝ)^(-(k:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
lemma source_dyadic_side_le (k N : ℕ) (h : k ≤ N) : (2:ℝ)^(-(N:ℝ)) ≤ (2:ℝ)^(-(k:ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (Nat.cast_le.mpr h)
lemma source_square_subset_ball (k : ℕ) (ij : ℤ × ℤ) :
    retainedDyadicSquare k ij ⊆ ball (sourceDyadicCenter k ij) ((2:ℝ)^(-(k:ℝ))) := by
  let l := (2:ℝ)^(-(k:ℝ))
  have hl : 0 < l := source_dyadic_side_pos k
  have hinv : l*(2:ℝ)^k = 1 := by
    dsimp [l]
    rw [Real.rpow_neg (by norm_num),Real.rpow_natCast,inv_mul_cancel₀ (by positivity)]
  intro z ⟨hr1,hr2,hi1,hi2⟩
  have bound (j x : ℝ) (h1 : j ≤ (2:ℝ)^k*x) (h2 : (2:ℝ)^k*x < j+1) :
      (x-(j+1/2)*l)^2 ≤ (l/2)^2 := by
    have ha := mul_le_mul_of_nonneg_left h1 hl.le
    have hb := mul_lt_mul_of_pos_left h2 hl
    have he : l*((2:ℝ)^k*x) = x := by rw [←mul_assoc,hinv,one_mul]
    rw [he] at ha hb
    nlinarith [sq_nonneg (x-(j+1/2)*l+l/2),sq_nonneg (x-(j+1/2)*l-l/2),
      mul_nonneg (show 0 ≤ x-j*l by nlinarith) (show 0 ≤ (j+1)*l-x by nlinarith)]
  have hr := bound ij.1 z.re hr1 hr2
  have hi := bound ij.2 z.im hi1 hi2
  have hn := norm_nonneg (z-sourceDyadicCenter k ij)
  have hs : ‖z-sourceDyadicCenter k ij‖^2 =
      (z.re-((ij.1:ℝ)+1/2)*l)^2+(z.im-((ij.2:ℝ)+1/2)*l)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,sourceDyadicCenter,l,pow_two]
  rw [Metric.mem_ball,dist_eq_norm]
  change ‖z-sourceDyadicCenter k ij‖ < l
  nlinarith [sq_pos_of_pos hl]
lemma source_square_center_height (z₀ : ℂ) (k : ℕ) (ij : ℤ × ℤ)
    (hm : (closedBall z₀ 1 ∩ retainedDyadicSquare k ij).Nonempty) :
    z₀.im-2 ≤ (sourceDyadicCenter k ij).im := by
  obtain ⟨z,hzK,hzQ⟩ := hm
  have hd : dist z (sourceDyadicCenter k ij) < (2:ℝ)^(-(k:ℝ)) := source_square_subset_ball k ij hzQ
  have hs : (2:ℝ)^(-(k:ℝ)) ≤ 1 := by
    rw [source_dyadic_side_eq]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hK : dist z z₀ ≤ 1 := hzK
  have ha : abs (z.im-z₀.im) ≤ dist z z₀ := by
    simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
  have hb : abs (z.im-(sourceDyadicCenter k ij).im) ≤ dist z (sourceDyadicCenter k ij) := by
    simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-sourceDyadicCenter k ij)
  have := neg_abs_le (z.im-z₀.im)
  have := le_abs_self (z.im-(sourceDyadicCenter k ij).im)
  linarith
lemma source_small_dyadic_level (H : ℝ) (hH : 0 < H) :
    ∃ kmin : ℕ, ∀ k : ℕ, kmin ≤ k →
      4*(2:ℝ)^(-(k:ℝ)) ≤ H ∧
      Real.exp 1*((128*Real.pi)*(4*(2:ℝ)^(-(k:ℝ)))) ≤ 2*H := by
  have ht : Tendsto (fun k : ℕ => (2:ℝ)^(-(k:ℝ))) atTop (𝓝 0) := by
    simp_rw [source_dyadic_side_eq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : ∀ᶠ k : ℕ in atTop, (2:ℝ)^(-(k:ℝ)) <
      min (H/4) (H/(256*Real.pi*Real.exp 1)) :=
    ht.eventually (gt_mem_nhds (lt_min (by positivity) (by positivity)))
  obtain ⟨kmin,he⟩ := eventually_atTop.mp he
  refine ⟨kmin,fun k hk => ?_⟩
  have ha := (lt_min_iff.mp (he k hk)).1
  have hb := (lt_min_iff.mp (he k hk)).2
  constructor
  · linarith
  · have hh := (lt_div_iff₀ (by positivity : 0 < 256*Real.pi*Real.exp 1)).mp hb
    nlinarith
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_finite_mass_le_ball {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (z₀ : ℂ) (r rf : ℝ)
    (hr : 0 < r) (hy : 4*r ≤ z₀.im) (hf : 0 < rf) (hfr : rf ≤ r)
    (T : ℝ≥0) (K : Set ℂ) (hK : K ⊆ ball z₀ r) (ω : a.samples) :
    (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T K).toReal ≤
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ r) := by
  have hheight (z : ℂ) (hz : z ∈ ball z₀ r) : rf ≤ z.im := by
    have ha : abs (z.im-z₀.im) ≤ dist z z₀ := by
      simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
    have hb := neg_abs_le (z.im-z₀.im)
    have hd : dist z z₀ < r := hz
    linarith
  have hi := a.spatialGreenWeight_spatial_integrable hκ hκ8 rf hf (ball z₀ r)
    measurableSet_ball (measure_ball_lt_top (μ := volume) (x := z₀) (r := r)).ne hheight ω
  have hn (z : ℂ) : 0 ≤ spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z rf := by
    dsimp [spatialGreenWeight]; split_ifs
    · exact le_rfl
    · exact greenDensity_nonneg (a.witness ω) κ _ z
  have hbound : finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T K ≤
      ENNReal.ofReal (spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ r)) := by
    rw [spatialRealMass,ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)]
    apply (lintegral_mono_set hK).trans
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    split_ifs
    · exact le_rfl
    · exact hn z
  have hrn : 0 ≤ spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ r) :=
    integral_nonneg hn
  simpa only [ENNReal.toReal_ofReal hrn] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
end
end SLEExactGauge
end


end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SimpleTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simple Tails for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric



open Set Filter Metric Complex
open scoped Topology NNReal



open Set Filter Metric Complex
open scoped Topology NNReal



open Set Filter Metric Complex
open scoped Topology NNReal



open Set Filter
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators
namespace SLEExactGauge

lemma geometric_amplitude_sum (C r q α : ℝ) (hC : 0 ≤ C) (hr : 0 < r)
    (hq : 0 < q) (hq1 : q < 1) (hα : 0 < α) (N : ℕ) :
    ∑ n ∈ Finset.range N, C * (r*q^n)^α ≤ C*r^α / (1-q^α) := by
  have hs : q^α < 1 := Real.rpow_lt_one hq.le hq1 hα
  have he (n : ℕ) : C*(r*q^n)^α = C*r^α*(q^α)^n := by
    rw [Real.mul_rpow hr.le (pow_nonneg hq.le _), ← Real.rpow_pow_comm hq.le]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hgeom : ∑ n ∈ Finset.range N, (q^α)^n ≤ (1-q^α)⁻¹ := by
    rw [geom_sum_eq (ne_of_lt hs)]
    have hpos : 0 < 1-q^α := sub_pos.mpr hs
    rw [show ((q^α)^N-1)/(q^α-1) = (1-(q^α)^N)/(1-q^α) by rw [div_eq_div_iff (sub_ne_zero.mpr (ne_of_lt hs)) hpos.ne']; ring]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by have := pow_nonneg (Real.rpow_nonneg hq.le α) N; linarith) hpos.le
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hgeom
    (mul_nonneg hC (Real.rpow_nonneg hr.le _))

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma exists_exact_geometric_mesh {q δ ε : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hε : 0 < ε) (hεδ : ε ≤ δ) :
    ∃ (N : ℕ) (r : ℝ), q*δ < r ∧ r ≤ δ ∧ ε = r*q^N := by
  have hδ : 0 < δ := hε.trans_le hεδ
  obtain ⟨N, hN1, hN2⟩ := exists_nat_pow_near_of_lt_one (div_pos hε hδ)
    ((div_le_one hδ).mpr hεδ) hq hq1
  refine ⟨N, ε/q^N, ?_, ?_, ?_⟩
  · apply (lt_div_iff₀ (pow_pos hq N)).mpr
    have hh := (lt_div_iff₀ hδ).mp hN1
    rw [pow_succ] at hh
    nlinarith
  · apply (div_le_iff₀ (pow_pos hq N)).mpr
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hN2
  · field_simp

 

lemma mesh_tail_exponent {δ B p : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    -(δ^(-p))^2 / (2*(B*δ^(1-p))^2) = -(1/(2*B^2))*δ^(-2 : ℝ) := by
  have he : δ ^ (1-p) = δ*δ^(-p) := by
    rw [sub_eq_add_neg, Real.rpow_add hδ, Real.rpow_one]
  rw [he, show δ^(-2 : ℝ) = (δ^2)⁻¹ by rw [Real.rpow_neg hδ.le, Real.rpow_two]]
  have hp : δ^(-p) ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  field_simp [hδ.ne', hB.ne', hp]

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma meshTailAmplitude_pos {κ q : ℝ} (A : Set ℂ)
    (hκ : 0 < κ) (hq : 0 < q) (hq1 : q < 1) : 0 < meshTailAmplitude κ q A := by
  have hd : 0 < 1-q^(1-codimension κ) :=
    sub_pos.mpr (Real.rpow_lt_one hq.le hq1 (sub_pos.mpr (codimension_lt_one κ hκ)))
  have := div_nonneg (slabAmplitude_nonneg κ q A) hd.le
  dsimp [meshTailAmplitude]
  linarith

end SLEExactGauge

end
end

 
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SmallKappaSausageMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Kappa Sausage Moments for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology


section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_past_exponential_fatou
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (D : Set Ω) (hD : MeasurableSet D) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (θ V : ℝ) (hm : ∀ n, Measurable (X n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hexp : ∀ n, (∫⁻ ω, if ω ∈ D then ENNReal.ofReal
      (Real.exp (θ*X n ω-θ^2*V/2)) else 1 ∂P) ≤ 1) :
    (∫⁻ ω, if ω ∈ D then ENNReal.ofReal
      (Real.exp (θ*Y ω-θ^2*V/2)) else 1 ∂P) ≤ 1 := by
  let f (n : ℕ) (ω : Ω) := if ω ∈ D then
    ENNReal.ofReal (Real.exp (θ*X n ω-θ^2*V/2)) else 1
  have hfm (n : ℕ) : Measurable (f n) :=
    (((((hm n).const_mul θ).sub_const (θ^2*V/2)).exp).ennreal_ofReal).ite hD measurable_const
  have hl : ∀ᵐ ω ∂P, (if ω ∈ D then ENNReal.ofReal
      (Real.exp (θ*Y ω-θ^2*V/2)) else 1) = liminf (fun n => f n ω) atTop := by
    filter_upwards [hlim] with ω hω
    by_cases hmem : ω ∈ D
    · simp only [hmem, ↓reduceIte, f]
      exact ((ENNReal.continuous_ofReal.tendsto _).comp
        ((Real.continuous_exp.tendsto _).comp
          ((hω.const_mul θ).sub_const (θ^2*V/2)))).liminf_eq.symm
    · simp only [hmem, ↓reduceIte, f, liminf_const]
  calc
    _ = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P := lintegral_congr_ae hl
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' (fun n => (hfm n).aemeasurable)
    _ ≤ 1 := liminf_le_of_frequently_le (Frequently.of_forall hexp)
end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
lemma source_past_spatial_slab_terminal_exponential [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z ∈ A, (s : WithTop ℝ≥0) ≤ spatialHitTime (γ ω) z r)
    (θ : ℝ) :
    (∫⁻ ω in D, ENNReal.ofReal (Real.exp
      (θ*spatialSlabIncrement κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) A ε r - θ^2*slabVariance κ ε r A/2))
      ∂(P.comap Subtype.val)) ≤ (P.comap Subtype.val) D := by
  have hs : A ⊆ closedBall 0 R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hbound z hz
  have hfin : volume A ≠ ∞ := ne_of_lt
    ((measure_mono hs).trans_lt (isCompact_closedBall (0 : ℂ) R).measure_lt_top)
  obtain ⟨N,hN⟩ := exists_nat_ge s
  let X (n : ℕ) (ω : a.samples) := ∫ z in A,
    greenDensity κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε (n+N)) z -
    greenDensity κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r (n+N)) z
  let Y (ω : a.samples) := spatialSlabIncrement κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) A ε r
  have hXm (n : ℕ) : Measurable (X n) :=
    ((a.boundedSpatialGreen_measurable ε (n+N)).sub
      (a.boundedSpatialGreen_measurable r (n+N))).stronglyMeasurable.integral_prod_left'.measurable
  have hDm : MeasurableSet D := (a.filtration.le s) _ hD
  have hmask : (∫⁻ ω : a.samples, if ω ∈ D then ENNReal.ofReal
      (Real.exp (θ*Y ω-θ^2*slabVariance κ ε r A/2)) else 1 ∂P.comap Subtype.val) ≤ 1 := by
    apply source_past_exponential_fatou D hDm X Y θ (slabVariance κ ε r A) hXm
    · filter_upwards [a.spatial_slab_area_tendsto hκ (by linarith) A hA hfin ε r R hε hεr hrR hheight hbound] with ω hω
      simpa only [X, Y, spatialSlabIncrement, Function.comp_def, Nat.cast_add] using hω.comp (tendsto_add_atTop_nat N)
    · intro n
      apply a.source_past_spatial_slab_finite_exponential hκ hκ4 A hA ε r R hε hεr hrR hheight hbound (n+N) s D hD
      intro ω hω z
      apply WithTop.coe_le_coe.mp
      rw [boundedSpatialHit_coe]
      apply le_min (hbefore ω hω z z.2)
      exact WithTop.coe_le_coe.mpr (hN.trans (le_add_of_nonneg_left (by positivity)))
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let f (ω : a.samples) := ENNReal.ofReal (Real.exp (θ*Y ω-θ^2*slabVariance κ ε r A/2))
  change (∫⁻ ω, if ω ∈ D then f ω else 1 ∂μ) ≤ 1 at hmask
  rw [←lintegral_add_compl _ hDm] at hmask
  have hleft : (∫⁻ ω in D, if ω ∈ D then f ω else 1 ∂μ) = ∫⁻ ω in D, f ω ∂μ :=
    setLIntegral_congr_fun hDm (fun ω hω => ite_eq_left hω)
  have hright : (∫⁻ ω in Dᶜ, if ω ∈ D then f ω else 1 ∂μ) = μ Dᶜ := by
    rw [setLIntegral_congr_fun hDm.compl (fun ω hω => ite_eq_right hω)]
    simp
  rw [hleft,hright] at hmask
  have hsum : μ D+μ Dᶜ = 1 := by rw [measure_add_measure_compl hDm,measure_univ]
  exact (ENNReal.add_le_add_iff_right (measure_ne_top μ Dᶜ)).mp (hmask.trans_eq hsum.symm)
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_infinite_stopping_grid_piece
    {Ω : Type*} [m : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 m}
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ) (n k : ℕ) :
    MeasurableSet[ℱ (stopGridTime n k)]
      ({ω | ρ ω ≠ ⊤} ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) = k}) := by
  let A := {ω | ρ ω ≠ ⊤}
  have hle (j : ℕ) : MeasurableSet[ℱ (stopGridTime n j)]
      (A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) ≤ j}) := by
    convert hρ (stopGridTime n j) using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    cases he : ρ ω with
    | top => simp only [A,mem_inter_iff,mem_ofPred_eq,he,ne_eq,not_true_eq_false,false_and,WithTop.not_top_le_coe]
    | coe t => simp only [A,mem_inter_iff,mem_ofPred_eq,he,WithTop.coe_ne_top,ne_eq,not_false_eq_true,true_and,WithTop.untopD_coe,stopGridIndex_le,WithTop.coe_le_coe]
  cases k with
  | zero => simpa only [Nat.le_zero] using hle 0
  | succ k =>
    have he : A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) = k+1} =
        (A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) ≤ k+1}) \
          (A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) ≤ k}) := by
      ext ω
      simp only [mem_inter_iff,mem_ofPred_eq,Set.mem_sdiff]
      constructor
      · rintro ⟨hω,he⟩; exact ⟨⟨hω,he.le⟩,fun hn => by omega⟩
      · rintro ⟨⟨hω,hle⟩,hn⟩
        exact ⟨hω,by have hh : ¬stopGridIndex n ((ρ ω).untopD 0) ≤ k := fun hk => hn ⟨hω,hk⟩; omega⟩
    change MeasurableSet[ℱ (stopGridTime n (k+1))] (A ∩ _)
    rw [he]
    exact (hle (k+1)).diff (ℱ.mono (monotone_stopGridTime n (Nat.le_succ k)) _ (hle k))

 

lemma source_between_stopping_tail
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m} {ρ τ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime ℱ ρ) (hτ : IsStoppingTime ℱ τ)
    (H : Set Ω) (hH : MeasurableSet H)
    (hHA : H ⊆ {ω | ρ ω ≠ ⊤})
    (hsep : ∀ ω, ρ ω ≠ ⊤ → ρ ω < τ ω)
    (K : ℝ≥0∞)
    (ht : ∀ (s : ℝ≥0) (D : Set Ω), MeasurableSet[ℱ s] D →
      (∀ ω ∈ D, (s : WithTop ℝ≥0) ≤ τ ω) → μ (D ∩ H) ≤ μ D*K) :
    μ H ≤ μ {ω | ρ ω ≠ ⊤}*K := by
  let A := {ω | ρ ω ≠ ⊤}
  let Q (n k : ℕ) := A ∩ {ω | stopGridIndex n ((ρ ω).untopD 0) = k}
  let D (n k : ℕ) := Q n k ∩ {ω | (stopGridTime n k : WithTop ℝ≥0) < τ ω}
  let E (n : ℕ) := ⋃ k, D n k
  have hQ (n k : ℕ) : MeasurableSet[ℱ (stopGridTime n k)] (Q n k) :=
    source_infinite_stopping_grid_piece hρ n k
  have hD (n k : ℕ) : MeasurableSet[ℱ (stopGridTime n k)] (D n k) :=
    (hQ n k).inter (by simpa only [compl_ofPred,not_le] using (hτ (stopGridTime n k)).compl)
  have hDm (n k : ℕ) : MeasurableSet (D n k) := (ℱ.le _) _ (hD n k)
  have hEm (n : ℕ) : MeasurableSet (E n) := MeasurableSet.iUnion (hDm n)
  have hEq (n : ℕ) : ⋃ k, Q n k = A := grid_partition_union A n
  have hEd (n : ℕ) : Pairwise (fun i j => Disjoint (Q n i) (Q n j)) := grid_partition_disjoint A n
  have hb (n : ℕ) : μ (E n ∩ H) ≤ μ A*K := by
    calc
      μ (E n ∩ H) = μ (⋃ k, D n k ∩ H) := by simp only [E,iUnion_inter]
      _ ≤ ∑' k, μ (D n k ∩ H) := measure_iUnion_le _
      _ ≤ ∑' k, μ (Q n k)*K := ENNReal.tsum_le_tsum fun k =>
        (ht (stopGridTime n k) (D n k) (hD n k) (fun ω hω => hω.2.le)).trans
          (mul_le_mul' (measure_mono inter_subset_left) le_rfl)
      _ = (∑' k, μ (Q n k))*K := ENNReal.tsum_mul_right
      _ = μ A*K := by rw [←measure_iUnion (hEd n) (fun k => (ℱ.le _) _ (hQ n k)),hEq]
  have hevent (ω : Ω) (hω : ω ∈ A) : ∀ᶠ n in atTop, ω ∈ E n := by
    obtain ⟨t,ht'⟩ := WithTop.ne_top_iff_exists.mp hω
    have ht : ρ ω = (t : WithTop ℝ≥0) := ht'.symm
    have hlt := hsep ω hω
    rw [ht] at hlt
    have hgrid : ∀ᶠ n in atTop, (stopGrid n t : WithTop ℝ≥0) < τ ω := by
      cases hv : τ ω with
      | top => exact Eventually.of_forall fun n => WithTop.coe_lt_top _
      | coe v =>
        rw [hv] at hlt
        have hh : ∀ᶠ n in atTop, stopGrid n t < v := (stopGrid_tendsto t) (Iio_mem_nhds (WithTop.coe_lt_coe.mp hlt))
        exact hh.mono fun n hn => by simpa only [hv,WithTop.coe_lt_coe] using hn
    filter_upwards [hgrid] with n hn
    refine mem_iUnion.mpr ⟨stopGridIndex n t, ?_⟩
    exact ⟨⟨hω,by change stopGridIndex n ((ρ ω).untopD 0) = stopGridIndex n t; rw [ht]; rfl⟩,hn⟩
  let f (n : ℕ) := (E n ∩ H).indicator (fun _ : Ω => (1 : ℝ≥0∞))
  have hfm (n : ℕ) : Measurable (f n) := measurable_const.indicator ((hEm n).inter hH)
  have hp : H.indicator (fun _ : Ω => (1 : ℝ≥0∞)) ≤ fun ω => liminf (fun n => f n ω) atTop := by
    intro ω
    by_cases hω : ω ∈ H
    · rw [indicator_of_mem hω]
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [hevent ω (hHA hω)] with n hn
      simp only [f,indicator_of_mem (show ω ∈ E n ∩ H from ⟨hn,hω⟩),le_refl]
    · simp only [indicator_of_notMem hω]
      exact bot_le
  calc
    μ H = ∫⁻ ω, H.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by simp [hH]
    _ ≤ ∫⁻ ω, liminf (fun n => f n ω) atTop ∂μ := lintegral_mono hp
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂μ) atTop := lintegral_liminf_le' (fun n => (hfm n).aemeasurable)
    _ ≤ μ A*K := liminf_le_of_frequently_le (Frequently.of_forall fun n => by
      simpa only [f,lintegral_indicator ((hEm n).inter hH),lintegral_const,Measure.restrict_apply_univ,one_mul] using hb n)
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
lemma source_simple_sphere_stopping (z : ℂ) (r : ℝ) :
    IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r) := by
  let X (t : ℝ≥0) (ω : a.samples) := dist (γ ω t) z-r
  have ha : Adapted a.filtration X := by
    intro t
    let : MeasurableSpace a.samples := a.filtration t
    exact ((a.trace_adapted t).dist measurable_const).sub_const _
  exact continuous_zero_hit_stopping a.filtration X ha
    (fun ω => ((a.trace_continuous ω).dist continuous_const).sub continuous_const) 0
lemma source_simple_center_before (z₀ : ℂ) (hz : 4 ≤ z₀.im) (r : ℝ) (hr : r ≤ 1)
    (ω : a.samples) (z : ℂ) (hzz : z ∈ ball z₀ 1) :
    spatialHitTime (γ ω) z₀ 2 ≤ spatialHitTime (γ ω) z r := by
  by_cases hn : spatialHitTime (γ ω) z r = ⊤
  · rw [hn]; exact le_top
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  rw [←ht]
  have hm := spatialHitTime_mem (a.trace_continuous ω) z r t ht.symm
  have hs : 2 ≤ dist (γ ω 0) z₀ := by
    rw [(a.witness ω).2.1,dist_zero_left]
    have hh := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
    linarith
  apply (spatialHitTime_lt_of_dist_lt (a.trace_continuous ω) z₀ 2 hs t ?_).le
  have hh : dist z z₀ < 1 := hzz
  have ht' := dist_triangle (γ ω t) z z₀
  linarith
lemma source_simple_spheres_separated (z : ℂ) (hz : 4 ≤ z.im) (ω : a.samples)
    (hn : spatialHitTime (γ ω) z 3 ≠ ⊤) :
    spatialHitTime (γ ω) z 3 < spatialHitTime (γ ω) z 2 := by
  have hs : 3 ≤ dist (γ ω 0) z := by
    rw [(a.witness ω).2.1,dist_zero_left]
    have hh := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
    linarith
  apply lt_of_le_of_ne (spatialHitTime_antitone_radius (a.trace_continuous ω) z (by norm_num : (2:ℝ) ≤ 3) hs)
  intro he
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  have h3 := spatialHitTime_mem (a.trace_continuous ω) z 3 t ht.symm
  have h2 := spatialHitTime_mem (a.trace_continuous ω) z 2 t (he.symm.trans ht.symm)
  linarith
lemma source_simple_weight_zero_no_entrance (z₀ : ℂ) (hz : 4 ≤ z₀.im) (r : ℝ) (hr : r ≤ 1)
    (ω : a.samples) (hn : spatialHitTime (γ ω) z₀ 3 = ⊤) (z : ℂ) (hzz : z ∈ ball z₀ 1) :
    spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r = 0 := by
  unfold spatialGreenWeight
  split_ifs with hb
  · rfl
  · have hn' : spatialHitTime (γ ω) z r ≠ ⊤ := fun hh => hb hh
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn'
    have hm := spatialHitTime_mem (a.trace_continuous ω) z r t ht.symm
    have hs : 3 ≤ dist (γ ω 0) z₀ := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have hh := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
      linarith
    have hd : dist (γ ω t) z₀ < 3 := by
      have hh : dist z z₀ < 1 := hzz
      have ht' := dist_triangle (γ ω t) z z₀
      linarith
    have hh := spatialHitTime_lt_of_dist_lt (a.trace_continuous ω) z₀ 3 hs t hd
    rw [hn] at hh
    exact (not_lt_of_ge le_top hh).elim
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_past_spatial_slab_subgaussian [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (q ε r R : ℝ) (hq : 0 < q) (hε : 0 < ε) (hqr : q*r ≤ ε)
    (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z ∈ A, (s : WithTop ℝ≥0) ≤ spatialHitTime (γ ω) z r)
    :
    HasSubgaussianMGF (fun ω : a.samples => spatialSlabIncrement κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) A ε r)
      (⟨slabAmplitude κ q A * r ^ (1 - codimension κ),
        mul_nonneg (slabAmplitude_nonneg κ q A) (Real.rpow_nonneg (hε.trans_le hεr).le _)⟩ ^ 2)
      ((P.comap Subtype.val)[|D]) := by
  apply hasSubgaussianMGF_of_compensated (a.spatialSlabIncrement_measurable A ε r).aemeasurable
  intro θ
  rw [ProbabilityTheory.cond, lintegral_smul_measure]
  apply (mul_le_mul' (le_refl (((P.comap Subtype.val) D)⁻¹)) ?_).trans (ENNReal.inv_mul_le_one _)
  have hv := slabVariance_scale_le A hκ (by linarith) hq (hε.trans_le hεr) hqr
  apply le_trans _ (a.source_past_spatial_slab_terminal_exponential hκ hκ4 A hA ε r R hε hεr hrR hheight hbound s D hD hbefore θ)
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  change θ * _ - θ^2 * (slabAmplitude κ q A * r ^ (1 - codimension κ))^2 / 2 ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg θ)]

end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_past_spatial_geometric_subgaussian [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (A : Set ℂ) (hA : MeasurableSet A)
    (q r R : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R) (N : ℕ)
    (s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z ∈ A, (s : WithTop ℝ≥0) ≤ spatialHitTime (γ ω) z r)
    :
    HasSubgaussianMGF (fun ω : a.samples =>
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*q^N) A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A)
      (NNReal.mk (slabAmplitude κ q A*r^(1-codimension κ)/(1-q^(1-codimension κ)))
        (div_nonneg (mul_nonneg (slabAmplitude_nonneg κ q A) (Real.rpow_nonneg hr.le _))
          (sub_nonneg.mpr (Real.rpow_lt_one hq.le hq1 (sub_pos.mpr (codimension_lt_one κ hκ))).le)) ^ 2)
      ((P.comap Subtype.val)[|D]) := by
  let rj : ℕ → ℝ := fun n => r*q^n
  have hp (n : ℕ) : 0 < rj n := mul_pos hr (pow_pos hq n)
  have hl (n : ℕ) : rj n ≤ r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ (n := n) hq.le hq1.le) hr.le
  have he (n : ℕ) : rj (n+1) = q*rj n := by dsimp [rj]; rw [pow_succ]; ring
  let X : ℕ → a.samples → ℝ := fun n ω => spatialSlabIncrement κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) A (rj (n+1)) (rj n)
  let b : ℕ → ℝ≥0 := fun n => NNReal.mk (slabAmplitude κ q A*(rj n)^(1-codimension κ))
    (mul_nonneg (slabAmplitude_nonneg κ q A) (Real.rpow_nonneg (hp n).le _))
  have hsub (n : ℕ) : HasSubgaussianMGF (X n) (b n^2) ((P.comap Subtype.val)[|D]) := by
    apply a.source_past_spatial_slab_subgaussian hκ hκ4 A hA q (rj (n+1)) (rj n) R hq (hp _) (he n).symm.le (s := s) (D := D)
    · rw [he]; exact mul_le_of_le_one_left (hp n).le hq1.le
    · exact (hl n).trans hrR
    · exact fun z hz => (hl n).trans (hheight z hz)
    · exact hbound
    · exact hD
    · intro ω hω z hz
      apply (hbefore ω hω z hz).trans
      apply spatialHitTime_antitone_radius (a.trace_continuous ω) z (hl n)
      rw [(a.witness ω).2.1,dist_zero_left]
      exact (hheight z hz).trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have hsum := subgaussian_sum_amplitudes X b N (fun n _ => hsub n)
  have hfin : volume A ≠ ∞ := (measure_mono (show A ⊆ Metric.closedBall 0 R from
    fun z hz => by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound z hz)).trans_lt
      (measure_closedBall_lt_top (μ := volume) (x := (0 : ℂ)) (r := R)) |>.ne
  have htel (ω : a.samples) : (∑ n ∈ Finset.range N, X n ω) =
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*q^N) A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A := by
    have hm (n : ℕ) : X n ω =
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (rj (n+1)) A -
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (rj n) A := by
      symm
      apply a.spatialRealMass_sub_eq_slab hκ (by linarith) A hA hfin _ _ (hp _)
      · rw [he]; exact mul_le_of_le_one_left (hp n).le hq1.le
      · exact fun z hz => (hl n).trans (hheight z hz)
    simp_rw [hm]
    simpa only [rj, pow_zero, mul_one] using Finset.sum_range_sub
      (fun n => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (rj n) A) N
  simp_rw [htel] at hsum
  apply SLEExactGauge.HasSubgaussianMGF.mono_parameter hsum
  apply pow_le_pow_left₀ (by positivity)
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, b, rj, NNReal.coe_mk] using geometric_amplitude_sum (slabAmplitude κ q A) r q (1-codimension κ)
    (slabAmplitude_nonneg κ q A) hr hq hq1 (sub_pos.mpr (codimension_lt_one κ hκ)) N

end RegularSLEPresentation
end
end SLEExactGauge
end

 
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SimplePastMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simple Past Mesh for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_past_half_plane_mesh_tail [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (A : Set ℂ) (hA : MeasurableSet A)
    (q ε δ R : ℝ) (hq : 0 < q) (hq1 : q < 1) (hε : 0 < ε)
    (hεδ : ε ≤ δ) (hδR : δ ≤ R)
    (hheight : ∀ z ∈ A, δ ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z ∈ A, (s : WithTop ℝ≥0) ≤ spatialHitTime (γ ω) z δ)
    :
    ((P.comap Subtype.val)[|D]) {ω : a.samples |
      ((volume A).toReal*q^(-codimension κ)+1)*δ^(-codimension κ) ≤
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A} ≤
      ENNReal.ofReal (Real.exp (-(1/(2*(meshTailAmplitude κ q A)^2))*δ^(-2 : ℝ))) := by
  obtain ⟨N,r, hqr, hrδ, he⟩ := exists_exact_geometric_mesh hq hq1 hε hεδ
  have hδ : 0 < δ := hε.trans_le hεδ
  have hr : 0 < r := (mul_pos hq hδ).trans hqr
  have hκ8 : κ < 8 := by linarith
  have hp : 0 < codimension κ := codimension_pos κ hκ8
  have hα : 0 < 1-codimension κ := sub_pos.mpr (codimension_lt_one κ hκ)
  have hd : 0 < 1-q^(1-codimension κ) := sub_pos.mpr (Real.rpow_lt_one hq.le hq1 hα)
  have hB := meshTailAmplitude_pos A hκ hq hq1
  have ham : slabAmplitude κ q A*r^(1-codimension κ)/(1-q^(1-codimension κ)) ≤
      meshTailAmplitude κ q A*δ^(1-codimension κ) := by
    calc
      _ ≤ slabAmplitude κ q A*δ^(1-codimension κ)/(1-q^(1-codimension κ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hr.le hrδ hα.le) (slabAmplitude_nonneg κ q A)) hd.le
      _ ≤ _ := by
        dsimp [meshTailAmplitude]
        have hx := (Real.rpow_pos_of_pos hδ (1-codimension κ)).le
        rw [add_mul, div_mul_eq_mul_div]
        nlinarith
  let B : ℝ≥0 := NNReal.mk (meshTailAmplitude κ q A*δ^(1-codimension κ))
    (mul_nonneg hB.le (Real.rpow_nonneg hδ.le _))
  have hsg := a.source_past_spatial_geometric_subgaussian hκ hκ4 A hA q r R hq hq1 hr
    (hrδ.trans hδR) (fun z hz => hrδ.trans (hheight z hz)) hbound N s D hD (fun ω hω z hz => (hbefore ω hω z hz).trans
      (spatialHitTime_antitone_radius (a.trace_continuous ω) z hrδ (by
        rw [(a.witness ω).2.1,dist_zero_left]
        exact (hheight z hz).trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)))))
  have hsg' : HasSubgaussianMGF (fun ω : a.samples =>
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A)
      (B^2) ((P.comap Subtype.val)[|D]) := by
    rw [he]
    apply SLEExactGauge.HasSubgaussianMGF.mono_parameter hsg
    apply pow_le_pow_left₀ (by positivity)
    exact NNReal.coe_le_coe.mp ham
  have hfin : volume A ≠ ∞ := (measure_mono (show A ⊆ closedBall 0 R from
    fun z hz => by simpa only [mem_closedBall, dist_zero_right] using hbound z hz)).trans_lt
      (measure_closedBall_lt_top (μ := volume) (x := (0 : ℂ)) (r := R)) |>.ne
  have hstart (ω : a.samples) :
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A ≤
      (volume A).toReal*q^(-codimension κ)*δ^(-codimension κ) := by
    apply (a.spatialRealMass_bound hκ hκ8 r hr A hA hfin
      (fun z hz => hrδ.trans (hheight z hz)) ω).2.trans
    have hh := Real.rpow_le_rpow_of_nonpos (mul_pos hq hδ) hqr.le (neg_nonpos.mpr hp.le)
    rw [Real.mul_rpow hq.le hδ.le] at hh
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh ENNReal.toReal_nonneg
  apply (measure_mono (show _ ⊆ {ω : a.samples | δ^(-codimension κ) ≤
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A} from ?_)).trans
  · apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
    have ht := hsg'.measure_ge_le (Real.rpow_nonneg hδ.le (-codimension κ))
    change ((P.comap Subtype.val)[|D]).real _ ≤ _
    simpa only [B, NNReal.coe_pow, NNReal.coe_mk, mesh_tail_exponent hδ hB] using ht
  · intro ω hω
    have := hstart ω
    change ((volume A).toReal*q^(-codimension κ)+1)*δ^(-codimension κ) ≤
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A at hω
    change δ^(-codimension κ) ≤
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A
    nlinarith

end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section


theorem sourceSimpleEntranceMesh_proved : SourceSimpleEntranceMeshTarget := by
  intro κ hκ hκ4
  let C := max 1 ((volume (ball (0:ℂ) 1)).toReal*(1/2:ℝ)^(-codimension κ)+1)
  let c := 1/(2*(meshTailAmplitude κ (1/2) (ball (0:ℂ) 1))^2)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hc : 0 < c := by
    have hh := meshTailAmplitude_pos (κ := κ) (q := (1/2:ℝ)) (ball (0:ℂ) 1) hκ (by norm_num) (by norm_num)
    exact div_pos zero_lt_one (mul_pos (by norm_num) (sq_pos_of_pos hh))
  refine ⟨C,c,1/2,hC,hc,by norm_num,by norm_num,?_⟩
  intro Ω m P hP γ a z₀ hz₀ rf δ hf hfd hd
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let H := {ω : a.samples | C*δ^(-codimension κ) < spatialRealMass κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)}
  have hH : MeasurableSet H := measurableSet_lt measurable_const (a.spatialRealMass_measurable _ _)
  have hδ : 0 < δ := hf.trans_le hfd
  have hδ1 : δ ≤ 1 := hd.trans (by norm_num)
  have hrf1 : rf ≤ 1 := hfd.trans hδ1
  have hHA : H ⊆ {ω | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} := by
    intro ω hω hn
    have hm : spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1) = 0 := by
      unfold spatialRealMass
      apply setIntegral_eq_zero_of_forall_eq_zero
      exact fun z hz => a.source_simple_weight_zero_no_entrance z₀ hz₀ rf hrf1 ω hn z hz
    change C*δ^(-codimension κ) < _ at hω
    rw [hm] at hω
    exact (not_lt_of_ge (mul_nonneg hC.le (Real.rpow_nonneg hδ.le _))) hω
  apply source_between_stopping_tail (a.source_simple_sphere_stopping z₀ 3)
    (a.source_simple_sphere_stopping z₀ 2) H hH hHA
    (a.source_simple_spheres_separated z₀ hz₀) (ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ))))
  intro s D hD hbefore
  have hDm : MeasurableSet D := (a.filtration.le s) _ hD
  have hheight : ∀ z ∈ ball z₀ 1, δ ≤ z.im := by
    intro z hz
    have he := (le_abs_self (z₀.im-z.im)).trans (Complex.abs_im_le_norm (z₀-z))
    have hn : ‖z₀-z‖ < 1 := by simpa only [mem_ball,dist_eq_norm, norm_sub_rev] using hz
    linarith
  have hbound : ∀ z ∈ ball z₀ 1, ‖z‖ ≤ ‖z₀‖+1 := by
    intro z hz
    have hh := norm_le_insert z₀ z
    rw [norm_sub_rev z₀ z] at hh
    have hn : ‖z-z₀‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hz
    linarith
  have hR : δ ≤ ‖z₀‖+1 := hδ1.trans (by linarith [norm_nonneg z₀])
  have ht := a.source_past_half_plane_mesh_tail hκ hκ4 (ball z₀ 1) measurableSet_ball
    (1/2) rf δ (‖z₀‖+1) (by norm_num) (by norm_num) hf hfd hR hheight hbound s D hD
    (fun ω hω z hz => (hbefore ω hω).trans (a.source_simple_center_before z₀ hz₀ δ hδ1 ω z hz))
  have hv : volume (ball z₀ 1) = volume (ball (0:ℂ) 1) := by rw [Complex.volume_ball,Complex.volume_ball]
  have ha : meshTailAmplitude κ (1/2) (ball z₀ 1) = meshTailAmplitude κ (1/2) (ball (0:ℂ) 1) := by
    simp only [meshTailAmplitude,slabAmplitude,hv]
  have hcoeff : (volume (ball z₀ 1)).toReal*(1/2:ℝ)^(-codimension κ)+1 ≤ C := by
    rw [hv]; exact le_max_right _ _
  have ht' : μ[H|D] ≤ ENNReal.ofReal (Real.exp (-c*δ^(-2:ℝ))) := by
    apply (measure_mono (show H ⊆ _ from ?_)).trans
    · simpa only [ha] using ht
    · intro ω hω
      exact (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hδ.le _)).trans hω.le
  calc
    μ (D ∩ H) = μ[H|D]*μ D := (cond_mul_eq_inter hDm H μ).symm
    _ ≤ ENNReal.ofReal (Real.exp (-c*δ^(-2:ℝ)))*μ D := mul_le_mul' ht' le_rfl
    _ ≤ μ D*ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ))) := by
      rw [mul_comm]
      apply mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
      exact le_mul_of_one_le_left (Real.exp_pos _).le hC1
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_simple_entrance_bound {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 4 ≤ z₀.im) (hsmall : 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4))) :
    (P.comap Subtype.val).real {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} ≤
      (uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ)*initialGreen κ z₀ := by
  apply le_trans (measureReal_mono (show {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} ⊆
      {ω | ∃ t : ℝ≥0, dist (γ ω t) z₀ < 4} from ?_))
  · have hh := euclidean_approach a.brownian κ hκ hκ8 (fun ω : a.samples => γ ω) a.G a.F
      (Eventually.of_forall a.witness) z₀ (by change 0 < z₀.im; linarith) 4 (by norm_num) hz hsmall
    change ((P.comap Subtype.val) {ω : a.samples | ∃ t : ℝ≥0, dist (γ ω t) z₀ < 4}).toReal ≤ _
    calc
      _ ≤ _ := hh
      _ = _ := by ring
  · intro ω hω
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hω
    have hs : 3 ≤ dist (γ ω 0) z₀ := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
      linarith
    exact ⟨t,by rw [spatialHitTime_mem (a.trace_continuous ω) z₀ 3 t ht.symm]; norm_num⟩
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
theorem sourceSimpleStretchedTail_proved : SourceSimpleStretchedTailTarget := by
  intro κ hκ hκ4
  have hκ8 : κ < 8 := by linarith
  obtain ⟨C,c,δ₀,hC,hc,hδ,hδ1,ht⟩ := sourceSimpleEntranceMesh_proved κ hκ hκ4
  let v := (volume (ball (0:ℂ) 1)).toReal
  let M := max C v*δ₀^(-codimension κ)
  let b := c*δ₀^(-2:ℝ)
  let A := uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ
  have hk : 0 < κ := by linarith
  have hp : 0 < codimension κ := codimension_pos κ hκ8
  have hM : 0 < M := mul_pos (hC.trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos hδ _)
  have hb : 0 < b := mul_pos hc (Real.rpow_pos_of_pos hδ _)
  have hA : 0 < A := mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hk hκ8 zero_lt_one)
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨M,A*C,b,hM,mul_pos hA hC,hb,?_⟩
  intro Ω m P hP γ a z₀ hz hsmall rf u hf hf1 hu
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hx (ω : a.samples) : X ω ≤ v*rf^(-codimension κ) := by
    have hh := (a.spatialRealMass_bound hk hκ8 rf hf (ball z₀ 1) measurableSet_ball
      (measure_ball_lt_top (μ := volume) (x := z₀) (r := 1)).ne (fun z hz' => ?_) ω).2
    · simpa only [v,Complex.volume_ball] using hh
    · have hd : abs (z.im-z₀.im) ≤ dist z z₀ := by
        simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
      have hh : dist z z₀ < 1 := hz'
      have ha := neg_abs_le (z.im-z₀.im)
      linarith
  have ht' := source_mesh_tail_to_stretched μ X (codimension κ) C c δ₀ v rf
    (μ.real {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤}) hp hC hc hδ
    ENNReal.toReal_nonneg hf ENNReal.toReal_nonneg hx
    (fun δ hfd hd => by
      have hh := ht Ω m P hP γ a z₀ hz rf δ hf hfd hd
      simpa only [Measure.real, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh) u hu
  apply ht'.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (A*initialGreen κ z₀)*C*Real.exp (-b*u^(2/codimension κ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (source_simple_entrance_bound a hk hκ8 z₀ hz hsmall) hC.le) (Real.exp_pos _).le
    _ = _ := by ring
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_simple_entrance_all_tail (κ : ℝ) (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ),
    4 ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4)) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ 1 → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)} ≤
      ENNReal.ofReal (C*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ))) := by
  have hκ8 : κ < 8 := by linarith
  obtain ⟨M,C,b,hM,hC,hb,ht⟩ := sourceSimpleStretchedTail_proved κ hκ hκ4
  let A := uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ
  have hk : 0 < κ := by linarith
  have hA : 0 < A := mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hk hκ8 zero_lt_one)
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨max C A*Real.exp b,b/(max M 1)^(2/codimension κ),
    mul_pos (hC.trans_le (le_max_left _ _)) (Real.exp_pos _),
    div_pos hb (Real.rpow_pos_of_pos (hM.trans_le (le_max_left _ _)) _),?_⟩
  intro Ω m P hP γ a z₀ hz hsmall rf u hf hf1 hu
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hK : 0 < initialGreen κ z₀ := initialGreen_pos κ z₀ (by change 0 < z₀.im; linarith)
  have hzero : μ {ω | 0 < X ω} ≤ ENNReal.ofReal (A*initialGreen κ z₀) := by
    apply le_trans (measure_mono (show {ω | 0 < X ω} ⊆
      {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} from ?_))
    · apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (mul_pos hA hK).le).mpr
      exact source_simple_entrance_bound a hk hκ8 z₀ hz hsmall
    · intro ω hω hn
      have hx : X ω = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro z hz'
        exact a.source_simple_weight_zero_no_entrance z₀ hz rf hf1 ω hn z hz'
      change 0 < X ω at hω
      rw [hx] at hω
      exact (lt_irrefl 0) hω
  exact source_tail_threshold_normalize μ X M C A b (2/codimension κ) (initialGreen κ z₀)
    hM hC hA hb (div_pos (by norm_num) (codimension_pos κ hκ8)) hK.le hzero
    (fun v hv => ht Ω m P hP γ a z₀ hz hsmall rf v hf hf1 hv) u hu
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section


theorem sourceSimplePhysicalBallAllTail_proved : SourceSimplePhysicalBallAllTailTarget := by
  intro κ hκ hκ4
  have hκ8 : κ < 8 := by linarith
  obtain ⟨C,b,hC,hb,ht⟩ := source_simple_entrance_all_tail κ hκ hκ4
  refine ⟨C,b,hC,hb,?_⟩
  intro Ω m P hP γ a z r hr hz hsmall rf u hf hfr hu
  let : IsProbabilityMeasure P := hP
  let c : ℝ≥0 := ⟨r⁻¹,(inv_pos.mpr hr).le⟩
  have hc : 0 < c := inv_pos.mpr hr
  have hcR : (c:ℝ) = r⁻¹ := rfl
  let a' := a.sourceScaled c hc
  have him : ((c:ℂ)*z).im = r⁻¹*z.im := by simp [hcR,Complex.mul_im]
  have hcr : (c:ℝ)*r = 1 := by rw [hcR,inv_mul_cancel₀ hr.ne']
  have hheight : 4 ≤ ((c:ℂ)*z).im := by
    rw [him,mul_comm,←div_eq_mul_inv]
    exact (le_div_iff₀ hr).mpr hz
  have hsmall' : 1 ≤ Real.log ((2*((c:ℂ)*z).im)/((128*Real.pi)*4)) := by
    have he : (2*((c:ℂ)*z).im)/((128*Real.pi)*4) = (2*z.im)/((128*Real.pi)*(4*r)) := by
      rw [him]
      field_simp
    rwa [he]
  have hf' : 0 < (c:ℝ)*rf := mul_pos hc hf
  have hfr' : (c:ℝ)*rf ≤ 1 := by rw [←hcr]; exact mul_le_mul_of_nonneg_left hfr hc.le
  have htail := ht Ω m P hP (fun ω => sourceScaleTrace c (γ ω)) a' ((c:ℂ)*z)
    hheight hsmall' ((c:ℝ)*rf) u hf' hfr' hu
  change (P.comap (Subtype.val : a.samples → Ω)) {ω : a.samples | u < spatialRealMass κ
      (fun t => Real.sqrt κ*a'.B t ω) (sourceScaleTrace c (γ ω)) (a'.G ω)
      ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1)} ≤
      ENNReal.ofReal (C*initialGreen κ ((c:ℂ)*z)*Real.exp (-b*u^(2/codimension κ))) at htail
  have hp : 0 < (c:ℝ)^dimension κ := Real.rpow_pos_of_pos hc _
  have hrp : 0 < r^dimension κ := Real.rpow_pos_of_pos hr _
  have hmr : (c:ℝ)^dimension κ*(r^dimension κ*u) = u := by
    rw [hcR,Real.inv_rpow hr.le]
    field_simp
  have hx (ω : a.samples) : spatialRealMass κ (fun t => Real.sqrt κ*a'.B t ω)
      (sourceScaleTrace c (γ ω)) (a'.G ω) ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1) =
      (c:ℝ)^dimension κ*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z r) := by
    simpa only [hcr] using a.sourceScaled_mass c hc z r rf ω
  have he : {ω : a.samples | u < spatialRealMass κ (fun t => Real.sqrt κ*a'.B t ω)
      (sourceScaleTrace c (γ ω)) (a'.G ω) ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1)} =
      {ω : a.samples | r^dimension κ*u < spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) rf (ball z r)} := by
    ext ω
    change (u < _) ↔ _
    rw [hx ω]
    conv_lhs => rw [←hmr]
    exact mul_lt_mul_iff_right₀ hp
  rw [he] at htail
  have hg : initialGreen κ ((c:ℂ)*z) = r^codimension κ*initialGreen κ z := by
    rw [source_scale_initialGreen κ c hc z (by nlinarith),hcR,Real.inv_rpow hr.le,Real.rpow_neg hr.le,inv_inv]
  rw [hg] at htail
  convert htail using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
theorem sourcePhysicalBallEveryKappa_proved : SourcePhysicalBallEveryKappaTarget := by
  intro κ hκ hκ8
  by_cases hκ4 : κ ≤ 4
  · exact sourceSimplePhysicalBallAllTail_proved κ hκ hκ4
  · exact sourcePhysicalBallAllTail_proved κ (lt_of_not_ge hκ4) hκ8
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section


theorem sourceActualSquareTail_proved_allKappa_oai : SourceActualSquareTailTarget_allKappa := by
  intro κ hκ hκ8 Ω m P hP γ a z₀ hz₀
  obtain ⟨C,c,hC,hc,ht⟩ := sourcePhysicalBallEveryKappa_proved κ hκ hκ8
  let H := z₀.im-2
  have hH : 0 < H := sub_pos.mpr hz₀
  let G := (2:ℝ)^(-codimension κ)*H^(-codimension κ)
  have hG : 0 < G := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hH _)
  obtain ⟨kmin,hkmin⟩ := source_small_dyadic_level H hH
  refine ⟨C*G,c,kmin,mul_pos hC hG,hc,?_⟩
  intro T N k hk hkN ij u hu
  let l := (2:ℝ)^(-(k:ℝ))
  let rf := (2:ℝ)^(-(N:ℝ))
  have hl : 0 < l := source_dyadic_side_pos k
  have hf : 0 < rf := source_dyadic_side_pos N
  have hfl : rf ≤ l := source_dyadic_side_le k N hkN
  have hpos : 0 < l^dimension κ*u := mul_pos (Real.rpow_pos_of_pos hl _) (zero_lt_one.trans_le hu)
  by_cases hmeet : (closedBall z₀ 1 ∩ retainedDyadicSquare k ij).Nonempty
  · let z := sourceDyadicCenter k ij
    have hheight : H ≤ z.im := source_square_center_height z₀ k ij hmeet
    have hy : 4*l ≤ z.im := (hkmin k hk).1.trans hheight
    have hsmall : 1 ≤ Real.log ((2*z.im)/((128*Real.pi)*(4*l))) := by
      apply (Real.le_log_iff_exp_le (div_pos (by linarith) (by positivity))).mpr
      apply (le_div_iff₀ (by positivity : 0 < (128*Real.pi)*(4*l))).mpr
      exact (hkmin k hk).2.trans (mul_le_mul_of_nonneg_left hheight (by norm_num))
    have hgreen : initialGreen κ z ≤ G := by
      apply (initialGreen_le_height κ (by linarith) hκ8 z (hH.trans_le hheight)).trans
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      exact Real.rpow_le_rpow_of_nonpos hH hheight (neg_nonpos.mpr (codimension_pos κ hκ8).le)
    have hh := ht Ω m P hP γ a z l hl hy hsmall rf u hf hfl hu
    apply le_trans (measure_mono (show {ω : a.samples | l^dimension κ*u <
      (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T
        (closedBall z₀ 1 ∩ retainedDyadicSquare k ij)).toReal} ⊆
      {ω | l^dimension κ*u < spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) rf (ball z l)} from ?_)) (hh.trans ?_)
    · intro ω hω
      exact hω.trans_le (source_finite_mass_le_ball a (by linarith) hκ8 z l rf hl hy hf hfl T
        _ (fun w hw => source_square_subset_ball k ij hw.2) ω)
    · apply ENNReal.ofReal_le_ofReal
      calc
        C*l^codimension κ*initialGreen κ z*Real.exp (-c*u^(2/codimension κ)) ≤
            C*l^codimension κ*G*Real.exp (-c*u^(2/codimension κ)) := by gcongr
        _ = _ := by ring
  · have he : closedBall z₀ 1 ∩ retainedDyadicSquare k ij = ∅ := not_nonempty_iff_eq_empty.mp hmeet
    have hempty : {ω : a.samples | l^dimension κ*u <
      (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T
        (closedBall z₀ 1 ∩ retainedDyadicSquare k ij)).toReal} = ∅ := by
      simp only [he,finiteSpatialGreenMass,Measure.restrict_empty,lintegral_zero_measure,ENNReal.toReal_zero,
        not_lt_of_ge hpos.le,Set.ofPred_false]
    change (P.comap Subtype.val) _ ≤ _
    rw [hempty,measure_empty]
    exact bot_le
end
end SLEExactGauge
end


end
end
end

end OAI
end

theorem solution : type_of% @OAI.SLEExactGauge.sourceActualSquareTail_proved_allKappa_oai := @OAI.SLEExactGauge.sourceActualSquareTail_proved_allKappa_oai
