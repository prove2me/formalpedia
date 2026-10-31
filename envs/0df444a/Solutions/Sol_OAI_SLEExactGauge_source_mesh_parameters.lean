-- Prove2me | solution 1 for OAI.SLEExactGauge.source_mesh_parameters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:48:57.027556+00:00
-- url     : https://prove2.me/submissions/4670090f-3189-4251-9033-feb8ad455c4e

import Mathlib
import Definitions.Def_SLELowerPositivity
import Definitions.Def_OAIQ27Sle000
import Theorems.Thm_OAI_SLEExactGauge_source_interior_disk_unnormalized

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

 

lemma stopping_grid_piece_measurable
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (n k : ℕ) :
    MeasurableSet[ℱ (stopGridTime n k)] (A ∩ {ω | stopGridIndex n (τ ω) = k}) := by
  have hle (j : ℕ) : MeasurableSet[ℱ (stopGridTime n j)]
      (A ∩ {ω | stopGridIndex n (τ ω) ≤ j}) := by
    simpa only [stopGridIndex_le, WithTop.coe_le_coe] using hA.2 (stopGridTime n j)
  cases k with
  | zero => simpa only [Nat.le_zero] using hle 0
  | succ k =>
    have he : A ∩ {ω | stopGridIndex n (τ ω) = k + 1} =
        (A ∩ {ω | stopGridIndex n (τ ω) ≤ k + 1}) \ (A ∩ {ω | stopGridIndex n (τ ω) ≤ k}) := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff]
      constructor
      · rintro ⟨hω, heq⟩
        exact ⟨⟨hω, heq.le⟩, fun hb => by omega⟩
      · rintro ⟨⟨hω, hle⟩, hn⟩
        exact ⟨hω, by have hh : ¬ stopGridIndex n (τ ω) ≤ k := fun hk => hn ⟨hω, hk⟩; omega⟩
    rw [he]
    exact (hle (k + 1)).diff (ℱ.mono (monotone_stopGridTime n (Nat.le_succ k)) _ (hle k))

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

 

lemma integral_stopping_grid_glue [IsFiniteMeasure P]
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (n : ℕ)
    (f : Ω → ℝ) (hf : Integrable f P) (c : ℝ)
    (hpiece : ∀ k : ℕ, (∫ ω in A ∩ {ω | stopGridIndex n (τ ω) = k}, f ω ∂P) =
      P.real (A ∩ {ω | stopGridIndex n (τ ω) = k}) * c) :
    (∫ ω in A, f ω ∂P) = P.real A * c := by
  have hm (k : ℕ) : MeasurableSet (A ∩ {ω | stopGridIndex n (τ ω) = k}) :=
    ℱ.le _ _ (stopping_grid_piece_measurable hτ hA n k)
  have hfSum := hasSum_integral_iUnion hm (grid_partition_disjoint (τ := τ) A n) hf.integrableOn
  have hconstSum := hasSum_integral_iUnion hm (grid_partition_disjoint (τ := τ) A n)
    (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P).integrableOn
  simp only [grid_partition_union, hpiece] at hfSum
  simp only [grid_partition_union, integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] at hconstSum
  exact HasSum.unique hfSum (hconstSum.mul_right c)

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

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))

include hm in
lemma shiftedFDD_measurable (I : Finset ℝ≥0) (s : ℝ≥0) :
    Measurable (shiftedFDD B I s) :=
  Measurable.of_eval (fun i => (hm (s + i)).sub (hm s))

include hB hm in
omit [IsProbabilityMeasure P] in
lemma shiftedFDD_indep (I : Finset ℝ≥0) (s : ℝ≥0) :
    Indep (Filtration.natural B (fun t => (hm t).stronglyMeasurable) s)
      (MeasurableSpace.comap (shiftedFDD B I s) inferInstance) P := by
  have hi := ((hB.indepFun_shift s).comp
    (Measurable.of_eval (fun i : I => measurable_pi_apply (i : ℝ≥0))) measurable_id).symm
  rw [Filtration.natural_eq_comap B _ s]
  exact (IndepFun_iff_Indep _ _ _).mp hi

include hB hm in
omit [IsProbabilityMeasure P] in
lemma shiftedFDD_setIntegral (I : Finset ℝ≥0) (s : ℝ≥0)
    (φ : BoundedContinuousFunction (I → ℝ) ℝ) {A : Set Ω}
    (hA : MeasurableSet[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] A) :
    (∫ ω in A, φ (shiftedFDD B I s ω) ∂P) =
      P.real A * ∫ x, φ x ∂BrownianReal.projectiveFamily I := by
  rw [(shiftedFDD_indep hB hm I s).setIntegral_eq_mul
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s)
    (shiftedFDD_measurable hm I s).aemeasurable hA φ.continuous.aestronglyMeasurable]
  congr 1
  exact ((hB.shift s).hasLaw I).integral_comp φ.continuous.aestronglyMeasurable

include hm in
lemma shiftedFDD_grid_measurable {τ : Ω → ℝ≥0} (hτm : Measurable τ)
    (I : Finset ℝ≥0) (n : ℕ) :
    Measurable (fun ω => shiftedFDD B I (stopGrid n (τ ω)) ω) := by
  apply Measurable.of_eval
  intro i
  exact measurable_discrete_eval
    (fun k ω => B (stopGridTime n k + i) ω - B (stopGridTime n k) ω)
    (fun k => (hm _).sub (hm _)) (stopGridIndex_measurable hτm n)

include hB hm in
lemma shiftedFDD_grid_setIntegral {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (I : Finset ℝ≥0) (φ : BoundedContinuousFunction (I → ℝ) ℝ) (n : ℕ) :
    (∫ ω in A, φ (shiftedFDD B I (stopGrid n (τ ω)) ω) ∂P) =
      P.real A * ∫ x, φ x ∂BrownianReal.projectiveFamily I := by
  apply integral_stopping_grid_glue hτ hA n _
    (Integrable.of_bound (φ.continuous.measurable.comp
      (shiftedFDD_grid_measurable hm (stopping_time_measurable_nnreal hτ) I n)).aestronglyMeasurable
      ‖φ‖ (Eventually.of_forall (fun ω => φ.norm_coe_le_norm _)))
  intro k
  have hk := stopping_grid_piece_measurable hτ hA n k
  have hk' := (Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le _ _ hk
  rw [setIntegral_congr_fun hk' (g := fun ω => φ (shiftedFDD B I (stopGridTime n k) ω))
    (fun ω hω => by
      have he : stopGridIndex n (τ ω) = k := hω.2
      simp only [Function.comp_def, stopGrid, he])]
  exact shiftedFDD_setIntegral hB hm I _ φ hk

omit mΩ in
lemma shiftedFDD_grid_tendsto
    (hc : ∀ ω, Continuous (fun t => B t ω)) (I : Finset ℝ≥0) (τ : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n => shiftedFDD B I (stopGrid n (τ ω)) ω) atTop
      (𝓝 (shiftedFDD B I (τ ω) ω)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact ((hc ω).continuousAt.tendsto.comp ((stopGrid_tendsto (τ ω)).add_const (i : ℝ≥0))).sub
    ((hc ω).continuousAt.tendsto.comp (stopGrid_tendsto (τ ω)))

include hB hm in
 

theorem brownian_strongMarkov_integral
    (hc : ∀ ω, Continuous (fun t => B t ω)) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (I : Finset ℝ≥0) (φ : BoundedContinuousFunction (I → ℝ) ℝ) :
    (∫ ω in A, φ (shiftedFDD B I (τ ω) ω) ∂P) =
      P.real A * ∫ x, φ x ∂BrownianReal.projectiveFamily I := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (F := fun n ω => φ (shiftedFDD B I (stopGrid n (τ ω)) ω))
    (f := fun ω => φ (shiftedFDD B I (τ ω) ω)) (fun _ => ‖φ‖)
    (fun n => (φ.continuous.measurable.comp
      (shiftedFDD_grid_measurable hm (stopping_time_measurable_nnreal hτ) I n)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall (fun ω => φ.norm_coe_le_norm _))
    (Eventually.of_forall (fun ω => φ.continuous.continuousAt.tendsto.comp
      (shiftedFDD_grid_tendsto hc I τ ω)))
  simp only [shiftedFDD_grid_setIntegral hB hm hτ hA I φ] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
  (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
  (hc : ∀ ω, Continuous (fun t => B t ω))

include hm hc in
lemma brownianRestart_measurable {τ : Ω → ℝ≥0} (hτm : Measurable τ) :
    Measurable (fun ω t => brownianRestart B τ t ω) := by
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  apply Measurable.of_eval
  intro t
  exact (hBm.comp ((hτm.add_const t).prodMk measurable_id)).sub
    (hBm.comp (hτm.prodMk measurable_id))

include hB hm hc in
lemma brownian_restart_fdd_restrict {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) (I : Finset ℝ≥0) :
    (P.restrict A).map (fun ω => shiftedFDD B I (τ ω) ω) =
      P A • BrownianReal.projectiveFamily I := by
  have hXm : Measurable (fun ω => shiftedFDD B I (τ ω) ω) :=
    (Finset.measurable_restrict I).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ))
  let : IsFiniteMeasure (P A • BrownianReal.projectiveFamily I) :=
    Measure.smul_finite _ (measure_ne_top P A)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map hXm.aemeasurable φ.continuous.aestronglyMeasurable,
    integral_smul_measure]
  exact brownian_strongMarkov_integral hB hm hc hτ hA I φ

include hB hm hc in
 

theorem brownian_restart_path_law {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (fun ω t => brownianRestart B τ t ω) =
      P A • P.map (fun ω t => B t ω) := by
  have hXm := brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)
  have hBm : Measurable (fun ω t => B t ω) := Measurable.of_eval hm
  let (I : Finset ℝ≥0) : IsFiniteMeasure (P A • BrownianReal.projectiveFamily I) :=
    Measure.smul_finite _ (measure_ne_top P A)
  have hL : IsProjectiveLimit ((P.restrict A).map (fun ω t => brownianRestart B τ t ω))
      (fun I => P A • BrownianReal.projectiveFamily I) := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hXm]
    exact brownian_restart_fdd_restrict hB hm hc hτ hA I
  have hR : IsProjectiveLimit (P A • P.map (fun ω t => B t ω))
      (fun I => P A • BrownianReal.projectiveFamily I) := by
    intro I
    rw [Measure.map_smul,
      Measure.map_map (Finset.measurable_restrict I) hBm]
    exact congrArg (fun ν => P A • ν) (hB.hasLaw I).map_eq
  exact hL.unique hR

end SLEExactGauge
end


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

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma boundedDiskHit_coe (ρ : a.samples → ℝ≥0) (z : ℂ) (r : ℝ) (T : ℝ≥0)
    (ω : a.samples) :
    (a.boundedDiskHit ρ z r T ω : WithTop ℝ≥0) =
      min (diskHitAfter (γ ∘ Subtype.val) ρ z r ω) T := by
  have hn : min (diskHitAfter (γ ∘ Subtype.val) ρ z r ω) (T : WithTop ℝ≥0) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hn
  change (((min (diskHitAfter (γ ∘ Subtype.val) ρ z r ω) (T : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = _
  rw [← hv, WithTop.untopD_coe]

lemma boundedDiskHit_stopping (ρ : a.samples → ℝ≥0)
    (hρ : IsStoppingTime a.filtration (fun ω => (ρ ω : WithTop ℝ≥0)))
    (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    IsStoppingTime a.filtration (fun ω => (a.boundedDiskHit ρ z r T ω : WithTop ℝ≥0)) := by
  simpa only [a.boundedDiskHit_coe] using (a.diskHitAfter_stopping ρ hρ z r).min_const T



end RegularSLEPresentation
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
-- module Solutions.OAIQ27_SLE.SLE_StoppedMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopped Measures for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal

section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

attribute [local instance] OAI.SLEExactGauge.stoppedTraceFactorRealPathMeasurable
attribute [local instance] OAI.SLEExactGauge.stoppedTraceFactorComplexPathMeasurable
local instance stoppedTraceFactorRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance stoppedTraceFactorComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma source_trace_factor {Ω : Type*} [m : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → C(ℝ≥0, ℂ))
    (ha : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => γ ω t)) :
    ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), Measurable Φ ∧
      γ = Φ ∘ (fun ω => (⟨fun t => B t ω, hc ω⟩ : C(ℝ≥0, ℝ))) := by
  let bp : Ω → C(ℝ≥0, ℝ) := fun ω => ⟨fun t => B t ω, hc ω⟩
  have hb (t : ℝ≥0) : @Measurable Ω ℝ (MeasurableSpace.comap bp (borel _)) (borel ℝ)
      (B t) := by
    exact (continuous_eval_const t).measurable.comp (Measurable.of_comap_le le_rfl)
  have hle (t : ℝ≥0) :
      (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) t ≤
        MeasurableSpace.comap bp (borel _) := by
    change (⨆ s ≤ t, MeasurableSpace.comap (B s) (borel ℝ)) ≤ _
    exact iSup_le fun s => iSup_le fun _ => measurable_iff_comap_le.mp (hb s)
  have hγ : @Measurable Ω C(ℝ≥0,ℂ)
      (MeasurableSpace.comap bp (borel _)) (borel _) γ := by
    let : MeasurableSpace Ω := MeasurableSpace.comap bp (borel _)
    exact source_path_measurable γ (fun t => (ha t).mono (hle t) le_rfl)
  exact hγ.exists_eq_measurable_comp
end
end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_reverseField_sub_real (a u v : ℝ) (z : ℂ) :
    reverseField a (u - v) (z - (v : ℂ)) = reverseField a u z := by
  unfold reverseField
  congr 2
  apply Complex.ext <;> simp [reverseCenter]

 

lemma IsCapacityTwoWitness.source_shifted_reverse_identifies
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T t : ℝ≥0) (w : ℂ) {a : ℝ}
    (ha : 0 < a) (haw : a ≤ w.im) (Q : ℝ → ℂ) (hQ0 : Q 0 = w)
    (hQd : ∀ s ∈ Icc 0 (t : ℝ), HasDerivWithinAt Q
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (Q s))
        (Icc 0 (t : ℝ)) s) :
    F (T + t) (w + (U T : ℂ)) = F T (Q t + (U T : ℂ)) := by
  have hzH : w + (U T : ℂ) ∈ upperHalfPlane := by
    change 0 < (w + (U T : ℂ)).im
    simpa using ha.trans_le haw
  let z := F (T + t) (w + (U T : ℂ))
  have hz : z ∈ survivingDomain γ (T + t) := h.2.2.2.2.2.2.1 _ hzH
  have hzt : z ∈ survivingDomain γ T :=
    survivingDomain_antitone γ (le_add_of_nonneg_right (show 0 ≤ t from bot_le)) hz
  have ht (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      (((T + t : ℝ≥0) : ℝ) - s).toNNReal = T + ((t : ℝ) - s).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2])]
    simp only [NNReal.coe_add]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
    ring
  let R (s : ℝ) := G (((T + t : ℝ≥0) : ℝ) - s).toNNReal z - (U T : ℂ)
  have hRd (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) : HasDerivWithinAt R
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (R s))
      (Icc 0 (t : ℝ)) s := by
    have hs' : s ∈ Icc 0 ((T + t : ℝ≥0) : ℝ) :=
      ⟨hs.1, by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2]⟩
    have hd := ((h.reverse_path_derivative (T+t) (w + (U T : ℂ)) ha
      (by simpa using haw) s hs').sub_const (U T : ℂ)).mono
      (show Icc (0 : ℝ) t ⊆ Icc 0 ((T+t : ℝ≥0) : ℝ) from
        Icc_subset_Icc le_rfl (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg]))
    change HasDerivWithinAt R _ _ _ at hd
    simpa only [R, ht s hs, source_reverseField_sub_real] using hd
  have he : EqOn Q R (Icc 0 (t : ℝ)) := by
    apply ODE_solution_unique
      (fun s => reverseField_lipschitz ha (U (T + ((t : ℝ) - s).toNNReal) - U T))
      (fun s hs => (hQd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hQd s ⟨hs.1, hs.2.le⟩))
      (fun s hs => (hRd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hRd s ⟨hs.1, hs.2.le⟩))
    simpa only [R, sub_zero, Real.toNNReal_coe, z,
      h.2.2.2.2.2.2.2.2.1 (T+t) _ hzH, add_sub_cancel_right] using hQ0
  have heT := he ⟨t.coe_nonneg, le_rfl⟩
  have htime : (((T + t : ℝ≥0) : ℝ) - (t : ℝ)).toNNReal = T := by
    simp only [NNReal.coe_add, add_sub_cancel_right, Real.toNNReal_coe]
  have hQ : Q t + (U T : ℂ) = G T z := by
    simpa only [R, htime, sub_add_cancel] using congrArg (fun v : ℂ => v + (U T : ℂ)) heT
  rw [hQ, h.2.2.2.2.2.2.2.1 T z hzt]

end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.stoppedReverseFlowRealPathMeasurable
local instance stoppedReverseFlowRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma source_canonical_reverse_flow (κ : ℝ) (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    ∃ Q : ℝ → C(ℝ≥0, ℝ) → ℂ,
      (∀ s, Measurable (Q s)) ∧
      (∀ p, Q 0 p = (Real.sqrt κ * p T : ℝ) + (a : ℂ) * I) ∧
      ∀ p s, 0 ≤ s → HasDerivWithinAt (fun r => Q r p)
        (reverseField a (Real.sqrt κ * p ((T : ℝ) - s).toNNReal) (Q s p)) (Ici 0) s := by
  let V (s : ℝ) (p : C(ℝ≥0, ℝ)) := Real.sqrt κ * p ((T : ℝ) - s).toNNReal
  have hV : Continuous (fun q : ℝ × C(ℝ≥0, ℝ) => V q.1 q.2) := by
    apply continuous_const.mul
    exact continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_fst)))
  have hw : Measurable (fun p : C(ℝ≥0, ℝ) =>
      (Real.sqrt κ * p T : ℝ) + (a : ℂ) * I) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_eval_const T))).measurable.add_const _
  obtain ⟨Q, hQm, hQ0, hQd⟩ := exists_measurable_reverse_flow V hV.measurable
    (fun p => hV.comp (continuous_id.prodMk continuous_const)) _ hw ha
  exact ⟨Q, fun s => hQm.comp (measurable_prodMk_left (x := s)), hQ0, hQd⟩

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.stoppedRestartLawRealPathMeasurable
local instance stoppedRestartLawComplexPathMeasurable_r84b6d0_1 : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance stoppedRestartLawRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

local instance stoppedRestartLawComplexPathBorel_r84b6d0_1 : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_restart_continuous_driver_law
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (sourceRestartDriverPath B hc τ) =
      P A • P.map (sourceDriverPath B hc) := by
  have hbm : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  have hrm : Measurable (sourceRestartDriverPath B hc τ) :=
    source_path_measurable _ (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
  apply source_path_evaluation_embedding.map_injective
  have he := congrArg (Measure.map (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)))
    (brownian_restart_path_law hB hm hc hτ hA)
  have hem : Measurable (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [Measure.map_map source_path_evaluation_embedding.measurable hrm,
    Measure.map_smul,
    Measure.map_map source_path_evaluation_embedding.measurable hbm]
  rw [Measure.map_map hem (brownianRestart_measurable hm hc
    (stopping_time_measurable_nnreal hτ)), Measure.map_smul,
    Measure.map_map hem (Measurable.of_eval hm)] at he
  exact he

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.stoppedTraceLawRealPathMeasurable
attribute [local instance] OAI.SLEExactGauge.stoppedTraceLawComplexPathMeasurable
local instance stoppedTraceLawRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance stoppedTraceLawComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem sourceStoppedTraceLaw : SourceStoppedTraceLawTarget := by
  intro Ω m P κ hκ hκ8 B hB hm hc γ G F hw
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let bp := sourceDriverPath B hc
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  have hbm : Measurable bp := source_path_measurable bp hm
  have hγa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => gp ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω)
      ?_ (fun ω => continuous_const.mul (hc ω)) γ G F hw
    intro t
    exact measurable_const.mul
      ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
  obtain ⟨Φ, hΦm, hΦ⟩ := source_trace_factor B hm hc gp hγa
  have hΦe (ω : Ω) : Φ (bp ω) = gp ω := (congrFun hΦ ω).symm
  have hgm : Measurable gp := hΦ ▸ hΦm.comp hbm
  refine ⟨Φ, hΦm, hΦe, ?_⟩
  intro τ hτ
  let rp := sourceRestartDriverPath B hc τ
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have hlaw (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
      (P.restrict A).map rp = P A • P.map bp :=
    source_restart_continuous_driver_law hB hm hc τ hτ hA
  have hlaw0 : P.map rp = P.map bp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using hlaw univ MeasurableSet.univ
  constructor
  · intro A hA
    have he := congrArg (Measure.map Φ) (hlaw A hA)
    rw [Measure.map_map hΦm hrm, Measure.map_smul,
      Measure.map_map hΦm hbm] at he
    have hcomp : Φ ∘ bp = gp := hΦ.symm
    simpa only [hcomp, rp, gp, Function.comp_def] using he
  · choose Q hQm hQ0 hQd using fun (t : ℝ≥0) (n : ℕ) =>
      source_canonical_reverse_flow κ t (a := 1 / ((n : ℝ) + 1)) (by positivity)
    let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
    have hy : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall ha⟩
    have hQorig (ω : Ω) (t : ℝ≥0) (n : ℕ) :
        Q t n t (bp ω) = F ω t ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) := by
      apply (hw ω).reverse_flow_identifies t
        ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (bp ω)) (hQ0 t n (bp ω))
      intro s hs
      exact (hQd t n (bp ω) s hs.1).mono Icc_subset_Ici_self
    have hQlimit (ω : Ω) (t : ℝ≥0) :
        Tendsto (fun n => Q t n t (bp ω)) atTop (𝓝 (Φ (bp ω) t)) := by
      have ht := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 t).comp hy
      simpa only [hQorig, hΦe, gp, sourceTracePath, ContinuousMap.coe_mk, Function.comp_def] using ht
    have hset (t : ℝ≥0) : MeasurableSet
        {p : C(ℝ≥0,ℝ) | Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0)} :=
      measurableSet_tendsto (𝓝 (0 : ℂ)) (fun n => (hQm t n t).sub
        ((continuous_eval_const t).measurable.comp hΦm))
    have hQR (t : ℝ≥0) : ∀ᵐ ω ∂P,
        Tendsto (fun n => Q t n t (rp ω)) atTop (𝓝 (Φ (rp ω) t)) := by
      have ho : ∀ᵐ p ∂P.map bp,
          Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0) := by
        apply (ae_map_iff hbm.aemeasurable (hset t)).2
        exact Eventually.of_forall (fun ω => tendsto_sub_nhds_zero_iff.mpr (hQlimit ω t))
      rw [← hlaw0] at ho
      filter_upwards [(ae_map_iff hrm.aemeasurable (hset t)).1 ho] with ω hω
      exact tendsto_sub_nhds_zero_iff.mp hω
    have hQRall : ∀ᵐ ω ∂P, ∀ j : ℕ,
        Tendsto (fun n => Q (denseSeq ℝ≥0 j) n (denseSeq ℝ≥0 j) (rp ω)) atTop
          (𝓝 (Φ (rp ω) (denseSeq ℝ≥0 j))) := ae_all_iff.mpr (fun j => hQR _)
    filter_upwards [hQRall] with ω hω
    have hcoc (t : ℝ≥0) (n : ℕ) :
        F ω (τ ω + t) ((Real.sqrt κ * B (τ ω + t) ω : ℝ) + (a n : ℂ) * I) =
        F ω (τ ω) (Q t n t (rp ω) + (Real.sqrt κ * B (τ ω) ω : ℝ)) := by
      have he := (hw ω).source_shifted_reverse_identifies (τ ω) t
        ((Real.sqrt κ * (rp ω) t : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (rp ω)) (hQ0 t n (rp ω))
        (fun s hs => by
          have hh := (hQd t n (rp ω) s hs.1).mono
            (show Icc (0 : ℝ) t ⊆ Ici 0 from Icc_subset_Ici_self)
          simpa only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk,
            mul_sub] using hh)
      convert he using 2
      all_goals try with_reducible_and_instances rfl
      simp only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk]
      push_cast
      ring
    have hdense (j : ℕ) (hj : Φ (rp ω) (denseSeq ℝ≥0 j) ∈ upperHalfPlane) :
        γ ω (τ ω + denseSeq ℝ≥0 j) = F ω (τ ω)
          (Φ (rp ω) (denseSeq ℝ≥0 j) + (Real.sqrt κ * B (τ ω) ω : ℝ)) := by
      let t := denseSeq ℝ≥0 j
      have hz : Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ) ∈ upperHalfPlane := by
        simpa only [upperHalfPlane, mem_ofPred_eq, add_im, ofReal_im, add_zero] using hj
      have hFt : ContinuousAt (F ω (τ ω))
          (Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ)) :=
        ((hw ω).2.2.2.2.1 (τ ω)).continuousOn.continuousAt
          (isOpen_upperHalfPlane.mem_nhds hz)
      have hlimF := hFt.tendsto.comp ((hω j).add_const ((Real.sqrt κ * B (τ ω) ω : ℝ) : ℂ))
      have hlimγ := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 (τ ω + t)).comp hy
      simp only [Function.comp_def, hcoc] at hlimγ
      exact tendsto_nhds_unique hlimγ hlimF
    let S : Set ℝ≥0 := {t | Φ (rp ω) t ∈ upperHalfPlane}
    have hSo : IsOpen S := isOpen_upperHalfPlane.preimage (Φ (rp ω)).continuous
    have hleft : ContinuousOn (fun t => γ ω (τ ω + t)) S :=
      ((hw ω).1.comp (continuous_const.add continuous_id)).continuousOn
    have hright : ContinuousOn (fun t => F ω (τ ω)
        (Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ))) S := by
      apply ((hw ω).2.2.2.2.1 (τ ω)).continuousOn.comp
        ((Φ (rp ω)).continuous.add_const _).continuousOn
      intro t ht
      simpa only [S, upperHalfPlane, mem_ofPred_eq, add_im, ofReal_im, add_zero] using ht
    have hEq : EqOn (fun t => γ ω (τ ω + t))
        (fun t => F ω (τ ω) (Φ (rp ω) t + (Real.sqrt κ * B (τ ω) ω : ℝ)))
        (S ∩ range (denseSeq ℝ≥0)) := by
      rintro t ⟨ht, j, rfl⟩
      exact hdense j ht
    exact hEq.of_subset_closure hleft hright inter_subset_left
      ((denseRange_denseSeq ℝ≥0).open_subset_closure_inter hSo)
end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.stoppedForwardLawRealPathMeasurable
attribute [local instance] OAI.SLEExactGauge.stoppedForwardLawComplexPathMeasurable
local instance stoppedForwardLawRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance stoppedForwardLawComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma IsCapacityTwoWitness.source_shifted_forward_approximation
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T t : ℝ≥0) (w : ℂ) {a : ℝ}
    (ha : 0 < a) (haw : a ≤ w.im) (Q : ℝ → ℂ) (hQ0 : Q 0 = w)
    (hQd : ∀ s ∈ Icc 0 (t : ℝ), HasDerivWithinAt Q
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (Q s))
        (Icc 0 (t : ℝ)) s) :
    Q t = G T (F (T + t) (w + (U T : ℂ))) - (U T : ℂ) := by
  have hzH : w + (U T : ℂ) ∈ upperHalfPlane := by
    change 0 < (w + (U T : ℂ)).im
    simpa using ha.trans_le haw
  let z := F (T + t) (w + (U T : ℂ))
  have hz : z ∈ survivingDomain γ (T + t) := h.2.2.2.2.2.2.1 _ hzH
  have hzt : z ∈ survivingDomain γ T :=
    survivingDomain_antitone γ (le_add_of_nonneg_right (show 0 ≤ t from bot_le)) hz
  have ht (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      (((T + t : ℝ≥0) : ℝ) - s).toNNReal = T + ((t : ℝ) - s).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2])]
    simp only [NNReal.coe_add]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
    ring
  let R (s : ℝ) := G (((T + t : ℝ≥0) : ℝ) - s).toNNReal z - (U T : ℂ)
  have hRd (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) : HasDerivWithinAt R
      (reverseField a (U (T + ((t : ℝ) - s).toNNReal) - U T) (R s))
      (Icc 0 (t : ℝ)) s := by
    have hs' : s ∈ Icc 0 ((T + t : ℝ≥0) : ℝ) :=
      ⟨hs.1, by simp only [NNReal.coe_add]; linarith [T.coe_nonneg, hs.2]⟩
    have hd := ((h.reverse_path_derivative (T+t) (w + (U T : ℂ)) ha
      (by simpa using haw) s hs').sub_const (U T : ℂ)).mono
      (show Icc (0 : ℝ) t ⊆ Icc 0 ((T+t : ℝ≥0) : ℝ) from
        Icc_subset_Icc le_rfl (by simp only [NNReal.coe_add]; linarith [T.coe_nonneg]))
    change HasDerivWithinAt R _ _ _ at hd
    simpa only [R, ht s hs, source_reverseField_sub_real] using hd
  have he : EqOn Q R (Icc 0 (t : ℝ)) := by
    apply ODE_solution_unique
      (fun s => reverseField_lipschitz ha (U (T + ((t : ℝ) - s).toNNReal) - U T))
      (fun s hs => (hQd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hQd s ⟨hs.1, hs.2.le⟩))
      (fun s hs => (hRd s hs).continuousWithinAt)
      (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hRd s ⟨hs.1, hs.2.le⟩))
    simpa only [R, sub_zero, Real.toNNReal_coe, z,
      h.2.2.2.2.2.2.2.2.1 (T+t) _ hzH, add_sub_cancel_right] using hQ0
  have heT := he ⟨t.coe_nonneg, le_rfl⟩
  have htime : (((T + t : ℝ≥0) : ℝ) - (t : ℝ)).toNNReal = T := by
    simp only [NNReal.coe_add, add_sub_cancel_right, Real.toNNReal_coe]
  have hQ : Q t + (U T : ℂ) = G T z := by
    simpa only [R, htime, sub_add_cancel] using congrArg (fun v : ℂ => v + (U T : ℂ)) heT
  exact eq_sub_iff_add_eq.mpr hQ

universe u_source_stopped

theorem sourceStoppedTraceLaw_forward :
  ∀ {Ω : Type u_source_stopped} [_m : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ), 0 < κ → κ < 8 →
  ∀ (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)),
  ∃ Φ : C(ℝ≥0, ℝ) → C(ℝ≥0, ℂ), Measurable Φ ∧
    (∀ ω, Φ (sourceDriverPath B hc ω) = sourceTracePath γ (fun ω => (hw ω).1) ω) ∧
    ∀ (τ : Ω → ℝ≥0)
      (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (τ ω : WithTop ℝ≥0))),
      (∀ (A : Set Ω), MeasurableSet[hτ.measurableSpace] A →
        (P.restrict A).map (fun ω => Φ (sourceRestartDriverPath B hc τ ω)) =
          P A • P.map (sourceTracePath γ (fun ω => (hw ω).1))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        γ ω (τ ω + t) ∈ survivingDomain (γ ω) (τ ω) →
        Φ (sourceRestartDriverPath B hc τ ω) t =
          G ω (τ ω) (γ ω (τ ω + t)) - (Real.sqrt κ * B (τ ω) ω : ℝ)) := by
  intro Ω m P κ hκ hκ8 B hB hm hc γ G F hw
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let bp := sourceDriverPath B hc
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  have hbm : Measurable bp := source_path_measurable bp hm
  have hγa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => gp ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω)
      ?_ (fun ω => continuous_const.mul (hc ω)) γ G F hw
    intro t
    exact measurable_const.mul
      ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
  obtain ⟨Φ, hΦm, hΦ⟩ := source_trace_factor B hm hc gp hγa
  have hΦe (ω : Ω) : Φ (bp ω) = gp ω := (congrFun hΦ ω).symm
  have hgm : Measurable gp := hΦ ▸ hΦm.comp hbm
  refine ⟨Φ, hΦm, hΦe, ?_⟩
  intro τ hτ
  let rp := sourceRestartDriverPath B hc τ
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hc
      (stopping_time_measurable_nnreal hτ)))
  have hlaw (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
      (P.restrict A).map rp = P A • P.map bp :=
    source_restart_continuous_driver_law hB hm hc τ hτ hA
  have hlaw0 : P.map rp = P.map bp := by
    simpa only [Measure.restrict_univ, measure_univ, one_smul] using hlaw univ MeasurableSet.univ
  constructor
  · intro A hA
    have he := congrArg (Measure.map Φ) (hlaw A hA)
    rw [Measure.map_map hΦm hrm, Measure.map_smul,
      Measure.map_map hΦm hbm] at he
    have hcomp : Φ ∘ bp = gp := hΦ.symm
    simpa only [hcomp, rp, gp, Function.comp_def] using he
  · choose Q hQm hQ0 hQd using fun (t : ℝ≥0) (n : ℕ) =>
      source_canonical_reverse_flow κ t (a := 1 / ((n : ℝ) + 1)) (by positivity)
    let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
    have hy : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall ha⟩
    have hQorig (ω : Ω) (t : ℝ≥0) (n : ℕ) :
        Q t n t (bp ω) = F ω t ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) := by
      apply (hw ω).reverse_flow_identifies t
        ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (bp ω)) (hQ0 t n (bp ω))
      intro s hs
      exact (hQd t n (bp ω) s hs.1).mono Icc_subset_Ici_self
    have hQlimit (ω : Ω) (t : ℝ≥0) :
        Tendsto (fun n => Q t n t (bp ω)) atTop (𝓝 (Φ (bp ω) t)) := by
      have ht := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 t).comp hy
      simpa only [hQorig, hΦe, gp, sourceTracePath, ContinuousMap.coe_mk, Function.comp_def] using ht
    have hset (t : ℝ≥0) : MeasurableSet
        {p : C(ℝ≥0,ℝ) | Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0)} :=
      measurableSet_tendsto (𝓝 (0 : ℂ)) (fun n => (hQm t n t).sub
        ((continuous_eval_const t).measurable.comp hΦm))
    have hQR (t : ℝ≥0) : ∀ᵐ ω ∂P,
        Tendsto (fun n => Q t n t (rp ω)) atTop (𝓝 (Φ (rp ω) t)) := by
      have ho : ∀ᵐ p ∂P.map bp,
          Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0) := by
        apply (ae_map_iff hbm.aemeasurable (hset t)).2
        exact Eventually.of_forall (fun ω => tendsto_sub_nhds_zero_iff.mpr (hQlimit ω t))
      rw [← hlaw0] at ho
      filter_upwards [(ae_map_iff hrm.aemeasurable (hset t)).1 ho] with ω hω
      exact tendsto_sub_nhds_zero_iff.mp hω
    have hQRall : ∀ᵐ ω ∂P, ∀ j : ℕ,
        Tendsto (fun n => Q (denseSeq ℝ≥0 j) n (denseSeq ℝ≥0 j) (rp ω)) atTop
          (𝓝 (Φ (rp ω) (denseSeq ℝ≥0 j))) := ae_all_iff.mpr (fun j => hQR _)
    filter_upwards [hQRall] with ω hω
    have hcoc (t : ℝ≥0) (n : ℕ) :
        Q t n t (rp ω) = G ω (τ ω)
          (F ω (τ ω + t) ((Real.sqrt κ * B (τ ω + t) ω : ℝ) + (a n : ℂ) * I)) -
            (Real.sqrt κ * B (τ ω) ω : ℝ) := by
      have he := (hw ω).source_shifted_forward_approximation (τ ω) t
        ((Real.sqrt κ * (rp ω) t : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
        (fun s => Q t n s (rp ω)) (hQ0 t n (rp ω))
        (fun s hs => by
          have hh := (hQd t n (rp ω) s hs.1).mono
            (show Icc (0 : ℝ) t ⊆ Ici 0 from Icc_subset_Ici_self)
          simpa only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk,
            mul_sub] using hh)
      convert he using 2
      all_goals try with_reducible_and_instances rfl
      simp only [rp, sourceRestartDriverPath, brownianRestart, ContinuousMap.coe_mk]
      push_cast
      ring_nf
    have hdense (j : ℕ)
        (hj : γ ω (τ ω + denseSeq ℝ≥0 j) ∈ survivingDomain (γ ω) (τ ω)) :
        Φ (rp ω) (denseSeq ℝ≥0 j) =
          G ω (τ ω) (γ ω (τ ω + denseSeq ℝ≥0 j)) - (Real.sqrt κ * B (τ ω) ω : ℝ) := by
      let t := denseSeq ℝ≥0 j
      have hGc : ContinuousAt (G ω (τ ω)) (γ ω (τ ω + t)) :=
        ((hw ω).2.2.2.1 (τ ω)).continuousOn.continuousAt
          ((isOpen_survivingDomain (hw ω).1 (τ ω)).mem_nhds hj)
      have hlimγ := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 (τ ω + t)).comp hy
      have hlimG := (hGc.tendsto.comp hlimγ).sub_const ((Real.sqrt κ * B (τ ω) ω : ℝ) : ℂ)
      apply tendsto_nhds_unique (hω j)
      simpa only [hcoc, Function.comp_def] using hlimG
    let S : Set ℝ≥0 := {t | γ ω (τ ω + t) ∈ survivingDomain (γ ω) (τ ω)}
    have hγc : Continuous (fun t : ℝ≥0 => γ ω (τ ω + t)) :=
      (hw ω).1.comp (continuous_const.add continuous_id)
    have hSo : IsOpen S := (isOpen_survivingDomain (hw ω).1 (τ ω)).preimage hγc
    have hleft : ContinuousOn (fun t : ℝ≥0 => Φ (rp ω) t) S :=
      (Φ (rp ω)).continuous.continuousOn
    have hright : ContinuousOn (fun t : ℝ≥0 =>
        G ω (τ ω) (γ ω (τ ω + t)) - (Real.sqrt κ * B (τ ω) ω : ℝ)) S :=
      (((hw ω).2.2.2.1 (τ ω)).continuousOn.comp hγc.continuousOn
        (fun _ ht => ht)).sub continuousOn_const
    have hEq : EqOn (fun t : ℝ≥0 => Φ (rp ω) t)
        (fun t : ℝ≥0 => G ω (τ ω) (γ ω (τ ω + t)) - (Real.sqrt κ * B (τ ω) ω : ℝ))
        (S ∩ range (denseSeq ℝ≥0)) := by
      rintro t ⟨ht, j, rfl⟩
      exact hdense j ht
    exact hEq.of_subset_closure hleft hright inter_subset_left
      ((denseRange_denseSeq ℝ≥0).open_subset_closure_inter hSo)

end
end SLEExactGauge

end

section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
namespace SLEExactGauge

 

lemma source_parameter_joint_law
    {Ω Z E : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [IsProbabilityMeasure ν]
    (hm : m ≤ mΩ)
    {X : Ω → E} (hX : Measurable X) {Y : Ω → Z} (hY : Measurable[m] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A → (P.restrict A).map X = P A • ν)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    (P.restrict A).map (fun ω => (Y ω, X ω)) = ((P.restrict A).map Y).prod ν := by
  have hYa : Measurable Y := hY.mono hm le_rfl
  apply Measure.ext_prod
  intro S T hS hT
  have he := congrArg (fun μ : Measure E => μ T)
    (hlaw (A ∩ Y ⁻¹' S) (hA.inter (hY hS)))
  rw [Measure.map_apply hX hT, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply (hX hT)] at he
  rw [Measure.map_apply (hYa.prodMk hX) (hS.prod hT),
    Measure.restrict_apply ((hYa.prodMk hX) (hS.prod hT)),
    Measure.prod_prod, Measure.map_apply hYa hS, Measure.restrict_apply (hYa hS)]
  change P ((Y ⁻¹' S ∩ X ⁻¹' T) ∩ A) = P (Y ⁻¹' S ∩ A) * ν T
  simpa only [inter_assoc, inter_left_comm, inter_comm] using he

lemma source_parameter_condExp
    {Ω Z E : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [IsProbabilityMeasure ν]
    (hm : m ≤ mΩ)
    {X : Ω → E} (hX : Measurable X) {Y : Ω → Z} (hY : Measurable[m] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A → (P.restrict A).map X = P A • ν)
    (H : Z × E → ℝ) (hH : Measurable H) (hb : ∀ p, ‖H p‖ ≤ 1) :
    P[(fun ω => H (Y ω, X ω)) | m] =ᵐ[P] (fun ω => ∫ e, H (Y ω, e) ∂ν) := by
  have hYa : Measurable Y := hY.mono hm le_rfl
  have hK : StronglyMeasurable (fun y => ∫ e, H (y, e) ∂ν) :=
    hH.stronglyMeasurable.integral_prod_right'
  have hKb (y : Z) : ‖∫ e, H (y, e) ∂ν‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall (fun e => hb (y,e)))
  have hint : Integrable (fun ω => H (Y ω, X ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hH.comp (hYa.prodMk hX)).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hb (Y ω, X ω)))
  have hKint : Integrable (fun ω => ∫ e, H (Y ω, e) ∂ν) P :=
    (integrable_const (1 : ℝ)).mono' (hK.comp_measurable hYa).aestronglyMeasurable
      (Eventually.of_forall (fun ω => hKb (Y ω)))
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hint
    (fun _ _ _ => hKint.integrableOn) _ (hK.comp_measurable hY).aestronglyMeasurable
  intro A hA _
  have hprodint : Integrable H (((P.restrict A).map Y).prod ν) :=
    (integrable_const (1 : ℝ)).mono' hH.aestronglyMeasurable (Eventually.of_forall hb)
  calc
    (∫ ω in A, ∫ e, H (Y ω, e) ∂ν ∂P) =
        ∫ y, ∫ e, H (y, e) ∂ν ∂(P.restrict A).map Y :=
      (integral_map hYa.aemeasurable hK.aestronglyMeasurable).symm
    _ = ∫ p, H p ∂(((P.restrict A).map Y).prod ν) := (integral_prod H hprodint).symm
    _ = ∫ p, H p ∂(P.restrict A).map (fun ω => (Y ω, X ω)) := by
      rw [source_parameter_joint_law hm hX hY hlaw A hA]
    _ = ∫ ω in A, H (Y ω, X ω) ∂P :=
      integral_map (hYa.prodMk hX).aemeasurable hH.aestronglyMeasurable

end SLEExactGauge

end

end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ChartMeasurability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chart Measurability for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_killedChart_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (z : ℂ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace]
      (fun ω => if z ∈ survivingDomain (γ ω) (τ ω) then G ω (τ ω) z else 0) := by
  exact measurable_stoppedValue
    (source_killedChart_progressive hm hc κ γ G F hw z) hτ

end
end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex TopologicalSpace Classical
open scoped Topology NNReal
namespace SLEExactGauge

lemma source_measurable_inverse_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (S : Ω → Set ℂ) (G F K : Ω → ℂ → ℂ) (H : Set ℂ)
    (hS : ∀ ω, IsOpen (S ω)) (hH : IsOpen H)
    (hG : ∀ ω, ContinuousOn (G ω) (S ω))
    (hF : ∀ ω, ContinuousOn (F ω) H)
    (hFH : ∀ ω, MapsTo (F ω) H (S ω))
    (hGF : ∀ ω z, z ∈ H → G ω (F ω z) = z)
    (hFG : ∀ ω z, z ∈ S ω → F ω (G ω z) = z)
    (hK : ∀ z, Measurable (fun ω => K ω z))
    (hKeq : ∀ ω z, K ω z = if z ∈ S ω then G ω z else 0)
    (hGH : ∀ ω z, z ∈ S ω → 0 < (G ω z).im)
    (w : Ω → ℂ) (hwm : Measurable w) (hw : ∀ ω, w ω ∈ H) :
    Measurable (fun ω => F ω (w ω)) := by
  classical
  let d := denseSeq ℂ
  let v (k : ℕ) (ω : Ω) (n : ℕ) : Prop :=
    0 < (K ω (d n)).im ∧ dist (K ω (d n)) (w ω) < 1/((k:ℝ)+1)
  have hv (k : ℕ) (ω : Ω) : ∃ n, v k ω n := by
    have hpos : 0 < 1/((k:ℝ)+1) := by positivity
    have hx : F ω (w ω) ∈ S ω := hFH ω (hw ω)
    have hct := (hG ω).continuousAt ((hS ω).mem_nhds hx)
    have hn : {z | dist (G ω z) (w ω) < 1/((k:ℝ)+1)} ∈ 𝓝 (F ω (w ω)) := by
      change G ω ⁻¹' Metric.ball (w ω) (1/((k:ℝ)+1)) ∈ 𝓝 (F ω (w ω))
      apply hct.preimage_mem_nhds
      rw [hGF ω _ (hw ω)]
      exact Metric.ball_mem_nhds (w ω) hpos
    obtain ⟨n,hn⟩ := (denseRange_denseSeq ℂ).mem_nhds (inter_mem ((hS ω).mem_nhds hx) hn)
    refine ⟨n,?_⟩
    dsimp [v,d]
    rw [hKeq,ite_eq_left hn.1]
    exact ⟨hGH ω _ hn.1,hn.2⟩
  have hvm (k n : ℕ) : MeasurableSet {ω | v k ω n} :=
    (measurableSet_lt measurable_const (Complex.measurable_im.comp (hK _))).inter
      (measurableSet_lt ((hK _).dist hwm) measurable_const)
  let j (k : ℕ) (ω : Ω) : ℕ := Nat.find (hv k ω)
  have hj (k : ℕ) : Measurable (j k) := measurable_find (hv k) (hvm k)
  have hjv (k : ℕ) (ω : Ω) : v k ω (j k ω) := Nat.find_spec (hv k ω)
  have hjS (k : ℕ) (ω : Ω) : d (j k ω) ∈ S ω := by
    by_contra hn
    have hh := (hjv k ω).1
    rw [hKeq,ite_eq_right hn] at hh
    norm_num at hh
  have hlim (ω : Ω) : Tendsto (fun k => K ω (d (j k ω))) atTop (𝓝 (w ω)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
    refine ⟨N,fun k hk => (hjv k ω).2.trans ?_⟩
    simpa only [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < 1/((k:ℝ)+1))]
      using hN k hk
  have hflim (ω : Ω) : Tendsto (fun k => d (j k ω)) atTop (𝓝 (F ω (w ω))) := by
    have hh := ((hF ω).continuousAt (hH.mem_nhds (hw ω))).tendsto.comp (hlim ω)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext k
    simp only [Function.comp_apply,hKeq,ite_eq_left (hjS k ω),hFG ω _ (hjS k ω)]
  exact measurable_of_tendsto_metrizable (fun k => (measurable_of_countable d).comp (hj k)) (tendsto_pi_nhds.mpr hflim)
end SLEExactGauge

end

section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal
namespace SLEExactGauge
lemma source_stopped_inverseChart_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (w : Ω → ℂ)
    (hwm : Measurable[hτ.measurableSpace] w) (hwH : ∀ ω, w ω ∈ upperHalfPlane) :
    Measurable[hτ.measurableSpace] (fun ω => F ω (τ ω) (w ω)) := by
  apply @source_measurable_inverse_chart Ω hτ.measurableSpace
    (fun ω => survivingDomain (γ ω) (τ ω)) (fun ω => G ω (τ ω))
    (fun ω => F ω (τ ω))
    (fun ω z => if z ∈ survivingDomain (γ ω) (τ ω) then G ω (τ ω) z else 0)
    upperHalfPlane
    (fun ω => isOpen_survivingDomain (hw ω).1 _) isOpen_upperHalfPlane
    (fun ω => ((hw ω).2.2.2.1 _).continuousOn)
    (fun ω => ((hw ω).2.2.2.2.1 _).continuousOn)
    (fun ω => (hw ω).2.2.2.2.2.2.1 _)
    (fun ω => (hw ω).2.2.2.2.2.2.2.2.1 _)
    (fun ω => (hw ω).2.2.2.2.2.2.2.1 _)
    (fun z => source_killedChart_stopped_measurable hm hc κ γ G F hw z τ hτ)
    (fun _ _ => rfl)
    (fun ω z hz => (hw ω).imag_positive _ z hz) w hwm hwH
end SLEExactGauge

end

section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.instMeasurableSpaceContinuousMapElemComplexUpperHalfPlane
local instance instBorelSpaceContinuousMapElemComplexUpperHalfPlane : BorelSpace C(upperHalfPlane,ℂ) := ⟨rfl⟩

lemma source_halfplane_cmap_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → C(upperHalfPlane,ℂ))
    (hf : ∀ z, Measurable (fun ω => f ω z)) : Measurable f := by
  let : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
  let : PolishSpace upperHalfPlane := isOpen_upperHalfPlane.polishSpace
  let : Nonempty upperHalfPlane := ⟨⟨Complex.I,by simp [upperHalfPlane]⟩⟩
  have he : MeasurableEmbedding
      (fun F : C(upperHalfPlane,ℂ) => fun n => F (denseSeq upperHalfPlane n)) := by
    apply Continuous.measurableEmbedding
    · exact continuous_pi fun n => continuous_eval_const _
    · intro F G heq
      apply DFunLike.coe_injective
      exact (denseRange_denseSeq upperHalfPlane).equalizer F.continuous G.continuous heq
  exact he.measurable_comp_iff.mp (Measurable.of_eval (fun _ => hf _))

lemma source_stopped_inversePath_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] (sourceStoppedInversePath B κ γ G F hw τ) := by
  apply @source_halfplane_cmap_measurable Ω hτ.measurableSpace
  intro z
  have hB := measurable_stoppedValue
    ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).isStronglyProgressive_of_continuous hc) hτ
  apply source_stopped_inverseChart_measurable B hm hc κ γ G F hw τ hτ
    (fun ω => z+(Real.sqrt κ * B (τ ω) ω : ℝ))
  · exact measurable_const.add (Complex.measurable_ofReal.comp (measurable_const.mul hB))
  · intro ω
    simpa [upperHalfPlane] using z.2
end
end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma source_physical_disk_kernel_open :
  IsOpen {p : SourceDiskParameter × C(ℝ≥0,ℂ) |
    ∃ t : ℝ≥0, p.1.1.2 ∈ survivingDomain p.2 t ∧
      ∃ h : p.2 t ∈ upperHalfPlane,
        p.1.2.2 < ‖p.1.1.1 ⟨p.2 t,h⟩ - p.1.2.1‖} := by
  let : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
  have ht (t : ℝ≥0) :
      IsOpen {p : SourceDiskParameter × C(ℝ≥0,ℂ) |
        p.1.1.2 ∈ survivingDomain p.2 t ∧
          ∃ h : p.2 t ∈ upperHalfPlane,
            p.1.2.2 < ‖p.1.1.1 ⟨p.2 t,h⟩ - p.1.2.1‖} := by
    let S : Set (SourceDiskParameter × C(ℝ≥0,ℂ)) := {p | p.2 t ∈ upperHalfPlane}
    have hS : IsOpen S := isOpen_upperHalfPlane.preimage
      ((continuous_eval_const t).comp continuous_snd)
    let Z : S → upperHalfPlane := fun p => ⟨p.1.2 t,p.2⟩
    have hZ : Continuous Z := Continuous.subtype_mk
      ((continuous_eval_const t).comp (continuous_snd.comp continuous_subtype_val)) _
    have hF : Continuous (fun p : S => p.1.1.1.1 (Z p)) :=
      continuous_eval.comp
        ((continuous_fst.fst.fst.comp continuous_subtype_val).prodMk hZ)
    have hLive : IsOpen {p : S | p.1.1.1.2 ∈ survivingDomain p.1.2 t} :=
      source_survival_open.preimage
        (((continuous_snd.comp continuous_subtype_val).prodMk continuous_const).prodMk
          (continuous_fst.fst.snd.comp continuous_subtype_val))
    have hExit : IsOpen {p : S | p.1.1.2.2 < ‖p.1.1.1.1 (Z p) - p.1.1.2.1‖} :=
      isOpen_lt (continuous_fst.snd.snd.comp continuous_subtype_val)
        ((hF.sub (continuous_fst.snd.fst.comp continuous_subtype_val)).norm)
    have hO := hS.isOpenMap_subtype_val _ (hLive.inter hExit)
    convert hO using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    constructor
    · rintro ⟨hl,h,he⟩
      exact ⟨⟨p,h⟩,⟨hl,he⟩,rfl⟩
    · rintro ⟨q,⟨hl,he⟩,rfl⟩
      exact ⟨hl,q.2,he⟩
  simpa only [ofPred_exists] using isOpen_iUnion ht
end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_high_vertical_survives {γ : ℝ≥0 → ℂ} {t : ℝ≥0} {R : ℝ}
    (hR : 0 ≤ R) (hb : ∀ s ∈ Icc 0 t, ‖γ s‖ ≤ R) {y : ℝ} (hy : R < y) :
    (⟨0,y⟩ : ℂ) ∈ survivingDomain γ t := by
  let A : Set ℂ := {z | R < z.im}
  have hA : A ⊆ upperHalfPlane \ γ '' Icc 0 t := by
    intro z hz
    refine ⟨lt_of_le_of_lt hR hz, ?_⟩
    rintro ⟨s,hs,rfl⟩
    have hh := (le_abs_self (γ s).im).trans ((Complex.abs_im_le_norm _).trans (hb s hs))
    exact (not_lt_of_ge hh) hz
  refine ⟨hA hy, ?_⟩
  intro hbd
  obtain ⟨C,hC⟩ := (hbd.subset ((convex_halfSpace_im_gt R).isPreconnected.subset_connectedComponentIn hy hA)).exists_norm_le
  let v : ℝ := max C R + 1
  have hv : R < v := by dsimp [v]; linarith [le_max_right C R]
  have hvC : C < v := by dsimp [v]; linarith [le_max_left C R]
  have hh := hC (⟨0,v⟩ : ℂ) hv
  have hh' := Complex.abs_im_le_norm (⟨0,v⟩ : ℂ)
  change |v| ≤ _ at hh'
  linarith [le_abs_self v]

lemma IsCapacityTwoWitness.source_later_image_unbounded
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T t : ℝ≥0) :
    ¬ Bornology.IsBounded ((fun z => G T z - (U T : ℂ)) '' survivingDomain γ (T+t)) := by
  intro hbd
  obtain ⟨C,hC⟩ := hbd.exists_norm_le
  obtain ⟨R,hR⟩ := (isCompact_Icc.image h.1).isBounded.exists_norm_le
  have hb : ∀ s ∈ Icc 0 (T+t), ‖γ s‖ ≤ max R 0 := by
    intro s hs
    exact (hR _ ⟨s,hs,rfl⟩).trans (le_max_left _ _)
  have hlim := h.2.2.2.2.2.2.2.2.2.2.2.1 T
  have hnorm := hlim.norm
  have he : ∀ᶠ z in cocompact ℂ, z ∈ survivingDomain γ T →
      ‖z * (G T z - z)‖ < ‖(2 : ℂ)*(T : ℂ)‖ + 1 := by
    apply eventually_inf_principal.mp
    exact (tendsto_order.mp hnorm).2 _ (lt_add_one _)
  obtain ⟨K,hK,hKe⟩ := mem_cocompact.mp he
  obtain ⟨D,hD⟩ := hK.isBounded.exists_norm_le
  let A : ℝ := ‖(2 : ℂ)*(T : ℂ)‖ + 1
  let y : ℝ := max (max (max R 0) D) (max A (C + |U T|)) + 2
  have hyR : max R 0 < y := by dsimp [y]; linarith [le_max_left (max R 0) D,le_max_left (max (max R 0) D) (max A (C+|U T|))]
  have hyD : D < y := by dsimp [y]; linarith [le_max_right (max R 0) D,le_max_left (max (max R 0) D) (max A (C+|U T|))]
  have hyA : A < y := by dsimp [y]; linarith [le_max_left A (C+|U T|),le_max_right (max (max R 0) D) (max A (C+|U T|))]
  have hyC : C + |U T| + 1 < y := by dsimp [y]; linarith [le_max_right A (C+|U T|),le_max_right (max (max R 0) D) (max A (C+|U T|))]
  have hy0 : 0 < y := lt_of_le_of_lt (le_max_right R 0) hyR
  let z : ℂ := ⟨0,y⟩
  have hnz : ‖z‖ = y := by simp [z,Complex.norm_def,Real.sqrt_mul_self hy0.le]
  have hz : z ∈ survivingDomain γ (T+t) := source_high_vertical_survives (le_max_right R 0) hb hyR
  have hzt : z ∈ survivingDomain γ T := survivingDomain_antitone γ (le_add_of_nonneg_right (show 0 ≤ t from bot_le)) hz
  have hzK : z ∈ Kᶜ := by intro h'; have := hD z h'; rw [hnz] at this; linarith
  have hsmall := hKe hzK hzt
  have hG : ‖G T z‖ ≤ C + |U T| := by
    calc
      ‖G T z‖ = ‖(G T z-(U T : ℂ))+(U T : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖G T z-(U T : ℂ)‖+‖(U T : ℂ)‖ := norm_add_le _ _
      _ ≤ C + |U T| := by gcongr; exact hC _ ⟨z,hz,rfl⟩; simp
  have htri := norm_sub_norm_le z (G T z)
  rw [hnz,norm_sub_rev] at htri
  rw [norm_mul,hnz] at hsmall
  change y*‖G T z-z‖ < A at hsmall
  have hpos : 0 < A := by dsimp [A]; positivity
  nlinarith

lemma IsCapacityTwoWitness.source_surviving_preconnected
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) :
    IsPreconnected (survivingDomain γ t) := by
  have he : F t '' upperHalfPlane = survivingDomain γ t := by
    apply Subset.antisymm
    · rintro _ ⟨w,hw,rfl⟩
      exact h.2.2.2.2.2.2.1 t hw
    · intro z hz
      exact ⟨G t z,h.2.2.2.2.2.1 t hz,h.2.2.2.2.2.2.2.1 t z hz⟩
  rw [← he]
  exact (convex_halfSpace_im_gt 0).isPreconnected.image _ (h.2.2.2.2.1 t).continuousOn

lemma source_stopped_live_transfer
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T t : ℝ≥0) (β : ℝ≥0 → ℂ)
    (hid : ∀ s ∈ Icc 0 t, β s ∈ upperHalfPlane →
      γ (T+s) = F T (β s + (U T : ℂ)))
    (z : ℂ) (hz : z ∈ survivingDomain γ (T+t)) :
    G T z - (U T : ℂ) ∈ survivingDomain β t := by
  let f : ℂ → ℂ := fun z => G T z - (U T : ℂ)
  let D := survivingDomain γ (T+t)
  have hsub : D ⊆ survivingDomain γ T :=
    survivingDomain_antitone γ (le_add_of_nonneg_right (show 0 ≤ t from bot_le))
  have hmap : f '' D ⊆ upperHalfPlane \ β '' Icc 0 t := by
    rintro w ⟨v,hv,rfl⟩
    have hvT := hsub hv
    have him : f v ∈ upperHalfPlane := by
      simpa only [f,upperHalfPlane,mem_ofPred_eq,sub_im,ofReal_im,sub_zero]
        using h.2.2.2.2.2.1 T hvT
    refine ⟨him,?_⟩
    rintro ⟨s,hs,he⟩
    have hβ : β s ∈ upperHalfPlane := he ▸ him
    have hv' : γ (T+s) = v := by
      rw [hid s hs hβ,he]
      simp only [f,sub_add_cancel,h.2.2.2.2.2.2.2.1 T v hvT]
    exact hv.1.2 ⟨T+s,⟨bot_le,by simpa only [add_comm] using add_le_add_left hs.2 T⟩,hv'⟩
  have hconn : IsPreconnected (f '' D) :=
    (h.source_surviving_preconnected (T+t)).image _
      (((h.2.2.2.1 T).continuousOn.mono hsub).sub continuousOn_const)
  have hmem : f z ∈ f '' D := ⟨z,hz,rfl⟩
  refine ⟨hmap hmem,?_⟩
  intro hb
  exact h.source_later_image_unbounded T t
    (hb.subset (hconn.subset_connectedComponentIn hmem hmap))

end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex TopologicalSpace
open scoped Topology NNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.instMeasurableSpaceContinuousMapNNRealComplex_solutions
local instance instBorelSpaceContinuousMapNNRealComplex_solutions : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

lemma source_path_interior_dense_measurable :
    MeasurableSet {β : C(ℝ≥0,ℂ) | SourcePathInteriorDense β} := by
  have he : {β : C(ℝ≥0,ℂ) | SourcePathInteriorDense β} =
      ⋂ n : ℕ, ⋂ m : ℕ, {β | denseSeq ℝ≥0 n < denseSeq ℝ≥0 m →
        ∃ u ∈ Ioo (denseSeq ℝ≥0 n) (denseSeq ℝ≥0 m), 0 < (β u).im} := by
    ext β
    simp only [mem_iInter,mem_ofPred_eq]
    constructor
    · exact fun h _ _ => h _ _
    · intro h s t hst
      obtain ⟨a,ha⟩ := (denseRange_denseSeq ℝ≥0).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hst)
      obtain ⟨b,hb⟩ := (denseRange_denseSeq ℝ≥0).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr ha.2)
      obtain ⟨u,hu,hui⟩ := h a b hb.1
      exact ⟨u,⟨ha.1.trans hu.1,hu.2.trans hb.2⟩,hui⟩
  rw [he]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro m
  by_cases hnm : denseSeq ℝ≥0 n < denseSeq ℝ≥0 m
  · simp only [hnm,true_implies,ofPred_exists]
    apply IsOpen.measurableSet
    apply isOpen_iUnion
    intro u
    by_cases hu : u ∈ Ioo (denseSeq ℝ≥0 n) (denseSeq ℝ≥0 m)
    · simpa only [hu,true_and,Function.comp_apply] using isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_eval_const u))
    · simp [hu]
  · simp [hnm]
end
end SLEExactGauge

end

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsCapacityTwoWitness.radius_le_of_domain_subset
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (s t : ℝ≥0) (hsub : survivingDomain γ s ⊆ survivingDomain γ t)
    (z : ℂ) (hz : z ∈ survivingDomain γ s) :
    fullRadius G s z ≤ fullRadius G t z := by
  have hγ := h.1
  have ht : z ∈ survivingDomain γ t := hsub hz
  have hgs := h.derivative_norm_positive hU s z hz
  have hgt := h.derivative_norm_positive hU t z ht
  have hys := h.imag_positive s z hz
  rcases h with ⟨_,h0,hupper,hG,hF,hGm,hFm,hinv,hinv',hinit,hode,hnorm,htip⟩
  have hfs := ((hF s).differentiableAt (isOpen_upperHalfPlane.mem_nhds (hGm s hz))).hasDerivAt
  have hgsd := ((hG s).differentiableAt ((isOpen_survivingDomain hγ s).mem_nhds hz)).hasDerivAt
  have hgtd := ((hG t).differentiableAt ((isOpen_survivingDomain hγ t).mem_nhds ht)).hasDerivAt
  have hinvder : deriv (F s) (G s z)*deriv (G s) z = 1 := by
    have he : (fun w => F s (G s w)) =ᶠ[𝓝 z] (fun w => w) := by
      filter_upwards [(isOpen_survivingDomain hγ s).mem_nhds hz] with w hw
      exact hinv s w hw
    exact ((hfs.comp z hgsd).congr_of_eventuallyEq he.symm).unique (hasDerivAt_id z)
  have hnp : ‖deriv (F s) (G s z)‖*‖deriv (G s) z‖ = 1 := by
    simpa only [norm_mul,norm_one] using congrArg norm hinvder
  let f : ℂ → ℂ := fun w => G t (F s (diskToHalfPlane (G s z) w))
  have hfd : DifferentiableOn ℂ f (Metric.ball 0 1) :=
    (hG t).comp ((hF s).comp (diskToHalfPlane_differentiable _) (diskToHalfPlane_maps hys))
      (fun w hw => hsub (hFm s (diskToHalfPlane_maps hys hw)))
  have hfm : MapsTo f (Metric.ball 0 1) upperHalfPlane :=
    fun w hw => hGm t (hsub (hFm s (diskToHalfPlane_maps hys hw)))
  have hf0 : f 0 = G t z := by simp only [f,diskToHalfPlane_zero,hinv s z hz]
  have hder : deriv f 0 = deriv (G t) z*deriv (F s) (G s z)*(G s z-star (G s z)) := by
    have hfs' : HasDerivAt (F s) (deriv (F s) (G s z)) (diskToHalfPlane (G s z) 0) := by
      simpa only [diskToHalfPlane_zero] using hfs
    have hgt' : HasDerivAt (G t) (deriv (G t) z) (F s (diskToHalfPlane (G s z) 0)) := by
      simpa only [diskToHalfPlane_zero,hinv s z hz] using hgtd
    have hh := hgt'.comp 0 (hfs'.comp 0 (diskToHalfPlane_deriv_zero (G s z)))
    simpa only [f,Function.comp_def,mul_assoc] using hh.deriv
  have hn : ‖deriv f 0‖ = ‖deriv (G t) z‖*fullRadius G s z := by
    rw [hder,norm_mul,norm_mul,norm_sub_conj_of_im_pos hys,fullRadius]
    have hi : ‖deriv (F s) (G s z)‖ = 1/‖deriv (G s) z‖ := (eq_div_iff hgs.ne').mpr hnp
    rw [hi]
    ring
  have hpos : 0 < ‖deriv f 0‖ := by
    rw [hn,fullRadius]
    positivity
  have hbound := radius_of_halfplane_map (by norm_num : (0:ℝ) < 1) hfd hfm
    (norm_pos_iff.mp hpos)
  rw [hf0,hn] at hbound
  have hy : 0 < (G t z).im := hGm t ht
  have hh := (le_div_iff₀ (show 0 < ‖deriv (G t) z‖*fullRadius G s z by rwa [← hn])).mp hbound
  change _ ≤ 2*(G t z).im/‖deriv (G t) z‖
  exact (le_div_iff₀ hgt).mpr (by nlinarith [hh])

end SLEExactGauge
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

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsCapacityTwoWitness.live_initial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    z ∈ survivingDomain γ 0 := by
  have hl := h.2.2.2.2.2.2.1 0 hz
  have he := h.2.2.2.2.2.2.2.2.1 0 z hz
  rw [h.initial_value _ hl.1.1] at he
  exact he ▸ hl

lemma IsCapacityTwoWitness.green_initial
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (hU0 : U 0 = 0)
    (κ : ℝ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    greenDensity κ U γ G 0 z = initialGreen κ z := by
  have he := greenLogDensity_logCoordinates hU h κ 0 z 0 (h.live_initial hz)
    (by rw [hU0, mul_zero])
  simp only [NNReal.coe_zero] at he
  rw [logLoewnerCoordinates_initial hU h z (h.live_initial hz)] at he
  rw [← he]
  exact greenLogDensity_initial κ z hz

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma boundedSpatialHit_stopping (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    IsStoppingTime a.filtration
      (fun ω : a.samples => (boundedSpatialHit (γ ω) z r T : WithTop ℝ≥0)) := by
  exact a.boundedDiskHit_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r T

 

theorem spatialGreen_expectation_of_level [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (hz : z ∈ upperHalfPlane) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hu : 0 ≤ u) (hlevel : (2 * z.im) * Real.exp (-u) < r) :
    Integrable (fun ω : a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) (P.comap Subtype.val) ∧
    (∫ ω : a.samples, spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) z r ∂(P.comap Subtype.val)) = initialGreen κ z := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  obtain ⟨M, Z, hM, hZ, hMb, hZb, hClosed, hStop, heq, hNoHit⟩ :=
    exists_physical_green_stopping_regular a.brownian hBm a.continuous_B a.zero_B
      κ hκ hκ8 (γ ∘ Subtype.val) a.G a.F (Eventually.of_forall a.witness) z hz u hu
  let σ (n : ℕ) (ω : a.samples) : ℝ≥0 := boundedSpatialHit (γ ω) z r n
  have hσ (n : ℕ) : IsStoppingTime a.filtration (fun ω => (σ n ω : WithTop ℝ≥0)) :=
    a.boundedSpatialHit_stopping z r n
  dsimp only [filtration] at hσ
  let W (ω : a.samples) := spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
    (γ ω) (a.G ω) z r
  let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
  have hMi (n : ℕ) : Integrable (fun ω => M (σ n ω) ω) μ :=
    integrable_condExp.congr (hStop (σ n) (hσ n)).symm
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (σ n ω) ω) atTop (𝓝 (W ω)) := by
    filter_upwards [heq, hNoHit] with ω he hn
    simpa only [he.1, σ, W, Function.comp_apply] using
      (a.witness ω).spatialGreen_limit ((a.continuous_B ω).const_mul _) κ z r hr hy u hlevel hn
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖M (σ n ω) ω‖ ≤ K := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hMb _ ω).1]
    exact (hMb _ ω).2
  have hWi : Integrable W μ := by
    apply Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hMi n).aestronglyMeasurable) hlim) K
    filter_upwards [hlim] with ω hω
    exact le_of_tendsto hω.norm (Eventually.of_forall fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hMb _ ω).1]
      exact (hMb _ ω).2)
  have hI : Tendsto (fun n : ℕ => ∫ ω, M (σ n ω) ω ∂μ) atTop (𝓝 (∫ ω, W ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => K)
      (fun n => (hMi n).aestronglyMeasurable) (integrable_const _) hbound hlim
  have hInt (n : ℕ) : (∫ ω, M (σ n ω) ω ∂μ) = ∫ ω, Z ω ∂μ := by
    rw [integral_congr_ae (hStop (σ n) (hσ n))]
    have : IsFiniteMeasure (μ.trim (hσ n).measurableSpace_le) :=
      isFiniteMeasure_trim (hσ n).measurableSpace_le
    exact integral_condExp (μ := μ) (f := Z) (hσ n).measurableSpace_le
  have h0 : M 0 =ᵐ[μ] fun _ => initialGreen κ z := by
    filter_upwards [heq] with ω he
    rw [he.1 0]
    dsimp only [Function.comp_apply]
    rw [(a.witness ω).physicalGreen_eq_before_spatial
      ((a.continuous_B ω).const_mul _) κ z r hr hy u hlevel 0 bot_le]
    exact (a.witness ω).green_initial ((a.continuous_B ω).const_mul _)
      (by rw [a.zero_B ω, mul_zero]) κ hz
  have hZInt : (∫ ω, Z ω ∂μ) = initialGreen κ z := by
    calc
      _ = ∫ ω, M 0 ω ∂μ := by
        rw [integral_congr_ae (hClosed 0)]
        exact (integral_condExp (μ := μ) (f := Z) (a.filtration.le 0)).symm
      _ = _ := by rw [integral_congr_ae h0, integral_const]; simp
  refine ⟨hWi, ?_⟩
  have he : (∫ ω, W ω ∂μ) = ∫ ω, Z ω ∂μ :=
    tendsto_nhds_unique hI (by simpa only [hInt] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ ω, Z ω ∂μ) atTop (𝓝 (∫ ω, Z ω ∂μ))))
  exact he.trans hZInt

 

theorem spatialGreen_expectation [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im) :
    Integrable (fun ω : a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) (P.comap Subtype.val) ∧
    (∫ ω : a.samples, spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) z r ∂(P.comap Subtype.val)) = initialGreen κ z := by
  have hz : z ∈ upperHalfPlane := hr.trans_le hy
  let u := Real.log (4 * z.im / r)
  have hratio : 0 < 4 * z.im / r := div_pos (mul_pos (by norm_num) hz) hr
  have hu : 0 ≤ u := Real.log_nonneg ((le_div_iff₀ hr).mpr (by linarith))
  have hlev : (2 * z.im) * Real.exp (-u) = r / 2 := by
    dsimp only [u]
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp [(show 0 < z.im from hz).ne']
    ring
  exact a.spatialGreen_expectation_of_level hκ hκ8 z hz r hr hy u hu
    (by rw [hlev]; linarith)

end RegularSLEPresentation
end SLEExactGauge

end


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
-- module Solutions.OAIQ27_SLE.SLE_PhysicalTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Transport for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsCapacityTwoWitness.survivingDomain_injective
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) :
    Function.Injective (survivingDomain γ) := by
  intro s t he
  have hz : F s Complex.I ∈ survivingDomain γ s := by
    rcases h with ⟨hγ,h0,hupper,hG,hF,hGm,hFm,hrest⟩
    exact hFm s (by simp [upperHalfPlane])
  have ht : F s Complex.I ∈ survivingDomain γ t := he ▸ hz
  apply live_radius_unique hU h (F s Complex.I) s t hz ht
  exact le_antisymm (h.radius_le_of_domain_subset hU s t he.subset _ hz)
    (h.radius_le_of_domain_subset hU t s he.symm.subset _ ht)

theorem sourceInteriorTraceDensity_proved : SourceInteriorTraceDensityTarget := by
  intro U γ G F hU h s t hst
  by_contra hnone
  obtain ⟨b,hsb,hbt⟩ := exists_between hst
  obtain ⟨a,hsa,hab⟩ := exists_between hsb
  have hbase : upperHalfPlane \ (γ '' Icc 0 a) = upperHalfPlane \ (γ '' Icc 0 b) := by
    apply Subset.antisymm
    · intro z hz
      refine ⟨hz.1,?_⟩
      rintro ⟨u,hu,huz⟩
      by_cases hua : u ≤ a
      · exact hz.2 ⟨u,⟨hu.1,hua⟩,huz⟩
      · apply hnone
        refine ⟨u,⟨hsa.trans (not_le.mp hua),hu.2.trans_lt hbt⟩,?_⟩
        rw [huz]
        exact hz.1
    · intro z hz
      refine ⟨hz.1,?_⟩
      rintro ⟨u,hu,huz⟩
      exact hz.2 ⟨u,⟨hu.1,hu.2.trans hab.le⟩,huz⟩
  have he : survivingDomain γ a = survivingDomain γ b := by
    unfold survivingDomain
    rw [hbase]
  exact hab.ne (h.survivingDomain_injective hU he)

end SLEExactGauge

end

section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge
lemma source_flow_fence {g dg : ℝ → ℂ} {u : ℝ → ℝ} {a b c δ : ℝ}
    (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt g (dg t) (Ici t) t)
    (hu : ∀ t ∈ Ico a b, |u t-c| ≤ δ)
    (heq : ∀ t ∈ Ico a b, ‖dg t‖ ≤ 2 / ‖g t-(u t:ℂ)‖) :
    ‖g b-(c:ℂ)‖^2 ≤ ‖g a-(c:ℂ)‖^2+4*δ^2+9*(b-a) := by
  let f (t : ℝ) := ‖g t-(c:ℂ)‖^2
  let df (t : ℝ) := 2 * inner ℝ (g t-(c:ℂ)) (dg t)
  have hf : ContinuousOn f (Icc a b) := (hg.sub continuousOn_const).norm.pow 2
  have hdf (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt f (df t) (Ici t) t := (hd t ht |>.sub_const (c:ℂ)).norm_sq
  have hn (t : ℝ) (ht : t ∈ Ico a b) (hh : 4*δ^2 < f t) : df t < 9 := by
    have hr : 2*δ < ‖g t-(c:ℂ)‖ := by
      dsimp [f] at hh
      nlinarith [norm_nonneg (g t-(c:ℂ))]
    have htri : ‖g t-(c:ℂ)‖ ≤ ‖g t-(u t:ℂ)‖+δ := by
      calc
        _ ≤ ‖g t-(u t:ℂ)‖+‖(u t:ℂ)-(c:ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by
          have hc : ‖(u t:ℂ)-(c:ℂ)‖ ≤ δ := by simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hu t ht
          linarith
    have hp : 0 < ‖g t-(u t:ℂ)‖ := by nlinarith
    have hb : ‖g t-(c:ℂ)‖ ≤ 2*‖g t-(u t:ℂ)‖ := by linarith
    have hi := real_inner_le_norm (g t-(c:ℂ)) (dg t)
    have hm := mul_le_mul_of_nonneg_left (heq t ht) (norm_nonneg (g t-(c:ℂ)))
    have hx : ‖g t-(c:ℂ)‖ * (2 / ‖g t-(u t:ℂ)‖) ≤ 4 := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hp).mpr (by linarith)
    change 2 * inner ℝ (g t-(c:ℂ)) (dg t) < 9
    linarith
  have hbound (ε : ℝ) (hε : 0 < ε) :
      f b ≤ f a+4*δ^2+ε+9*(b-a) := by
    apply image_le_of_deriv_right_lt_deriv_boundary hf hdf
      (B := fun t => f a+4*δ^2+ε+9*(t-a)) (B' := fun _ => 9)
      (by nlinarith [sq_nonneg δ])
      (fun t => by convert (((hasDerivAt_id t).sub_const a).const_mul 9).const_add (f a+4*δ^2+ε) using 1 <;> first | rfl | norm_num)
      (fun t ht he => ?_) ⟨hab,le_rfl⟩
    apply hn t ht
    have : 0 ≤ f a := sq_nonneg _
    rw [he]
    nlinarith [ht.1]
  apply le_of_forall_pos_le_add
  intro ε hε
  simpa only [f] using (hbound ε hε).trans_eq (by ring)
end SLEExactGauge

end

section
namespace SLEExactGauge
lemma IsCapacityTwoWitness.short_flow_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) {s T : ℝ≥0} (hs : s ≤ T)
    {z : ℂ} (hz : z ∈ survivingDomain γ T) {c δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ t ∈ Icc s T, |U t-c| ≤ δ) :
    ‖G T z-(c:ℂ)‖^2 ≤ ‖G s z-(c:ℂ)‖^2+4*δ^2+9*((T:ℝ)-s) := by
  have hsub : Icc (s:ℝ) T ⊆ Icc (0:ℝ) T := Icc_subset_Icc_left s.coe_nonneg
  have hb := source_flow_fence (g := fun u => G u.toNNReal z)
    (dg := fun u => 2/(G u.toNNReal z-(U u.toNNReal:ℂ)))
    (u := fun u => U u.toNNReal) (a := (s:ℝ)) (b := (T:ℝ)) (c := c)
    (NNReal.coe_le_coe.mpr hs) hδ ((h.time_continuousOn T z hz).mono hsub)
    (fun u hu => hasDerivWithinAt_Ici_of_Icc hu ((h.time_derivative T z hz u
      (hsub ⟨hu.1,hu.2.le⟩)).mono hsub))
    (fun u hu => hU u.toNNReal ⟨by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ (s.coe_nonneg.trans hu.1)]
      exact hu.1, Real.toNNReal_le_iff_le_coe.mpr hu.2.le⟩)
    (fun u hu => by simp)
  simpa only [Real.toNNReal_coe] using hb

lemma IsCapacityTwoWitness.short_reverse_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) {s T : ℝ≥0} (hs : s ≤ T)
    {z : ℂ} (hz : z ∈ survivingDomain γ T) {c δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ t ∈ Icc s T, |U t-c| ≤ δ) :
    ‖G s z-(c:ℂ)‖^2 ≤ ‖G T z-(c:ℂ)‖^2+4*δ^2+9*((T:ℝ)-s) := by
  have hm (u : ℝ) (hu : u ∈ Icc (0:ℝ) ((T:ℝ)-s)) :
      (T:ℝ)-u ∈ Icc (s:ℝ) T := by constructor <;> linarith [hu.1,hu.2]
  have hm' (u : ℝ) (hu : u ∈ Icc (0:ℝ) ((T:ℝ)-s)) :
      (T:ℝ)-u ∈ Icc (0:ℝ) T := ⟨s.coe_nonneg.trans (hm u hu).1,(hm u hu).2⟩
  have hd (u : ℝ) (hu : u ∈ Icc (0:ℝ) ((T:ℝ)-s)) :
      HasDerivWithinAt (fun v : ℝ => G ((T:ℝ)-v).toNNReal z)
        (-(2/(G ((T:ℝ)-u).toNNReal z-(U ((T:ℝ)-u).toNNReal:ℂ))))
        (Icc 0 ((T:ℝ)-s)) u := by
    have hi : HasDerivWithinAt (fun v : ℝ => (T:ℝ)-v) (-1)
        (Icc 0 ((T:ℝ)-s)) u := by
      convert ((hasDerivAt_id u).const_sub (T:ℝ)).hasDerivWithinAt using 1
      all_goals try with_reducible_and_instances rfl
      rfl
    have hh := (h.time_derivative T z hz _ (hm' u hu)).scomp u hi
      (fun v hv => hm' v hv)
    simpa only [neg_smul, one_smul, Function.comp_def] using hh
  have hc : ContinuousOn (fun u : ℝ => G ((T:ℝ)-u).toNNReal z)
      (Icc (0:ℝ) ((T:ℝ)-s)) :=
    (h.time_continuousOn T z hz).comp (continuousOn_const.sub continuousOn_id) hm'
  have hb := source_flow_fence (g := fun u => G ((T:ℝ)-u).toNNReal z)
    (dg := fun u => -(2/(G ((T:ℝ)-u).toNNReal z-(U ((T:ℝ)-u).toNNReal:ℂ))))
    (u := fun u => U ((T:ℝ)-u).toNNReal) (a := 0) (b := (T:ℝ)-s) (c := c)
    (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hs)) hδ hc
    (fun u hu => hasDerivWithinAt_Ici_of_Icc hu (hd u ⟨hu.1,hu.2.le⟩))
    (fun u hu => hU _ (by
      constructor
      · apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ (hm' u ⟨hu.1,hu.2.le⟩).1]
        exact (hm u ⟨hu.1,hu.2.le⟩).1
      · exact Real.toNNReal_le_iff_le_coe.mpr (hm u ⟨hu.1,hu.2.le⟩).2))
    (fun u hu => by simp)
  simpa only [sub_sub_cancel,sub_zero, Real.toNNReal_coe] using hb
end SLEExactGauge

end

section
namespace SLEExactGauge
lemma IsCapacityTwoWitness.earlier_tip_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) {s T : ℝ≥0} (hs : s ≤ T)
    (ha : γ T ∈ survivingDomain γ s) {δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ t ∈ Icc s T, |U t-U T| ≤ δ) :
    ‖G s (γ T)-(U T:ℂ)‖^2 ≤ 4*δ^2+9*((T:ℝ)-s) := by
  have htip := h.2.2.2.2.2.2.2.2.2.2.2.2
  have hlim := (h.spatial_differentiableAt s (γ T) ha).continuousAt.tendsto.comp (htip T)
  have hleft := ((hlim.sub (tendsto_const_nhds (x := (U T:ℂ)))).norm).pow 2
  have hright : Tendsto (fun y : ℝ =>
      ‖((U T:ℂ)+(y:ℂ)*Complex.I)-(U T:ℂ)‖^2+4*δ^2+9*((T:ℝ)-s))
      (𝓝[>] 0) (𝓝 (4*δ^2+9*((T:ℝ)-s))) := by
    have hc : Continuous (fun y : ℝ =>
      ‖((U T:ℂ)+(y:ℂ)*Complex.I)-(U T:ℂ)‖^2+4*δ^2+9*((T:ℝ)-s)) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hiy : (U T:ℂ)+(y:ℂ)*Complex.I ∈ upperHalfPlane := by
    simpa [upperHalfPlane] using hy
  have hf := h.2.2.2.2.2.2.1 T hiy
  have hi := h.2.2.2.2.2.2.2.2.1 T _ hiy
  convert h.short_reverse_bound hs hf hδ hU using 1 <;> first | rfl | simp only [hi]
end SLEExactGauge

end

section
namespace SLEExactGauge
lemma IsCapacityTwoWitness.fresh_tip_chart_tendsto
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hUc : Continuous U)
    {T : ℝ≥0} (hT : 0 < T)
    (ha : ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s) :
    Tendsto (G T) (𝓝[survivingDomain γ T] (γ T)) (𝓝 (U T:ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ρ,hρ,hosc⟩ := Metric.continuousAt_iff.mp (hUc.continuousAt (x := T)) (ε/10) (by positivity)
  let η : ℝ := min ((T:ℝ)/2) (min (ρ/2) (ε^2/100))
  have hη : 0 < η := lt_min (by exact div_pos (NNReal.coe_pos.mpr hT) (by norm_num))
    (lt_min (by positivity) (by positivity))
  have hηT : η ≤ (T:ℝ)/2 := min_le_left _ _
  have hηρ : η ≤ ρ/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε^2/100 := (min_le_right _ _).trans (min_le_right _ _)
  let s : ℝ≥0 := ⟨(T:ℝ)-η,by linarith [T.coe_nonneg]⟩
  have hs : s < T := by change (T:ℝ)-η < T; linarith
  have hdiff : (T:ℝ)-s = η := by change (T:ℝ)-((T:ℝ)-η)=η; ring
  have hosc' (t : ℝ≥0) (ht : t ∈ Icc s T) : |U t-U T| ≤ ε/10 := by
    have hdist : dist t T < ρ := by
      rw [NNReal.dist_eq,abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr ht.2))]
      have ht' : (T:ℝ)-η ≤ t := NNReal.coe_le_coe.mpr ht.1
      linarith
    simpa only [Real.dist_eq] using (hosc hdist).le
  have hbound := h.earlier_tip_bound hs.le (ha s hs) (by positivity : 0 ≤ ε/10) hosc'
  rw [hdiff] at hbound
  have hnorm : ‖G s (γ T)-(U T:ℂ)‖ < ε/2 := by
    nlinarith [norm_nonneg (G s (γ T)-(U T:ℂ))]
  have hev : ∀ᶠ w in 𝓝 (γ T), ‖G s w-(U T:ℂ)‖ < ε/2 :=
    ((h.spatial_differentiableAt s (γ T) (ha s hs)).continuousAt.sub continuousAt_const).norm
      |>.eventually (isOpen_Iio.mem_nhds hnorm)
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwt
  have hh := h.short_flow_bound hs.le hwt (by positivity : 0 ≤ ε/10) hosc'
  rw [hdiff] at hh
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (G s w-(U T:ℂ)), norm_nonneg (G T w-(U T:ℂ))]
end SLEExactGauge

end

section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge


lemma disk_distance_gt_before_first_hit (γ : ℝ≥0 → ℂ) (hc : Continuous γ)
    (s τ : ℝ≥0) (z : ℂ) (r : ℝ)
    (hfree : Metric.closedBall z r ⊆ survivingDomain γ s)
    (hfirst : ∀ t ∈ Ico s τ, dist (γ t) z ≠ r)
    (t : ℝ≥0) (ht : t < τ) : r < dist (γ t) z := by
  have hold (u : ℝ≥0) (hu : u ≤ s) : r < dist (γ u) z := by
    by_contra hn
    have hu' : γ u ∈ Metric.closedBall z r := by
      simpa only [Metric.mem_closedBall] using not_lt.mp hn
    have hh := hfree hu'
    exact hh.1.2 ⟨u,⟨zero_le,hu⟩,rfl⟩
  by_cases hts : t ≤ s
  · exact hold t hts
  · by_contra hn
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc' (not_le.mp hts).le
      ((hc.dist continuous_const).continuousOn) (show r ∈ Icc (dist (γ t) z) (dist (γ s) z)
        from ⟨not_lt.mp hn,(hold s le_rfl).le⟩)
    exact hfirst u ⟨hu.1,hu.2.trans_lt ht⟩ he

lemma radialAccess_mem_ball (a z : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : dist a z = r) (v : ℝ) (hv : v ∈ Ioc (0:ℝ) 1) :
    (1-v) • a + v • z ∈ Metric.ball z r := by
  rw [Metric.mem_ball,dist_eq_norm]
  have he : (1-v) • a + v • z-z = (1-v) • (a-z) := by module
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hv.2),← dist_eq_norm,ha]
  nlinarith [hv.1]

theorem sourceFirstHitPhysicalAccess : SourceFirstHitPhysicalAccessTarget := by
  intro γ hc s τ z r hr hfree hsτ hhit hfirst hz
  have hprior := disk_distance_gt_before_first_hit γ hc s τ z r hfree hfirst
  have hball : Metric.ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 τ) := by
    intro w hw
    refine ⟨(hfree (Metric.ball_subset_closedBall hw)).1.1,?_⟩
    rintro ⟨t,ht,rfl⟩
    have hlt : dist (γ t) z < r := hw
    rcases lt_or_eq_of_le ht.2 with htτ | rfl
    · exact (not_lt_of_ge (hprior t htτ).le) hlt
    · rw [hhit] at hlt
      exact lt_irrefl _ hlt
  have hcc := (convex_ball z r).isPreconnected.subset_connectedComponentIn
    (Metric.mem_ball_self hr) hball
  have hsurv : Metric.ball z r ⊆ survivingDomain γ τ := by
    intro w hw
    refine ⟨hball hw,?_⟩
    rw [← connectedComponentIn_eq (hcc hw)]
    exact hz.2
  refine ⟨?_,hsurv,?_⟩
  · intro t ht he
    have hh := hprior t ht
    rw [he,hhit] at hh
    exact lt_irrefl _ hh
  · intro v hv
    exact hsurv (radialAccess_mem_ball (γ τ) z r hr hhit v hv)

end SLEExactGauge

end

section
namespace SLEExactGauge
lemma first_hit_tip_survives_earlier (γ : ℝ≥0 → ℂ) (hc : Continuous γ)
    (s τ : ℝ≥0) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hfree : Metric.closedBall z r ⊆ survivingDomain γ s)
    (hhit : dist (γ τ) z = r)
    (hfirst : ∀ t ∈ Ico s τ, dist (γ t) z ≠ r)
    (hz : z ∈ survivingDomain γ τ) :
    ∀ u : ℝ≥0, u < τ → γ τ ∈ survivingDomain γ u := by
  intro u hu
  have hprior := disk_distance_gt_before_first_hit γ hc s τ z r hfree hfirst
  have hclosed : Metric.closedBall z r ⊆ upperHalfPlane \ (γ '' Icc 0 u) := by
    intro w hw
    refine ⟨(hfree hw).1.1,?_⟩
    rintro ⟨t,ht,rfl⟩
    exact (not_le_of_gt (hprior t (ht.2.trans_lt hu))) (Metric.mem_closedBall.mp hw)
  have hcc := (convex_closedBall z r).isPreconnected.subset_connectedComponentIn
    (Metric.mem_closedBall_self hr.le) hclosed
  have hmem : γ τ ∈ Metric.closedBall z r := Metric.mem_closedBall.mpr hhit.le
  refine ⟨hclosed hmem,?_⟩
  rw [← connectedComponentIn_eq (hcc hmem)]
  exact (survivingDomain_antitone γ hu.le hz).2

theorem sourceFirstHitChartAccess_proved : SourceFirstHitChartAccessTarget := by
  intro U γ G F hUc h s τ z r hr hfree hsτ hhit hfirst hz
  have hslt : s < τ := by
    apply lt_of_le_of_ne hsτ
    intro he
    have hm := hfree (Metric.mem_closedBall.mpr hhit.le)
    exact hm.1.2 ⟨τ,⟨zero_le,by rw [he]⟩,rfl⟩
  have hT : 0 < τ := lt_of_le_of_lt (show (0:ℝ≥0) ≤ s from zero_le) hslt
  have ha := first_hit_tip_survives_earlier γ h.1 s τ z r hr hfree hhit hfirst hz
  have hlim := h.fresh_tip_chart_tendsto hUc hT ha
  have hradial := (sourceFirstHitPhysicalAccess γ h.1 s τ z r hr hfree hsτ hhit hfirst hz).2.2
  have hcont : Continuous (fun v : ℝ => (1-v) • γ τ + v • z) := by fun_prop
  have hpath : Tendsto (fun v : ℝ => (1-v) • γ τ + v • z) (𝓝[>] 0)
      (𝓝[survivingDomain γ τ] (γ τ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · have hev : ∀ᶠ v : ℝ in 𝓝[>] 0, v < 1 :=
        (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin,hev] with v hv hv'
      exact hradial v ⟨hv,hv'.le⟩
  simpa only [Function.comp_def,sub_self] using
    (hlim.comp hpath).sub (tendsto_const_nhds (x := (U τ:ℂ)))
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
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.physicalDiskKernelTraceMeasurableSpace
local instance physicalDiskKernelTraceBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
attribute [local instance] OAI.SLEExactGauge.physicalDiskKernelChartMeasurableSpace
local instance physicalDiskKernelChartBorelSpace : BorelSpace C(upperHalfPlane,ℂ) := ⟨rfl⟩

lemma sourcePhysicalDiskKernel_measurable : Measurable sourcePhysicalDiskKernel :=
  Measurable.ite source_physical_disk_kernel_open.measurableSet measurable_const measurable_const

lemma sourcePhysicalDiskKernel_norm_le (p : SourceDiskParameter × C(ℝ≥0,ℂ)) :
    ‖sourcePhysicalDiskKernel p‖ ≤ 1 := by
  unfold sourcePhysicalDiskKernel
  split_ifs <;> norm_num

lemma source_physical_exit_open (z : ℂ) (R : ℝ) :
    IsOpen {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t : ℝ≥0,
      z ∈ survivingDomain p.1 (p.2+t) ∧ R < dist (p.1 (p.2+t)) z} := by
  have ht (t : ℝ≥0) : IsOpen {p : C(ℝ≥0,ℂ) × ℝ≥0 |
      z ∈ survivingDomain p.1 (p.2+t) ∧ R < dist (p.1 (p.2+t)) z} := by
    have hc : Continuous (fun p : C(ℝ≥0,ℂ) × ℝ≥0 => (p.1,p.2+t)) :=
      continuous_fst.prodMk (continuous_snd.add continuous_const)
    exact (source_survival_open.preimage (hc.prodMk continuous_const)).inter
      (isOpen_lt continuous_const ((continuous_eval.comp hc).dist continuous_const))
  simpa only [ofPred_exists] using isOpen_iUnion ht

lemma source_restarted_interior_dense
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgm : Measurable (sourceTracePath γ (fun ω => (hw ω).1)))
    (β : Ω → C(ℝ≥0,ℂ)) (hβm : Measurable β)
    (hlaw : P.map β = P.map (sourceTracePath γ (fun ω => (hw ω).1))) :
    ∀ᵐ ω ∂P, SourcePathInteriorDense (β ω) := by
  apply (ae_map_iff hβm.aemeasurable source_path_interior_dense_measurable).mp
  rw [hlaw]
  apply (ae_map_iff hgm.aemeasurable source_path_interior_dense_measurable).mpr
  exact Eventually.of_forall fun ω => sourceInteriorTraceDensity_proved
    (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω)
    (continuous_const.mul (hc ω)) (hw ω)
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_firsthit_inverse_access
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hUc : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (s τ : ℝ≥0) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hfree : Metric.closedBall z r ⊆ survivingDomain γ s) (hsτ : s ≤ τ)
    (hhit : dist (γ τ) z = r)
    (hfirst : ∀ t ∈ Ico s τ, dist (γ t) z ≠ r)
    (hz : z ∈ survivingDomain γ τ) :
    ∃ η : ℝ → ℂ, ContinuousOn η (Icc 0 1) ∧ η 0 = 0 ∧
      η 1 = G τ z - (U τ : ℂ) ∧
      (∀ v ∈ Ioc 0 1, 0 < (η v).im) ∧
      (∀ v ∈ Ioc 0 1, ‖F τ (η v + (U τ : ℂ))-z‖ ≤ r) := by
  let α : ℝ → ℂ := fun v => (1-v) • γ τ + v • z
  let f : ℝ → ℂ := fun v => G τ (α v) - (U τ : ℂ)
  let η := Function.update f 0 0
  have hα : Continuous α := by dsimp [α]; fun_prop
  have hαD := (sourceFirstHitPhysicalAccess γ h.1 s τ z r hr hfree hsτ hhit hfirst hz).2.2
  have hf : ContinuousOn f (Icc 0 1 \ {0}) := by
    refine ((h.2.2.2.1 τ).continuousOn.comp hα.continuousOn ?_).sub continuousOn_const
    intro v hv
    exact hαD v ⟨lt_of_le_of_ne hv.1.1 (Ne.symm hv.2),hv.1.2⟩
  have hη : ContinuousOn η (Icc 0 1) := by
    apply continuousOn_update_iff.mpr
    refine ⟨hf,fun _ => ?_⟩
    apply (sourceFirstHitChartAccess_proved U γ G F hUc h s τ z r hr hfree hsτ hhit hfirst hz).mono_left
    apply nhdsWithin_mono
    intro v hv
    exact lt_of_le_of_ne hv.1.1 (Ne.symm hv.2)
  have hηv (v : ℝ) (hv : v ∈ Ioc 0 1) : η v = f v :=
    Function.update_of_ne (ne_of_gt hv.1) _ _
  refine ⟨η,hη,by simp [η],?_,?_,?_⟩
  · rw [hηv 1 (by norm_num)]
    simp [f,α]
  · intro v hv
    rw [hηv v hv]
    simpa only [f,α,upperHalfPlane,Set.mem_ofPred_eq,sub_im,ofReal_im,sub_zero] using h.2.2.2.2.2.1 τ (hαD v hv)
  · intro v hv
    rw [hηv v hv]
    simp only [f,sub_add_cancel,h.2.2.2.2.2.2.2.1 τ (α v) (hαD v hv)]
    simpa only [dist_eq_norm] using
      (show dist (α v) z < r from radialAccess_mem_ball (γ τ) z r hr hhit v hv).le

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
lemma source_physical_exit_interior_inclusion
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (β : C(ℝ≥0,ℂ))
    (hdense : SourcePathInteriorDense β)
    (hid : ∀ t : ℝ≥0, β t ∈ upperHalfPlane → γ (T+t) = F T (β t+(U T:ℂ)))
    (z : ℂ) (R : ℝ) (hR : dist (γ T) z ≤ R) :
    (∃ t : ℝ≥0, z ∈ survivingDomain γ (T+t) ∧ R < dist (γ (T+t)) z) →
    ∃ t : ℝ≥0, G T z-(U T:ℂ) ∈ survivingDomain β t ∧
      ∃ _ht : β t ∈ upperHalfPlane, R < ‖F T (β t+(U T:ℂ))-z‖ := by
  rintro ⟨t,hl,he⟩
  have ht : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := le_antisymm (not_lt.mp hn) bot_le
    simp only [ht0,add_zero] at he
    exact (not_lt_of_ge hR) he
  have hc : Continuous (fun u : ℝ≥0 => dist (γ (T+u)) z) :=
    (h.1.comp (continuous_const.add continuous_id)).dist continuous_const
  have hevent : {u : ℝ≥0 | R < dist (γ (T+u)) z} ∈ 𝓝 t :=
    (isOpen_lt continuous_const hc).mem_nhds he
  obtain ⟨b,hbt,hb⟩ := exists_Ioc_subset_of_mem_nhds hevent ⟨0,ht⟩
  obtain ⟨u,hu,hupos⟩ := hdense b t hbt
  have hlu : z ∈ survivingDomain γ (T+u) :=
    survivingDomain_antitone γ (by simpa only [add_comm] using add_le_add_left hu.2.le T) hl
  refine ⟨u,source_stopped_live_transfer h T u β (fun v _ => hid v) z hlu,hupos,?_⟩
  rw [← hid u hupos,← dist_eq_norm]
  exact hb ⟨hu.1,hu.2.le⟩
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.finitePhysicalDiskTargetTraceMeasurableSpace
local instance finitePhysicalDiskTargetTraceBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
attribute [local instance] OAI.SLEExactGauge.finitePhysicalDiskTargetDriverMeasurableSpace
local instance finitePhysicalDiskTargetDriverBorelSpace : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

attribute [local instance] OAI.SLEExactGauge.finitePhysicalDiskTargetChartMeasurableSpace
local instance finitePhysicalDiskTargetChartBorelSpace_r84b6d0_1 : BorelSpace C(upperHalfPlane,ℂ) := ⟨rfl⟩
lemma source_physical_kernel_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (gp : Ω → C(ℝ≥0,ℂ)) (hgm : Measurable gp)
    (Y : SourceDiskParameter) (Ψ : ℂ → ℂ)
    (hΨ : ∀ w : upperHalfPlane, Y.1.1 w = Ψ w)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : P {v | ∃ t : ℝ≥0, Y.1.2 ∈ survivingDomain (gp v) t ∧
      0 < (gp v t).im ∧ Y.2.2 < ‖Ψ (gp v t)-Y.2.1‖} ≤ ENNReal.ofReal b) :
    (∫ p, sourcePhysicalDiskKernel (Y,p) ∂P.map gp) ≤ b := by
  let S : Set Ω := {v | ∃ t : ℝ≥0, Y.1.2 ∈ survivingDomain (gp v) t ∧
      0 < (gp v t).im ∧ Y.2.2 < ‖Ψ (gp v t)-Y.2.1‖}
  have he (v : Ω) : sourcePhysicalDiskKernel (Y,gp v) = S.indicator (fun _ => (1:ℝ)) v := by
    unfold sourcePhysicalDiskKernel
    have hi : (∃ t : ℝ≥0, Y.1.2 ∈ survivingDomain (gp v) t ∧
        ∃ ht : gp v t ∈ upperHalfPlane,
          Y.2.2 < ‖Y.1.1 ⟨gp v t,ht⟩-Y.2.1‖) ↔ v ∈ S := by
      constructor
      · rintro ⟨t,ht,hi,hf⟩
        exact ⟨t,ht,hi,by simpa only [hΨ] using hf⟩
      · rintro ⟨t,ht,hi,hf⟩
        exact ⟨t,ht,hi,by simpa only [hΨ] using hf⟩
    simp only [hi,Set.indicator_apply]
  have hfun : Measurable (fun p : C(ℝ≥0,ℂ) => sourcePhysicalDiskKernel (Y,p)) :=
    sourcePhysicalDiskKernel_measurable.comp (measurable_const.prodMk measurable_id)
  have hS : MeasurableSet S := by
    have hh := measurableSet_lt (measurable_const (a := (0:ℝ))) (hfun.comp hgm)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext v
    change v ∈ S ↔ 0 < sourcePhysicalDiskKernel (Y,gp v)
    rw [he]
    by_cases hv : v ∈ S <;> simp [hv]
  have hKi : (∫ p, sourcePhysicalDiskKernel (Y,p) ∂P.map gp) = (P S).toReal := by
    rw [integral_map hgm.aemeasurable hfun.aestronglyMeasurable]
    simp_rw [he]
    simp only [integral_indicator_const _ hS,smul_eq_mul,mul_one,measureReal_def]
  rw [hKi]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hbound |>.trans
    (le_of_eq (ENNReal.toReal_ofReal hb))

lemma source_firsthit_kernel_mean_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (gp : Ω → C(ℝ≥0,ℂ)) (hgm : Measurable gp)
    (U : ℝ≥0 → ℝ) (hU : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ) (hw : IsCapacityTwoWitness U γ G F)
    (s T : ℝ≥0) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hs : s ≤ T) (hfree : Metric.closedBall z r ⊆ survivingDomain γ s)
    (hhit : dist (γ T) z = r)
    (hfirst : ∀ t ∈ Ico s T, dist (γ t) z ≠ r) (hz : z ∈ survivingDomain γ T)
    (ψ : C(upperHalfPlane,ℂ)) (hψ : ∀ w, ψ w = F T (w+(U T:ℂ)))
    (L b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ upperHalfPlane → InjOn Ψ upperHalfPlane →
      ∀ η : ℝ → ℂ, ContinuousOn η (Icc 0 1) → η 0 = 0 → Ψ (η 1) = z →
      (∀ v ∈ Ioc 0 1, 0 < (η v).im) → (∀ v ∈ Ioc 0 1, ‖Ψ (η v)-z‖ ≤ r) →
      P {v | ∃ t : ℝ≥0, η 1 ∈ survivingDomain (gp v) t ∧
        0 < (gp v t).im ∧ L*r < ‖Ψ (gp v t)-z‖} ≤ ENNReal.ofReal b) :
    (∫ p, sourcePhysicalDiskKernel (((ψ,G T z-(U T:ℂ)),(z,L*r)),p) ∂P.map gp) ≤ b := by
  let Ψ : ℂ → ℂ := fun w => F T (w+(U T:ℂ))
  have hmap : MapsTo (fun w : ℂ => w+(U T:ℂ)) upperHalfPlane upperHalfPlane := by
    intro w hw
    simpa [upperHalfPlane] using hw
  have hΨd : DifferentiableOn ℂ Ψ upperHalfPlane :=
    (hw.2.2.2.2.1 T).comp (differentiable_id.add_const _).differentiableOn hmap
  have hΨi : InjOn Ψ upperHalfPlane := by
    intro a ha b hb he
    have ha' := hw.2.2.2.2.2.2.2.2.1 T (a+(U T:ℂ)) (hmap ha)
    have hb' := hw.2.2.2.2.2.2.2.2.1 T (b+(U T:ℂ)) (hmap hb)
    have hh := congrArg (G T) he
    dsimp only [Ψ] at hh
    rw [ha',hb'] at hh
    exact add_right_cancel hh
  obtain ⟨η,hη,hη0,hη1,hηup,hηpath⟩ := source_firsthit_inverse_access
    hU hw s T z r hr hfree hs hhit hfirst hz
  have hq : Ψ (η 1) = z := by
    rw [hη1]
    simp only [Ψ,sub_add_cancel,hw.2.2.2.2.2.2.2.1 T z hz]
  have hprob := hbound Ψ hΨd hΨi η hη hη0 hq hηup hηpath
  apply source_physical_kernel_mean_le gp hgm _ Ψ hψ b hb
  simpa only [hη1] using hprob

lemma source_physical_exit_measurable {Ω : Type*} [MeasurableSpace Ω]
    (gp : Ω → C(ℝ≥0,ℂ)) (hgp : Measurable gp)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (z : ℂ) (R : ℝ) :
    MeasurableSet {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (gp ω) (τ ω+t) ∧
      R < dist (gp ω (τ ω+t)) z} := by
  have hp : Measurable (fun ω => (gp ω,τ ω)) := hgp.prodMk hτ
  have he : MeasurableSet {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t : ℝ≥0,
      z ∈ survivingDomain p.1 (p.2+t) ∧ R < dist (p.1 (p.2+t)) z} :=
    (source_physical_exit_open z R).measurableSet
  have hh := he.preimage hp
  simpa only [Set.preimage_ofPred_eq] using hh

theorem sourceFinitePhysicalDisk_proved : SourceFinitePhysicalDiskTarget := by
  intro κ hκ hκ8
  obtain ⟨C,c,hC,hc,hbound⟩ := source_interior_disk_unnormalized κ hκ hκ8
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω m P hP B hB hm hBc γ G F hw τ hτ z r hr A hA hgeom L hL
  let : IsProbabilityMeasure P := hP
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  obtain ⟨Φ,hΦm,hΦeq,hΦ⟩ := sourceStoppedTraceLaw κ (by linarith) hκ8 B hB hm hBc γ G F hw
  have hgm : Measurable gp := by
    have he : gp = fun ω => Φ (sourceDriverPath B hBc ω) := funext fun ω => (hΦeq ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable _ hm)
  let ν := P.map gp
  let : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  have hγsle : IsOrdinaryChordalSLE κ γ P :=
    ⟨fun t => (continuous_eval_const t).measurable.comp hgm,
      B,hB,Eventually.of_forall fun ω => ⟨G ω,F ω,hw ω⟩⟩
  obtain ⟨hlaw,hid⟩ := hΦ τ hτ
  let rp := sourceRestartDriverPath B hBc τ
  let β (ω : Ω) := Φ (rp ω)
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable hm hBc (stopping_time_measurable_nnreal hτ)))
  have hβm : Measurable β := hΦm.comp hrm
  have hβlaw : P.map β = ν := by simpa only [Measure.restrict_univ,measure_univ,one_smul] using hlaw univ MeasurableSet.univ
  have hdense : ∀ᵐ ω ∂P, SourcePathInteriorDense (β ω) :=
    source_restarted_interior_dense B hBc κ γ G F hw hgm β hβm hβlaw
  let ξ (ω : Ω) :=
    (if z ∈ survivingDomain (γ ω) (τ ω) then G ω (τ ω) z else 0) -
      (Real.sqrt κ * B (τ ω) ω : ℝ)
  let Y (ω : Ω) : SourceDiskParameter :=
    ((sourceStoppedInversePath B κ γ G F hw τ ω,ξ ω),(z,L*r))
  have hξm : Measurable[hτ.measurableSpace] ξ := by
    have hGm := source_killedChart_stopped_measurable hm hBc κ γ G F hw z τ hτ
    have hBm := measurable_stoppedValue
      ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).isStronglyProgressive_of_continuous hBc) hτ
    exact hGm.sub (Complex.measurable_ofReal.comp (measurable_const.mul hBm))
  have hYm : Measurable[hτ.measurableSpace] Y :=
    ((source_stopped_inversePath_measurable B hm hBc κ γ G F hw τ hτ).prodMk hξm).prodMk measurable_const
  let H (ω : Ω) := sourcePhysicalDiskKernel (Y ω,β ω)
  let K (ω : Ω) := ∫ p, sourcePhysicalDiskKernel (Y ω,p) ∂ν
  have hHm : Measurable H := sourcePhysicalDiskKernel_measurable.comp
    ((hYm.mono hτ.measurableSpace_le le_rfl).prodMk hβm)
  have hHi : Integrable H P :=
    (integrable_const (1:ℝ)).mono' hHm.aestronglyMeasurable
      (Eventually.of_forall fun ω => sourcePhysicalDiskKernel_norm_le (Y ω,β ω))
  have hcond : P[H | hτ.measurableSpace] =ᵐ[P] K :=
    source_parameter_condExp hτ.measurableSpace_le hβm hYm hlaw sourcePhysicalDiskKernel
      sourcePhysicalDiskKernel_measurable sourcePhysicalDiskKernel_norm_le
  have hmean (ω : Ω) (hω : ω ∈ A) : K ω ≤ C*L^(-c) := by
    obtain ⟨s,hs,hfree,hhit,hfirst,hz⟩ := hgeom ω hω
    dsimp only [K,Y,ξ]
    rw [ite_eq_left hz]
    apply source_firsthit_kernel_mean_le gp hgm (fun t => Real.sqrt κ*B t ω)
      (continuous_const.mul (hBc ω)) (γ ω) (G ω) (F ω) (hw ω)
      s (τ ω) z r hr hs hfree hhit hfirst hz _ (fun _ => rfl)
      L (C*L^(-c)) (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
    intro Ψ hΨd hΨi η hη hη0 hq hηup hηpath
    exact hbound Ω m P hP γ hγsle Ψ hΨd hΨi z r hr η 1 (by norm_num)
      hη hη0 hq hηup hηpath L hL
  let E : Set Ω := {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) (τ ω+t) ∧
      L*r < dist (γ ω (τ ω+t)) z}
  let f : Ω → ℝ := E.indicator (fun _ => 1)
  have hE : MeasurableSet E :=
    source_physical_exit_measurable gp hgm τ (stopping_time_measurable_nnreal hτ) z (L*r)
  have hfi : Integrable f P := (integrable_const (1:ℝ)).indicator hE
  have hAi : Integrable (A.indicator f) P := hfi.indicator (hτ.measurableSpace_le _ hA)
  have hAH : Integrable (A.indicator H) P := hHi.indicator (hτ.measurableSpace_le _ hA)
  have hdom : A.indicator f ≤ᵐ[P] A.indicator H := by
    filter_upwards [hid,hdense] with ω hωid hωdense
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
      by_cases he : ω ∈ E
      · obtain ⟨s,hs,hfree,hhit,hfirst,hz⟩ := hgeom ω hω
        have hR : dist (γ ω (τ ω)) z ≤ L*r := by rw [hhit]; nlinarith
        obtain ⟨t,ht,htH,hfar⟩ := source_physical_exit_interior_inclusion (hw ω) (τ ω) (β ω)
          hωdense hωid z (L*r) hR he
        have hkernel : H ω = 1 := by
          apply ite_eq_left
          refine ⟨t,?_,htH,?_⟩
          · simpa only [Y,ξ,ite_eq_left hz] using ht
          · exact hfar
        simp only [f,Set.indicator_of_mem he,hkernel,le_refl]
      · simp only [f,Set.indicator_of_notMem he]
        dsimp [H,sourcePhysicalDiskKernel]
        split_ifs <;> norm_num
    · simp only [Set.indicator_of_notMem hω,le_refl]
  have hmono := condExp_mono (m := hτ.measurableSpace) hAi hAH hdom
  filter_upwards [hmono,condExp_indicator hfi hA,condExp_indicator hHi hA,hcond] with ω hm hf hH hK
  intro hω
  rw [hf,hH,Set.indicator_of_mem hω,Set.indicator_of_mem hω,hK] at hm
  exact hm.trans (hmean ω hω)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma sourceStop_indicator_tendsto (τ : WithTop ℝ≥0) (v : ℝ)
    (hzero : τ = ⊤ → v = 0) :
    Tendsto (fun n : ℕ => if τ ≤ (n : ℝ≥0) then v else 0) atTop (𝓝 v) := by
  by_cases ht : τ = ⊤
  · simp only [ht, hzero ht, ite_self]
    exact tendsto_const_nhds
  obtain ⟨t, rfl⟩ := WithTop.ne_top_iff_exists.mp ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (⌈(t : ℝ)⌉₊)] with n hn
  have htn : t ≤ (n : ℝ≥0) := by exact_mod_cast (Nat.le_of_ceil_le hn)
  simp only [WithTop.coe_le_coe, ite_eq_left htn]

lemma source_unbounded_setIntegral_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 mΩ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hz : ∀ ω, τ ω = ⊤ → f ω = 0 ∧ g ω = 0)
    (hloc : ∀ (n : ℕ) (A : Set Ω),
      MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace] A →
      (∀ ω ∈ A, τ ω = (sourceStopTruncate τ n ω : WithTop ℝ≥0)) →
      (∫ ω in A, f ω ∂μ) ≤ ∫ ω in A, g ω ∂μ)
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, f ω ∂μ) ≤ ∫ ω in A, g ω ∂μ := by
  have hAm (n : ℕ) : MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace]
      (A ∩ {ω | τ ω ≤ (n : ℝ≥0)}) := by
    have hh := hτ.measurableSet_inter_le (isStoppingTime_const ℱ (n : ℝ≥0)) A hA
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext ω
    exact sourceStopTruncate_coe τ n ω
  have hset (n : ℕ) :
      (∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, f ω ∂μ) ≤
        ∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, g ω ∂μ := by
    apply hloc n _ (hAm n)
    intro ω hω
    rw [sourceStopTruncate_coe, min_eq_left hω.2]
  have hlim (v : Ω → ℝ) (hv : Integrable v μ) (hzero : ∀ ω, τ ω = ⊤ → v ω = 0) :
      Tendsto (fun n : ℕ => ∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, v ω ∂μ) atTop
        (𝓝 (∫ ω in A, v ω ∂μ)) := by
    have he (n : ℕ) : (∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, v ω ∂μ) =
        ∫ ω in A, {ω | τ ω ≤ (n : ℝ≥0)}.indicator v ω ∂μ :=
      (setIntegral_indicator (μ := μ) (s := A) (f := v)
        ((ℱ.le (n : ℝ≥0)) _ (hτ n))).symm
    simp_rw [he]
    apply tendsto_integral_of_dominated_convergence (fun ω => ‖v ω‖)
      (fun n => (hv.indicator ((ℱ.le (n : ℝ≥0)) _ (hτ n))).integrableOn.aestronglyMeasurable)
      hv.norm.integrableOn
    · intro n
      exact Eventually.of_forall fun ω => norm_indicator_le_norm_self _ _
    · apply Eventually.of_forall
      intro ω
      apply (sourceStop_indicator_tendsto (τ ω) (v ω) (hzero ω)).congr'
      apply Eventually.of_forall
      intro n
      by_cases hn : τ ω ≤ (n : WithTop ℝ≥0) <;> simp [Set.indicator, hn]
  exact le_of_tendsto_of_tendsto' (hlim f hf (fun ω ht => (hz ω ht).1))
    (hlim g hg (fun ω ht => (hz ω ht).2)) hset

end
end SLEExactGauge

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
namespace SLEExactGauge
lemma source_unbounded_conditional_bound_on
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 mΩ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAfin : ∀ ω ∈ A, τ ω ≠ ⊤)
    (f : Ω → ℝ) (hf : Integrable f μ) (b : ℝ)
    (hloc : ∀ (n : ℕ) (E : Set Ω),
      MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace] E →
      E ⊆ A ∩ {ω | τ ω ≤ (n : ℝ≥0)} →
      (∫ ω in E, f ω ∂μ) ≤ ∫ _ in E, b ∂μ) :
    ∀ᵐ ω ∂μ, ω ∈ A → μ[f | hτ.measurableSpace] ω ≤ b := by
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  have hfi : Integrable (A.indicator f) μ := hf.indicator hAm
  have hbi : Integrable (A.indicator (fun _ => b)) μ := (integrable_const _).indicator hAm
  have hbound : μ[A.indicator f | hτ.measurableSpace] ≤ᵐ[μ] A.indicator (fun _ => b) := by
    apply source_condExp_le_of_setIntegral_le hτ.measurableSpace_le hfi hbi
      (stronglyMeasurable_const.indicator hA)
    intro S hS
    apply source_unbounded_setIntegral_le ℱ hτ _ _ hfi hbi ?_ ?_ S hS
    · intro ω ht
      have hnot : ω ∉ A := fun hω => hAfin ω hω ht
      simp only [Set.indicator_of_notMem hnot, and_self]
    · intro n E hE hτE
      have hen (ω : Ω) (hω : ω ∈ E) : τ ω ≤ (n : ℝ≥0) := by
        rw [hτE ω hω,sourceStopTruncate_coe]
        exact min_le_right _ _
      have hAn : MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace]
          (A ∩ {ω | τ ω ≤ (n : ℝ≥0)}) := by
        have hh := hτ.measurableSet_inter_le (isStoppingTime_const ℱ (n : ℝ≥0)) A hA
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        exact sourceStopTruncate_coe τ n ω
      have heq : E ∩ A = E ∩ (A ∩ {ω | τ ω ≤ (n : ℝ≥0)}) := by
        ext ω
        exact ⟨fun h => ⟨h.1,h.2,hen ω h.1⟩,fun h => ⟨h.1,h.2.1⟩⟩
      have hEA : MeasurableSet[(sourceStopTruncate_stopping ℱ hτ n).measurableSpace] (E ∩ A) := by
        rw [heq]
        exact hE.inter hAn
      rw [setIntegral_indicator hAm,setIntegral_indicator hAm]
      exact hloc n (E ∩ A) hEA (fun ω hω => ⟨hω.2,hen ω hω.1⟩)
  filter_upwards [hbound,condExp_indicator hf hA] with ω hb he
  intro hω
  rw [he,Set.indicator_of_mem hω,Set.indicator_of_mem hω] at hb
  exact hb
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.physicalClosedPrefixTraceMeasurableSpace
local instance physicalClosedPrefixTraceBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

lemma source_physical_closed_prefix_isClosed (z : ℂ) (R : ℝ) (v : ℝ≥0) :
    IsClosed {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t ∈ Icc (0 : ℝ≥0) v,
      R ≤ dist (p.1 (p.2+t)) z} := by
  let E := {p : (C(ℝ≥0,ℂ) × ℝ≥0) × Icc (0 : ℝ≥0) v |
    R ≤ dist (p.1.1 (p.1.2+p.2)) z}
  have he : IsClosed E := by
    apply isClosed_le continuous_const
    exact (continuous_eval.comp ((continuous_fst.fst).prodMk
      (continuous_fst.snd.add (continuous_subtype_val.comp continuous_snd)))).dist continuous_const
  have hc := isClosedMap_fst_of_compactSpace E he
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨t,ht,he⟩
    exact ⟨(p,⟨t,ht⟩),he,rfl⟩
  · rintro ⟨⟨p',t⟩,ht,rfl⟩
    exact ⟨t,t.2,ht⟩

lemma source_physical_closed_exit_measurableSet (z : ℂ) (R : ℝ) :
    MeasurableSet {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t : ℝ≥0,
      z ∈ survivingDomain p.1 (p.2+t) ∧ R ≤ dist (p.1 (p.2+t)) z} := by
  have heq : {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ t : ℝ≥0,
      z ∈ survivingDomain p.1 (p.2+t) ∧ R ≤ dist (p.1 (p.2+t)) z} =
      {p : C(ℝ≥0,ℂ) × ℝ≥0 | ∃ q : ℚ,
        z ∈ survivingDomain p.1 (p.2+(q:ℝ).toNNReal) ∧
        ∃ t ∈ Icc (0 : ℝ≥0) (q:ℝ).toNNReal, R ≤ dist (p.1 (p.2+t)) z} := by
    ext p
    constructor
    · rintro ⟨t,hl,he⟩
      have ho : IsOpen {u : ℝ≥0 | z ∈ survivingDomain p.1 (p.2+u)} :=
        source_survival_open.preimage
          ((continuous_const.prodMk (continuous_const.add continuous_id)).prodMk continuous_const)
      obtain ⟨b,htb,hb⟩ := exists_Ico_subset_of_mem_nhds (ho.mem_nhds hl) ⟨t+1,by simp⟩
      obtain ⟨q,htq,hqb⟩ := exists_rat_btwn (show (t:ℝ) < b from htb)
      have hqn : 0 ≤ (q:ℝ) := le_trans t.coe_nonneg htq.le
      have htu : t ≤ (q:ℝ).toNNReal := by
        change (t:ℝ) ≤ ((q:ℝ).toNNReal:ℝ)
        rw [Real.coe_toNNReal _ hqn]
        exact htq.le
      have hub : (q:ℝ).toNNReal < b := by
        change ((q:ℝ).toNNReal:ℝ) < (b:ℝ)
        rw [Real.coe_toNNReal _ hqn]
        exact hqb
      exact ⟨q,hb ⟨htu,hub⟩,t,⟨bot_le,htu⟩,he⟩
    · rintro ⟨q,hl,t,ht,he⟩
      refine ⟨t,?_,he⟩
      exact survivingDomain_antitone p.1 (by simpa only [add_comm] using add_le_add_left ht.2 p.2) hl
  rw [heq]
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  have ho : IsOpen {p : C(ℝ≥0,ℂ) × ℝ≥0 |
      z ∈ survivingDomain p.1 (p.2+(q:ℝ).toNNReal)} :=
    source_survival_open.preimage
      ((continuous_fst.prodMk (continuous_snd.add continuous_const)).prodMk continuous_const)
  exact ho.measurableSet.inter (source_physical_closed_prefix_isClosed z R (q:ℝ).toNNReal).measurableSet

lemma source_physical_closed_exit_measurable {Ω : Type*} [MeasurableSpace Ω]
    (gp : Ω → C(ℝ≥0,ℂ)) (hgp : Measurable gp)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (z : ℂ) (R : ℝ) :
    MeasurableSet {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (gp ω) (τ ω+t) ∧
      R ≤ dist (gp ω (τ ω+t)) z} := by
  have hp : Measurable (fun ω => (gp ω,τ ω)) := hgp.prodMk hτ
  have hh := (source_physical_closed_exit_measurableSet z R).preimage hp
  simpa only [Set.preimage_ofPred_eq] using hh
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace SLEExactGauge
lemma source_physical_slack_large (C c L : ℝ) (_hC : 0 ≤ C) (hL : 0 < L) :
    C * (L/2)^(-c) ≤ ((C+1)*2^c)*L^(-c) := by
  have he : (L/2)^(-c) = 2^c*L^(-c) := by
    rw [Real.div_rpow hL.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    simp only [div_inv_eq_mul,mul_comm]
  rw [he]
  have hh := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) c
  have hh' := Real.rpow_nonneg hL.le (-c)
  nlinarith [mul_nonneg hh hh']

lemma source_physical_slack_small (C c L : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hL : 0 < L) (hL2 : L ≤ 2) :
    1 ≤ ((C+1)*2^c)*L^(-c) := by
  have h2 : (0:ℝ) < 2^c := Real.rpow_pos_of_pos (by norm_num) _
  have hrec : 2^(-c) ≤ L^(-c) := Real.rpow_le_rpow_of_nonpos hL hL2 (by linarith)
  have he : (2:ℝ)^c * 2^(-c) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    simp
  have hh := mul_le_mul_of_nonneg_left hrec h2.le
  rw [he] at hh
  have hp : 0 ≤ 2^c * L^(-c) := le_trans (by norm_num) hh
  nlinarith [mul_nonneg hC hp]
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.physicalDiskTargetTraceMeasurableSpace
local instance physicalDiskTargetTraceBorelSpace_r84b6d0_1 : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
attribute [local instance] OAI.SLEExactGauge.physicalDiskTargetDriverMeasurableSpace
local instance physicalDiskTargetDriverBorelSpace : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩


theorem sourcePhysicalDisk_proved : SourcePhysicalDiskTarget := by
  intro κ hκ hκ8
  obtain ⟨C,c,hC,hc,hbound⟩ := sourceFinitePhysicalDisk_proved κ hκ hκ8
  refine ⟨(C+1)*2^c,c,mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _),hc,?_⟩
  intro Ω m P hP B hB hm hBc γ G F hw τ hτ z r hr A hA hgeom L hL
  let : IsProbabilityMeasure P := hP
  let ℱ := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  obtain ⟨Φ,hΦm,hΦeq,hΦ⟩ := sourceStoppedTraceLaw κ (by linarith) hκ8 B hB hm hBc γ G F hw
  have hgm : Measurable gp := by
    have he : gp = fun ω => Φ (sourceDriverPath B hBc ω) := funext fun ω => (hΦeq ω).symm
    rw [he]
    exact hΦm.comp (source_path_measurable _ hm)
  let H := {ω | τ ω ≠ ⊤ ∧ ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) ((τ ω).untopD 0+t) ∧
    L*r ≤ dist (γ ω ((τ ω).untopD 0+t)) z}
  let f : Ω → ℝ := H.indicator (fun _ => 1)
  have hH : MeasurableSet H := by
    have hfin : MeasurableSet {ω | τ ω ≠ ⊤} := (measurableSet_eq_fun hτ.measurable' measurable_const).compl
    have he := source_physical_closed_exit_measurable gp hgm (fun ω => (τ ω).untopD 0)
      (hτ.measurable'.untopD 0) z (L*r)
    exact hfin.inter he
  have hf : Integrable f P := (integrable_const (1:ℝ)).indicator hH
  have hfeq : f = (fun ω => if ω ∈ H then (1:ℝ) else 0) := by
    funext ω
    exact Set.indicator_apply _ _ _
  suffices hh : ∀ᵐ ω ∂P, ω ∈ A → P[f | hτ.measurableSpace] ω ≤ ((C+1)*2^c)*L^(-c) by
    simpa only [hfeq,H,Set.mem_ofPred_eq] using hh
  by_cases hL2 : L ≤ 2
  · have hfle : f ≤ᵐ[P] fun _ => (1:ℝ) := Eventually.of_forall fun ω => by
      dsimp [f,Set.indicator]; split_ifs <;> norm_num
    have hmono := condExp_mono (m := hτ.measurableSpace) hf (integrable_const (1:ℝ)) hfle
    have he := condExp_const (μ := P) hτ.measurableSpace_le (1:ℝ)
    filter_upwards [hmono] with ω hω
    intro _
    rw [he] at hω
    exact hω.trans (source_physical_slack_small C c L hC.le hc (by linarith) hL2)
  have hAfin : ∀ ω ∈ A, τ ω ≠ ⊤ := by
    intro ω hω
    obtain ⟨T,s,hT,_⟩ := hgeom ω hω
    rw [hT]
    exact WithTop.coe_ne_top
  apply source_unbounded_conditional_bound_on ℱ hτ A hA hAfin f hf _
  intro n E hE hEA
  let ρ := sourceStopTruncate τ n
  have hρ : IsStoppingTime ℱ (fun ω => (ρ ω : WithTop ℝ≥0)) := sourceStopTruncate_stopping ℱ hτ n
  have heq (ω : Ω) (hω : ω ∈ E) : τ ω = (ρ ω : WithTop ℝ≥0) := by
    rw [sourceStopTruncate_coe,min_eq_left (hEA hω).2]
  have hgeomE : ∀ ω ∈ E, ∃ s : ℝ≥0, s ≤ ρ ω ∧
      Metric.closedBall z r ⊆ survivingDomain (γ ω) s ∧ dist (γ ω (ρ ω)) z = r ∧
      (∀ t ∈ Ico s (ρ ω), dist (γ ω t) z ≠ r) ∧ z ∈ survivingDomain (γ ω) (ρ ω) := by
    intro ω hω
    obtain ⟨T,s,hT,hs,hfree,hhit,hfirst,hz⟩ := hgeom ω (hEA hω).1
    have hTr : T = ρ ω := WithTop.coe_injective (hT.symm.trans (heq ω hω))
    exact ⟨s,hTr ▸ hs,hfree,hTr ▸ hhit,hTr ▸ hfirst,hTr ▸ hz⟩
  have hLhalf : 1 ≤ L/2 := by linarith
  have hlocal := hbound Ω m P hP B hB hm hBc γ G F hw ρ hρ z r hr E hE hgeomE (L/2) hLhalf
  let K := {ω | ∃ t : ℝ≥0, z ∈ survivingDomain (γ ω) (ρ ω+t) ∧
    (L/2)*r < dist (γ ω (ρ ω+t)) z}
  let g : Ω → ℝ := K.indicator (fun _ => 1)
  have hK : MeasurableSet K := source_physical_exit_measurable gp hgm ρ
    (stopping_time_measurable_nnreal hρ) z ((L/2)*r)
  have hg : Integrable g P := (integrable_const (1:ℝ)).indicator hK
  have hgeq : g = (fun ω => if ω ∈ K then (1:ℝ) else 0) := by
    funext ω
    exact Set.indicator_apply _ _ _
  have hfg : ∀ ω ∈ E, f ω ≤ g ω := by
    intro ω hω
    by_cases hh : ω ∈ H
    · obtain ⟨hfin,t,ht,hd⟩ := (show τ ω ≠ ⊤ ∧ ∃ t : ℝ≥0,
        z ∈ survivingDomain (γ ω) ((τ ω).untopD 0+t) ∧
        L*r ≤ dist (γ ω ((τ ω).untopD 0+t)) z from hh)
      have hτr : (τ ω).untopD 0 = ρ ω := by rw [heq ω hω,WithTop.untopD_coe]
      have hk : ω ∈ K := ⟨t,by rwa [hτr] at ht,by rw [hτr] at hd; nlinarith⟩
      simp only [f,g,Set.indicator_of_mem hh,Set.indicator_of_mem hk,le_refl]
    · simp only [f,Set.indicator_of_notMem hh]
      dsimp [g,Set.indicator]; split_ifs <;> norm_num
  have hEm : MeasurableSet E := hρ.measurableSpace_le _ hE
  have hi1 : (∫ ω in E, f ω ∂P) ≤ ∫ ω in E, g ω ∂P :=
    setIntegral_mono_on hf.integrableOn hg.integrableOn hEm hfg
  have hi2 : (∫ ω in E, g ω ∂P) ≤ ∫ ω in E, C*(L/2)^(-c) ∂P := by
    rw [← setIntegral_condExp hρ.measurableSpace_le hg hE]
    apply setIntegral_mono_on_ae integrable_condExp.integrableOn (integrable_const _).integrableOn hEm
    filter_upwards [hlocal] with ω hω
    simpa only [hgeq,K,Set.mem_ofPred_eq] using hω
  have hi3 : (∫ ω in E, C*(L/2)^(-c) ∂P) ≤ ∫ ω in E, ((C+1)*2^c)*L^(-c) ∂P := by
    exact setIntegral_mono_on (integrable_const _).integrableOn (integrable_const _).integrableOn hEm
      (fun _ _ => source_physical_slack_large C c L hC.le (by linarith))
  exact hi1.trans (hi2.trans hi3)

end
end SLEExactGauge
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
namespace SLEExactGauge
 

lemma source_halfplane_map_local_bound {f : ℂ → ℂ} {z w : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hεr : ε ≤ r / 2)
    (hd : DifferentiableOn ℂ f (ball z r))
    (hm : MapsTo f (ball z r) upperHalfPlane) (hw : dist w z ≤ ε) :
    dist (f w) (f z) ≤ 4 * (f z).im * ε / r := by
  have hz : z ∈ ball z r := mem_ball_self hr
  have hwr : w ∈ ball z r := mem_ball.mpr (hw.trans_lt (by linarith))
  have hy : 0 < (f z).im := hm hz
  have hden (v : ℂ) (hv : v ∈ ball z r) : f v - star (f z) ≠ 0 := by
    intro he
    have hx := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hx
    have hvy : 0 < (f v).im := hm hv
    linarith
  let g := fun v => (f v - f z) / (f v - star (f z))
  have hg0 : g z = 0 := by simp [g]
  have hgd : DifferentiableOn ℂ g (ball z r) :=
    (hd.sub_const _).div (hd.sub_const _) hden
  have hgm : MapsTo g (ball z r) (closedBall (g z) 1) := by
    intro v hv
    rw [hg0, mem_closedBall_zero_iff]
    exact (upper_mobius_norm_lt_one (hm hv) hy).le
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hgm hwr
  rw [hg0, dist_zero_right] at hsch
  have hsch' : ‖g w‖ ≤ ε / r :=
    hsch.trans (by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      div_le_div_of_nonneg_right hw hr.le)
  have hmult : ‖f w - f z‖ ≤ (ε / r) * ‖f w - star (f z)‖ := by
    simpa only [g, norm_div, div_le_iff₀ (norm_pos_iff.mpr (hden w hwr))] using hsch'
  have hn : ‖f z - star (f z)‖ = 2 * (f z).im := by
    rw [Complex.star_def, Complex.sub_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hy), Complex.norm_I, mul_one]
  have htri : ‖f w - star (f z)‖ ≤ ‖f w - f z‖ + 2 * (f z).im := by
    rw [← hn]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have ha : 0 ≤ ε / r := div_nonneg hε hr.le
  have hb : ε / r ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith)
  have hmain := hmult.trans (mul_le_mul_of_nonneg_left htri ha)
  rw [dist_eq_norm]
  have hp := mul_nonneg (sub_nonneg.mpr hb) (norm_nonneg (f w - f z))
  calc
    ‖f w - f z‖ ≤ 4 * (f z).im * (ε / r) := by nlinarith
    _ = _ := by ring
end SLEExactGauge

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
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.sourceApproachComplexPathMeasurable
local instance sourceApproachComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma sourceApproachKernel_measurable (ε r : ℝ) : Measurable (sourceApproachKernel ε r) := by
  have he (p : ℂ × C(ℝ≥0, ℂ)) :
      (∃ t : ℝ≥0, dist (p.2 t) p.1 < 8 * p.1.im * ε / r) ↔
      ∃ n : ℕ, dist (p.2 (denseSeq ℝ≥0 n)) p.1 < 8 * p.1.im * ε / r := by
    constructor
    · intro h
      exact (denseRange_denseSeq ℝ≥0).exists_mem_open
        (isOpen_lt (p.2.continuous.dist continuous_const) continuous_const) h
    · rintro ⟨n, hn⟩
      exact ⟨_, hn⟩
  apply Measurable.ite _ measurable_const measurable_const
  simp_rw [he]
  rw [ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_lt
    (((continuous_eval_const _).comp continuous_snd).dist continuous_fst).measurable
    ((((continuous_im.comp continuous_fst).const_mul 8).mul_const ε).div_const r).measurable

lemma sourceApproachKernel_norm_le (ε r : ℝ) (p : ℂ × C(ℝ≥0, ℂ)) :
    ‖sourceApproachKernel ε r p‖ ≤ 1 := by
  unfold sourceApproachKernel
  split_ifs <;> norm_num

lemma sourceApproachKernel_zero {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    {p : ℂ × C(ℝ≥0, ℂ)} (hp : p.1.im ≤ 0) : sourceApproachKernel ε r p = 0 := by
  apply ite_eq_right
  rintro ⟨t, ht⟩
  have hh : 8 * p.1.im * ε / r ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hp) hε) hr
  exact not_lt_of_ge (dist_nonneg.trans' hh) ht

lemma source_rpow_scale (p y ε r R : ℝ) (hy : 0 < y) (he : 0 < ε)
    (hr : 0 < r) (hR : 0 < R) :
    (2 * y) ^ (-p) * (8 * y * ε / r) ^ p =
      (4 * R / r) ^ p * ε ^ p * R ^ (-p) := by
  rw [Real.rpow_def_of_pos (by positivity : 0 < 2*y),
    Real.rpow_def_of_pos (by positivity : 0 < 8*y*ε/r),
    Real.rpow_def_of_pos (by positivity : 0 < 4*R/r),
    Real.rpow_def_of_pos he, Real.rpow_def_of_pos hR,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_div (by positivity) hr.ne', Real.log_div (by positivity) hr.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hy.ne',
    Real.log_mul (by positivity : 8*y ≠ 0) he.ne',
    Real.log_mul (by norm_num : (8:ℝ) ≠ 0) hy.ne',
    Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hR.ne']
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ)=2^3 by norm_num, Real.log_pow]; ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; ring
  rw [h8, h4]
  ring
end
end SLEExactGauge

end


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

end
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_liveIndicator_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (ε : ℝ) (hy : ε ≤ z.im) :
    Measurable (fun ω : a.samples =>
      if liveSpatialHitTime (γ ω) z ε = ⊤ then (0 : ℝ) else 1) := by
  classical
  have hτ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z ε) :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z ε
  have hK := measurable_stoppedValue
    (source_killedChart_progressive a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z) hτ
  have hKm : Measurable (fun ω : a.samples =>
      (if z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z ε).untopA
        then a.G ω (spatialHitTime (γ ω) z ε).untopA z else 0 : ℂ)) :=
    hK.mono hτ.measurableSpace_le le_rfl
  have htop : MeasurableSet {ω : a.samples | spatialHitTime (γ ω) z ε = ⊤} :=
    measurableSet_eq_fun (hτ.measurable.mono hτ.measurableSpace_le le_rfl) measurable_const
  have hl : MeasurableSet {ω : a.samples |
      0 < (if z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z ε).untopA
        then a.G ω (spatialHitTime (γ ω) z ε).untopA z else 0 : ℂ).im} :=
    measurableSet_lt measurable_const (Complex.measurable_im.comp hKm)
  have hmo : Measurable (fun ω : a.samples =>
      if spatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else
        if 0 < (if z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z ε).untopA
          then a.G ω (spatialHitTime (γ ω) z ε).untopA z else 0 : ℂ).im then 1 else 0) :=
    Measurable.ite htop measurable_const (Measurable.ite hl measurable_const measurable_const)
  convert hmo using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  have hs : ε ≤ dist (γ ω 0) z := by
    rw [(a.witness ω).2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  rw [liveSpatialHitTime_eq (a.trace_continuous ω) z ε hs]
  by_cases ht : spatialHitTime (γ ω) z ε = ⊤
  · simp only [ite_eq_left ht, ite_true]
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [ite_eq_right ht, ite_eq_right ht, ← hv]
    change (if (if z ∈ survivingDomain (γ ω) v then (v : WithTop ℝ≥0) else ⊤) = ⊤
      then (0:ℝ) else 1) =
      (if 0 < (if z ∈ survivingDomain (γ ω) v then a.G ω v z else 0 : ℂ).im then 1 else 0)
    by_cases hz : z ∈ survivingDomain (γ ω) v
    · simp only [ite_eq_left hz, WithTop.coe_ne_top, ite_false,
        ite_eq_left ((a.witness ω).imag_positive v z hz)]
    · simp only [ite_eq_right hz, ite_true, Complex.zero_im, lt_self_iff_false, ite_false]

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma sourceApproachConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < sourceApproachConstant κ := by
  exact mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num))
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by positivity) _)

attribute [local instance] OAI.SLEExactGauge.windowBoundsApproachPathMeasurableSpace
local instance windowBoundsApproachPathBorelSpace_r84b6d0_1 : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_kernel_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgm : Measurable (sourceTracePath γ (fun ω => (hw ω).1)))
    (ζ : ℂ) (hζ : ζ ∈ upperHalfPlane) (ε r R : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (hy : 8 * ε ≤ r)
    (hsmall : Real.exp 1 * (512 * Real.pi) * ε ≤ r)
    (hR : 0 < R) (hRb : R ≤ (128 * Real.pi) * r) :
    (∫ p, sourceApproachKernel ε r (ζ, p) ∂P.map (sourceTracePath γ (fun ω => (hw ω).1))) ≤
      sourceApproachConstant κ * ε ^ codimension κ *
        (R ^ (-codimension κ) * (Real.sin (Complex.arg ζ)) ^ greenExponent κ) := by
  have hypos : 0 < ζ.im := hζ
  let δ := 8 * ζ.im * ε / r
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδy : δ ≤ ζ.im := by
    apply (div_le_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hy (show 0 ≤ ζ.im from hζ.le)]
  have hδsmall : 1 ≤ Real.log ((2 * ζ.im) / ((128 * Real.pi) * δ)) := by
    apply (Real.le_log_iff_exp_le (by positivity)).mpr
    apply (le_div_iff₀ (by positivity : 0 < (128 * Real.pi) * δ)).mpr
    calc
      Real.exp 1 * ((128 * Real.pi) * δ) =
          (2 * ζ.im) * (Real.exp 1 * (512 * Real.pi) * ε) / r := by dsimp [δ]; ring
      _ ≤ (2 * ζ.im) * r / r :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall (by positivity)) hr.le
      _ = 2 * ζ.im := mul_div_cancel_right₀ _ hr.ne'
  have hb := euclidean_approach hB κ hκ hκ8 γ G F (Eventually.of_forall hw)
    ζ hζ δ hδ hδy hδsmall
  let S : Set Ω := {ω | ∃ t : ℝ≥0, dist (γ ω t) ζ < δ}
  have hS : MeasurableSet S := by
    have hh := measurableSet_lt (measurable_const (a := (0:ℝ)))
      ((sourceApproachKernel_measurable ε r).comp ((measurable_const (a := ζ)).prodMk hgm))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    change (∃ t : ℝ≥0, dist (γ ω t) ζ < δ) ↔ 0 <
      (if ∃ t : ℝ≥0, dist (γ ω t) ζ < δ then (1:ℝ) else 0)
    split_ifs <;> simp_all
  have hint : (∫ p, sourceApproachKernel ε r (ζ, p)
      ∂P.map (sourceTracePath γ (fun ω => (hw ω).1))) = (P S).toReal := by
    have hfun : Measurable (fun p : C(ℝ≥0, ℂ) => sourceApproachKernel ε r (ζ, p)) :=
      (sourceApproachKernel_measurable ε r).comp (measurable_const.prodMk measurable_id)
    calc
      _ = ∫ ω, sourceApproachKernel ε r (ζ, sourceTracePath γ (fun ω => (hw ω).1) ω) ∂P :=
        integral_map hgm.aemeasurable hfun.aestronglyMeasurable
      _ = _ := ?_

    change (∫ ω, S.indicator (fun _ => (1:ℝ)) ω ∂P) = _
    simp only [integral_indicator_const _ hS, smul_eq_mul, mul_one, measureReal_def]
  rw [hint]
  apply hb.trans
  have hsin : 0 ≤ Real.sin (Complex.arg ζ) := by
    rw [Complex.sin_arg]
    exact div_nonneg hζ.le (norm_nonneg _)
  have hC : 0 ≤ uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ :=
    (mul_pos (uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num))
      (Real.rpow_pos_of_pos (by positivity) _)).le
  have hp : (4 * R / r) ^ codimension κ ≤ (512 * Real.pi) ^ codimension κ := by
    apply Real.rpow_le_rpow (by positivity) _ (codimension_pos κ hκ8).le
    apply (div_le_iff₀ hr).mpr
    nlinarith [hRb]
  have heq := source_rpow_scale (codimension κ) ζ.im ε r R hζ hε hr hR
  dsimp only [initialGreen, δ]
  calc
    _ = (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
        ((2 * ζ.im) ^ (-codimension κ) * (8 * ζ.im * ε / r) ^ codimension κ) *
        (Real.sin (Complex.arg ζ)) ^ greenExponent κ := by ring
    _ = (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
        ((4 * R / r) ^ codimension κ * ε ^ codimension κ * R ^ (-codimension κ)) *
        (Real.sin (Complex.arg ζ)) ^ greenExponent κ := by rw [heq]
    _ ≤ (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
        ((512 * Real.pi) ^ codimension κ * ε ^ codimension κ * R ^ (-codimension κ)) *
        (Real.sin (Complex.arg ζ)) ^ greenExponent κ := by
      gcongr
    _ = _ := by dsimp [sourceApproachConstant]; ring

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_liveSpatialHitTime_ne_top_iff (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) :
    liveSpatialHitTime γ z r ≠ ⊤ ↔
      ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ r := by
  simp only [liveSpatialHitTime]
  split_ifs with h
  · simp only [ne_eq, WithTop.coe_ne_top, not_false_eq_true, true_iff]
    exact h
  · simp only [ne_eq, not_true_eq_false, false_iff]
    exact h

 

lemma source_live_contact_restarts
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (z : ℂ) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (he : ε ≤ r / 2) (hy : r ≤ z.im)
    (τ : ℝ≥0) (hτ : spatialHitTime γ z r = τ)
    (s : ℝ≥0) (hs : z ∈ survivingDomain γ s) (hd : dist (γ s) z ≤ ε) :
    τ < s ∧ z ∈ survivingDomain γ τ ∧ γ s ∈ survivingDomain γ τ ∧
      dist (G τ (γ s) - (U τ : ℂ)) (G τ z - (U τ : ℂ)) <
        8 * (G τ z).im * ε / r := by
  have hs0 : r ≤ dist (γ 0) z := by
    rw [h.2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have her : ε < r := by linarith
  have hτs : τ < s := WithTop.coe_lt_coe.mp (hτ ▸
    spatialHitTime_lt_of_dist_lt h.1 z r hs0 s (hd.trans_lt her))
  have hl : z ∈ survivingDomain γ τ := survivingDomain_antitone γ hτs.le hs
  have hfree : ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 τ) := by
    intro w hw
    refine ⟨ball_subset_upperHalfPlane hy hw, ?_⟩
    rintro ⟨t, ht, rfl⟩
    have hh := spatialHitTime_lt_of_dist_lt h.1 z r hs0 t (mem_ball.mp hw)
    rw [hτ] at hh
    exact not_lt_of_ge ht.2 (WithTop.coe_lt_coe.mp hh)
  have hb := ball_subset_survivingDomain hr hl hfree
  have hgs := hb (mem_ball.mpr (hd.trans_lt her))
  refine ⟨hτs, hl, hgs, ?_⟩
  rw [dist_sub_right]
  have hbound := source_halfplane_map_local_bound hr hε.le he
    ((h.2.2.2.1 τ).mono hb) (fun w hw => h.2.2.2.2.2.1 τ (hb hw)) hd
  apply hbound.trans_lt
  apply (div_lt_div_iff_of_pos_right hr).mpr
  have hp : 0 < (G τ z).im * ε := mul_pos (h.2.2.2.2.2.1 τ hl) hε
  nlinarith

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_liveIndicator_zero_of_coarse_top
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (z : ℂ) (r ε : ℝ)
    (he : ε < r) (hy : r ≤ z.im) (htop : spatialHitTime γ z r = ⊤) :
    (if liveSpatialHitTime γ z ε = ⊤ then (0:ℝ) else 1) = 0 := by
  have hs0 : r ≤ dist (γ 0) z := by
    rw [h.2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have hl : liveSpatialHitTime γ z ε = ⊤ := by
    by_contra hn
    obtain ⟨s, _, hd⟩ := (source_liveSpatialHitTime_ne_top_iff γ z ε).mp hn
    have hh := spatialHitTime_lt_of_dist_lt h.1 z r hs0 s (hd.trans_lt he)
    rw [htop] at hh
    exact not_lt_of_ge le_top hh
  simp only [ite_eq_left hl]

lemma source_restarted_kernel_dominates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (z : ℂ) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (he : ε ≤ r / 2) (hy : r ≤ z.im)
    (τ : ℝ≥0) (hτ : spatialHitTime γ z r = τ)
    (p : C(ℝ≥0, ℂ))
    (hfwd : ∀ t : ℝ≥0, γ (τ + t) ∈ survivingDomain γ τ →
      p t = G τ (γ (τ + t)) - (U τ : ℂ)) :
    (if liveSpatialHitTime γ z ε = ⊤ then (0:ℝ) else 1) ≤
      sourceApproachKernel ε r ((if z ∈ survivingDomain γ τ then G τ z else 0) - (U τ : ℂ), p) := by
  by_cases ht : liveSpatialHitTime γ z ε = ⊤
  · simp only [ite_eq_left ht, sourceApproachKernel]
    split_ifs <;> norm_num
  · obtain ⟨s, hs, hd⟩ := (source_liveSpatialHitTime_ne_top_iff γ z ε).mp ht
    obtain ⟨hτs, hl, hgs, hb⟩ := source_live_contact_restarts h z r ε hr hε he hy τ hτ s hs hd
    have heq : τ + (s - τ) = s := add_tsub_cancel_of_le hτs.le
    have hf := hfwd (s - τ) (by simpa only [heq] using hgs)
    simp only [heq] at hf
    have hhit : ∃ t : ℝ≥0, dist (p t) (G τ z - (U τ : ℂ)) <
        8 * (G τ z - (U τ : ℂ)).im * ε / r := by
      refine ⟨s - τ, ?_⟩
      simpa only [hf, Complex.sub_im, Complex.ofReal_im, sub_zero] using hb
    simp only [ite_eq_right ht, ite_eq_left hl, sourceApproachKernel, ite_eq_left hhit, le_refl]

attribute [local instance] OAI.SLEExactGauge.windowBoundsLivePathMeasurableSpace
local instance windowBoundsLivePathBorelSpace_r84b6d0_1 : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_stopped_kernel_mean_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgm : Measurable (sourceTracePath γ (fun ω => (hw ω).1)))
    {U' : ℝ≥0 → ℝ} {γ' : ℝ≥0 → ℂ} {G' F' : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U') (hw' : IsCapacityTwoWitness U' γ' G' F')
    (z : ℂ) (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r)
    (hy : 8 * ε ≤ r) (hsmall : Real.exp 1 * (512 * Real.pi) * ε ≤ r)
    (τ : ℝ≥0) (hτ : spatialHitTime γ' z r = τ) :
    (∫ p, sourceApproachKernel ε r
      ((if z ∈ survivingDomain γ' τ then G' τ z else 0) - (U' τ : ℂ), p)
      ∂P.map (sourceTracePath γ (fun ω => (hw ω).1))) ≤
      sourceApproachConstant κ * ε ^ codimension κ * spatialGreenWeight κ U' γ' G' z r := by
  have ht : spatialHitTime γ' z r ≠ ⊤ := by rw [hτ]; exact WithTop.coe_ne_top
  have he : (spatialHitTime γ' z r).untopD 0 = τ := by rw [hτ]; rfl
  by_cases hz : z ∈ survivingDomain γ' τ
  · have hζ : G' τ z - (U' τ : ℂ) ∈ upperHalfPlane := by
      change 0 < (G' τ z - (U' τ : ℂ)).im
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hw'.imag_positive τ z hz
    have hRb : fullRadius G' τ z ≤ (128 * Real.pi) * r := by
      have hh := hw'.radius_le_past_distance hU τ z hz τ le_rfl
      rwa [dist_comm z, spatialHitTime_mem hw'.1 z r τ hτ] at hh
    have hb := source_kernel_mean_bound hB κ hκ hκ8 γ G F hw hgm
      (G' τ z - (U' τ : ℂ)) hζ ε r (fullRadius G' τ z) hε hr hy hsmall
      (hw'.fullRadius_positive hU τ z hz) hRb
    simpa only [ite_eq_left hz, spatialGreenWeight, ite_eq_right ht, he, greenDensity, ite_eq_left hz] using hb
  · have hk (p : C(ℝ≥0, ℂ)) : sourceApproachKernel ε r ((0:ℂ) - (U' τ : ℂ), p) = 0 :=
      sourceApproachKernel_zero hε.le hr.le (by simp)
    simp only [hk, integral_zero, spatialGreenWeight, ite_eq_right ht, he,
      greenDensity, ite_eq_right hz, mul_zero, le_refl]

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] OAI.SLEExactGauge.windowBoundsIntegralPathMeasurableSpace
local instance windowBoundsIntegralPathBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
attribute [local instance] OAI.SLEExactGauge.windowBoundsDriverPathMeasurableSpace
local instance windowBoundsDriverPathBorelSpace : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma source_finite_approach_setIntegral_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (z : ℂ) (ε r : ℝ)
    (hε : 0 < ε) (hr : 0 < r) (he : ε ≤ r / 2) (hy : r ≤ z.im)
    (h8 : 8 * ε ≤ r) (hsmall : Real.exp 1 * (512 * Real.pi) * ε ≤ r)
    (σ : a.samples → ℝ≥0)
    (hσ : IsStoppingTime a.filtration (fun ω => (σ ω : WithTop ℝ≥0)))
    (A : Set a.samples) (hA : MeasurableSet[hσ.measurableSpace] A)
    (hAσ : ∀ ω ∈ A, spatialHitTime (γ ω) z r = (σ ω : WithTop ℝ≥0)) :
    (∫ ω in A, (if liveSpatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else 1)
      ∂P.comap Subtype.val) ≤
    ∫ ω in A, sourceApproachConstant κ * ε ^ codimension κ * spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r ∂P.comap Subtype.val := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  let gp := sourceTracePath (fun ω : a.samples => γ ω) (fun ω => (a.witness ω).1)
  have hgm : Measurable gp := source_path_measurable gp (fun t =>
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl)
  let ν := μ.map gp
  let : IsProbabilityMeasure ν := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)
  obtain ⟨Φ, hΦm, _, hΦ⟩ := sourceStoppedTraceLaw_forward κ hκ hκ8
    a.B a.brownian a.measurable_B a.continuous_B (fun ω : a.samples => γ ω)
    a.G a.F a.witness
  obtain ⟨hlaw, hfwd⟩ := hΦ σ hσ
  let rp := sourceRestartDriverPath a.B a.continuous_B σ
  let X (ω : a.samples) := Φ (rp ω)
  have hrm : Measurable rp := source_path_measurable rp (fun t =>
    (measurable_pi_apply t).comp (brownianRestart_measurable a.measurable_B a.continuous_B
      (stopping_time_measurable_nnreal hσ)))
  have hXm : Measurable X := hΦm.comp hrm
  let Y (ω : a.samples) : ℂ :=
    (if z ∈ survivingDomain (γ ω) (σ ω) then a.G ω (σ ω) z else 0) -
      (Real.sqrt κ * a.B (σ ω) ω : ℝ)
  have hYm : Measurable[hσ.measurableSpace] Y := by
    have hGm := measurable_stoppedValue
      (source_killedChart_progressive a.measurable_B a.continuous_B κ
        (fun ω : a.samples => γ ω) a.G a.F a.witness z) hσ
    have hBm := measurable_stoppedValue
      ((Filtration.stronglyAdapted_natural (fun t => (a.measurable_B t).stronglyMeasurable)).isStronglyProgressive_of_continuous a.continuous_B) hσ
    exact hGm.sub (Complex.measurable_ofReal.comp (measurable_const.mul hBm))
  let H (ω : a.samples) := sourceApproachKernel ε r (Y ω, X ω)
  let K (ω : a.samples) := ∫ p, sourceApproachKernel ε r (Y ω, p) ∂ν
  have hHmeas : Measurable H := (sourceApproachKernel_measurable ε r).comp
    ((hYm.mono hσ.measurableSpace_le le_rfl).prodMk hXm)
  have hHi : Integrable H μ :=
    (integrable_const (1:ℝ)).mono' hHmeas.aestronglyMeasurable
      (Eventually.of_forall (fun ω => sourceApproachKernel_norm_le ε r (Y ω, X ω)))
  have hcond : μ[H | hσ.measurableSpace] =ᵐ[μ] K :=
    source_parameter_condExp hσ.measurableSpace_le hXm hYm hlaw
      (sourceApproachKernel ε r) (sourceApproachKernel_measurable ε r)
      (sourceApproachKernel_norm_le ε r)
  have hKi : Integrable K μ := integrable_condExp.congr hcond
  let W (ω : a.samples) := sourceApproachConstant κ * ε ^ codimension κ * spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r
  have hτ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r) :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  have hWm : Measurable W := measurable_const.mul
    ((source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z r hτ).mono hτ.measurableSpace_le le_rfl)
  have hWi : Integrable W μ := by
    apply Integrable.of_bound hWm.aestronglyMeasurable
      (sourceApproachConstant κ * ε ^ codimension κ * r ^ (-codimension κ))
    apply Eventually.of_forall
    intro ω
    have hb := (a.witness ω).spatialGreenWeight_bound
      (continuous_const.mul (a.continuous_B ω)) hκ hκ8 hr z hy
    have hc : 0 ≤ sourceApproachConstant κ * ε ^ codimension κ :=
      mul_nonneg (sourceApproachConstant_pos κ hκ hκ8).le (Real.rpow_nonneg hε.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hb.1)]
    exact mul_le_mul_of_nonneg_left hb.2 hc
  have hfi : Integrable (fun ω : a.samples => if liveSpatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else 1) μ := by
    apply Integrable.of_bound (source_liveIndicator_measurable a z ε (by linarith)).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro ω
    split_ifs <;> norm_num
  have hAm : MeasurableSet A := hσ.measurableSpace_le A hA
  calc
    _ ≤ ∫ ω in A, H ω ∂μ := by
      apply integral_mono_ae hfi.integrableOn hHi.integrableOn
      filter_upwards [ae_restrict_of_ae hfwd, ae_restrict_mem hAm] with ω hf hωA
      exact source_restarted_kernel_dominates (a.witness ω) z r ε hr hε he hy
        (σ ω) (hAσ ω hωA) (X ω) hf
    _ = ∫ ω in A, K ω ∂μ := by
      have : IsFiniteMeasure (μ.trim hσ.measurableSpace_le) := isFiniteMeasure_trim _
      rw [← integral_congr_ae (ae_restrict_of_ae hcond)]
      exact (setIntegral_condExp hσ.measurableSpace_le hHi hA).symm
    _ ≤ ∫ ω in A, W ω ∂μ := by
      apply integral_mono_ae hKi.integrableOn hWi.integrableOn
      filter_upwards [ae_restrict_mem hAm] with ω hωA
      exact source_stopped_kernel_mean_bound a.brownian κ hκ hκ8
        (fun ω : a.samples => γ ω) a.G a.F a.witness hgm
        (continuous_const.mul (a.continuous_B ω)) (a.witness ω)
        z ε r hε hr h8 hsmall (σ ω) (hAσ ω hωA)

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
universe u_source_approach


lemma source_approach_small_scale (ε r : ℝ) (hε : 0 < ε)
    (h : ε ≤ min (1/16) (1/(Real.exp 1 * (512 * Real.pi))) * r) :
    0 < r ∧ ε ≤ r/2 ∧ 8*ε ≤ r ∧ Real.exp 1 * (512 * Real.pi) * ε ≤ r := by
  have hA : 0 < Real.exp 1 * (512 * Real.pi) := by positivity
  have hq : 0 < min (1/16:ℝ) (1/(Real.exp 1 * (512 * Real.pi))) := by positivity
  have hr : 0 < r := by
    by_contra! hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hq.le hn
    linarith
  have h16 : ε ≤ r/16 := by
    apply h.trans
    have hh := mul_le_mul_of_nonneg_right
      (min_le_left (1/16:ℝ) (1/(Real.exp 1 * (512 * Real.pi)))) hr.le
    nlinarith
  refine ⟨hr, by linarith, by linarith, ?_⟩
  have hqA := (le_div_iff₀ hA).mp
    (min_le_right (1/16:ℝ) (1/(Real.exp 1 * (512 * Real.pi))))
  have hh := mul_le_mul_of_nonneg_right hqA hr.le
  have hhh := mul_le_mul_of_nonneg_left h hA.le
  nlinarith only [hh, hhh]

 

theorem sourceConditionalApproach_proved : SourceConditionalApproachTarget := by
  intro κ hκ hκ8
  refine ⟨sourceApproachConstant κ, sourceApproachConstant_pos κ hκ hκ8,
    min (1/16) (1/(Real.exp 1 * (512 * Real.pi))), by positivity, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by norm_num)
  intro Ω mΩ P hP γ a z ε r hε hεq hy
  let : IsProbabilityMeasure P := hP
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  obtain ⟨hr, he, h8, hsmall⟩ := source_approach_small_scale ε r hε hεq
  let τ (ω : a.samples) := spatialHitTime (γ ω) z r
  have hτ : IsStoppingTime a.filtration τ :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  refine ⟨hτ, ?_⟩
  let f (ω : a.samples) : ℝ := if liveSpatialHitTime (γ ω) z ε = ⊤ then 0 else 1
  let W (ω : a.samples) := spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r
  let g (ω : a.samples) := sourceApproachConstant κ * ε ^ codimension κ * W ω
  have hf : Integrable f μ := by
    apply Integrable.of_bound (source_liveIndicator_measurable a z ε (by linarith)).aestronglyMeasurable 1
    apply Eventually.of_forall
    intro ω
    dsimp [f]
    split_ifs <;> norm_num
  have hWm : Measurable[hτ.measurableSpace] W :=
    source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z r hτ
  have hgm : Measurable[hτ.measurableSpace] g := measurable_const.mul hWm
  have hg : Integrable g μ := by
    apply Integrable.of_bound (hgm.mono hτ.measurableSpace_le le_rfl).aestronglyMeasurable
      (sourceApproachConstant κ * ε ^ codimension κ * r ^ (-codimension κ))
    apply Eventually.of_forall
    intro ω
    have hb := (a.witness ω).spatialGreenWeight_bound
      (continuous_const.mul (a.continuous_B ω)) hκ hκ8 hr z hy
    have hc : 0 ≤ sourceApproachConstant κ * ε ^ codimension κ :=
      mul_nonneg (sourceApproachConstant_pos κ hκ hκ8).le (Real.rpow_nonneg hε.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hb.1)]
    exact mul_le_mul_of_nonneg_left hb.2 hc
  change μ[f | hτ.measurableSpace] ≤ᵐ[μ] g
  apply source_condExp_le_of_setIntegral_le hτ.measurableSpace_le hf hg hgm.stronglyMeasurable
  apply source_unbounded_setIntegral_le a.filtration hτ f g hf hg
  · intro ω ht
    constructor
    · exact source_liveIndicator_zero_of_coarse_top (a.witness ω) z r ε (by linarith) hy ht
    · change sourceApproachConstant κ * ε ^ codimension κ * spatialGreenWeight κ _ _ _ z r = 0
      change spatialHitTime (γ ω) z r = ⊤ at ht
      simp only [spatialGreenWeight, ite_eq_left ht, mul_zero]
  · intro n A hA hAτ
    exact source_finite_approach_setIntegral_bound hκ hκ8 a z ε r hε hr he hy h8 hsmall
      (sourceStopTruncate τ n) (sourceStopTruncate_stopping a.filtration hτ n) A hA hAτ

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
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

lemma source_nested_stops_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 mΩ) (τ σ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ) (hτσ : τ ≤ σ)
    (M : ℝ≥0 → Ω → ℝ) (Z V W : Ω → ℝ) (hZ : Integrable Z μ)
    (hStop : ∀ (ρ : Ω → ℝ≥0) (hρ : IsStoppingTime ℱ (fun ω => (ρ ω : WithTop ℝ≥0))),
      (fun ω => M (ρ ω) ω) =ᵐ[μ] μ[Z | hρ.measurableSpace])
    (K : ℝ) (hbound : ∀ t ω, ‖M t ω‖ ≤ K)
    (hVlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (sourceStopTruncate τ n ω) ω) atTop (𝓝 (V ω)))
    (hWlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (sourceStopTruncate σ n ω) ω) atTop (𝓝 (W ω)))
    (hzero : ∀ ω, τ ω = ⊤ → V ω = 0 ∧ W ω = 0)
    (hterm : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, τ ω ≤ (t : WithTop ℝ≥0) → M (sourceStopTruncate τ t ω) ω = V ω) :
    μ[W | hτ.measurableSpace] =ᵐ[μ] V := by
  let τn := sourceStopTruncate τ
  let σn := sourceStopTruncate σ
  have hτn (t : ℝ≥0) := sourceStopTruncate_stopping ℱ hτ t
  have hσn (t : ℝ≥0) := sourceStopTruncate_stopping ℱ hσ t
  have hVi (t : ℝ≥0) : Integrable (fun ω => M (τn t ω) ω) μ :=
    integrable_condExp.congr (hStop (τn t) (hτn t)).symm
  have hWi (t : ℝ≥0) : Integrable (fun ω => M (σn t ω) ω) μ :=
    integrable_condExp.congr (hStop (σn t) (hσn t)).symm
  have hVm (n : ℕ) : StronglyMeasurable[hτ.measurableSpace]
      (μ[Z | (hτn n).measurableSpace]) := by
    apply stronglyMeasurable_condExp.mono
    apply IsStoppingTime.measurableSpace_mono
    intro ω
    dsimp only
    rw [sourceStopTruncate_coe]
    exact min_le_left _ _
  have hVmeas : AEStronglyMeasurable[hτ.measurableSpace] V μ := by
    refine ⟨fun ω => limUnder atTop (fun n : ℕ => μ[Z | (hτn n).measurableSpace] ω),
      (by
        let : MeasurableSpace Ω := hτ.measurableSpace
        exact StronglyMeasurable.limUnder hVm), ?_⟩
    filter_upwards [hVlim, ae_all_iff.mpr (fun n : ℕ => hStop (τn n) (hτn n))] with ω hω he
    have hf : (fun n : ℕ => μ[Z | (hτn n).measurableSpace] ω) =
        (fun n : ℕ => M (τn n ω) ω) := funext fun n => (he n).symm
    rw [hf]
    exact hω.limUnder_eq.symm
  have hVint : Integrable V μ := by
    apply Integrable.of_bound (hVmeas.mono hτ.measurableSpace_le) K
    filter_upwards [hVlim] with ω hω
    exact le_of_tendsto hω.norm (Eventually.of_forall fun n => hbound _ _)
  have hWint : Integrable W μ := by
    apply Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop
      (fun n : ℕ => (hWi n).aestronglyMeasurable) hWlim) K
    filter_upwards [hWlim] with ω hω
    exact le_of_tendsto hω.norm (Eventually.of_forall fun n => hbound _ _)
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hWint
    (fun _ _ _ => hVint.integrableOn) _ hVmeas
  intro A hA _
  have hAm (m : ℕ) : MeasurableSet[(hτn m).measurableSpace]
      (A ∩ {ω | τ ω ≤ (m : ℝ≥0)}) := by
    have hh := hτ.measurableSet_inter_le (isStoppingTime_const ℱ (m : ℝ≥0)) A hA
    convert hh using 1
    · congr 1
      funext ω
      exact sourceStopTruncate_coe τ m ω
  have hset (m : ℕ) : (∫ ω in A ∩ {ω | τ ω ≤ (m : ℝ≥0)}, V ω ∂μ) =
      ∫ ω in A ∩ {ω | τ ω ≤ (m : ℝ≥0)}, W ω ∂μ := by
    let E := A ∩ {ω | τ ω ≤ (m : ℝ≥0)}
    have hI : Tendsto (fun n : ℕ => ∫ ω in E, M (σn n ω) ω ∂μ) atTop
        (𝓝 (∫ ω in E, W ω ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => K)
        (fun n => (hWi n).integrableOn.aestronglyMeasurable)
        (integrable_const _) _ (ae_restrict_of_ae hWlim)
      intro n
      exact Eventually.of_forall fun ω => hbound _ _
    have he : ∀ᶠ n : ℕ in atTop, (∫ ω in E, M (σn n ω) ω ∂μ) =
        ∫ ω in E, V ω ∂μ := by
      filter_upwards [eventually_ge_atTop m] with n hn
      have hmn : (m : ℝ≥0) ≤ (n : ℝ≥0) := by exact_mod_cast hn
      have hle : (hτn m).measurableSpace ≤ (hσn n).measurableSpace := by
        apply IsStoppingTime.measurableSpace_mono
        intro ω
        dsimp only
        rw [sourceStopTruncate_coe, sourceStopTruncate_coe]
        exact min_le_min (hτσ ω) (WithTop.coe_le_coe.mpr hmn)
      have h1 : (∫ ω in E, M (σn n ω) ω ∂μ) = ∫ ω in E, Z ω ∂μ := by
        rw [integral_congr_ae (ae_restrict_of_ae (hStop (σn n) (hσn n)))]
        have : IsFiniteMeasure (μ.trim (hσn n).measurableSpace_le) := isFiniteMeasure_trim _
        exact setIntegral_condExp (hσn n).measurableSpace_le hZ (hle E (hAm m))
      have h2 : (∫ ω in E, M (τn m ω) ω ∂μ) = ∫ ω in E, Z ω ∂μ := by
        rw [integral_congr_ae (ae_restrict_of_ae (hStop (τn m) (hτn m)))]
        have : IsFiniteMeasure (μ.trim (hτn m).measurableSpace_le) := isFiniteMeasure_trim _
        exact setIntegral_condExp (hτn m).measurableSpace_le hZ (hAm m)
      rw [h1, ← h2]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hterm, ae_restrict_mem
        ((hτn m).measurableSpace_le E (hAm m))] with ω hω hE
      exact hω m hE.2
    have hc : Tendsto (fun n : ℕ => ∫ ω in E, M (σn n ω) ω ∂μ) atTop
        (𝓝 (∫ ω in E, V ω ∂μ)) := tendsto_const_nhds.congr' (he.mono fun n hn => hn.symm)
    exact (tendsto_nhds_unique hI hc).symm
  have hlim (f : Ω → ℝ) (hf : Integrable f μ) (hz : ∀ ω, τ ω = ⊤ → f ω = 0) :
      Tendsto (fun n : ℕ => ∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, f ω ∂μ) atTop
        (𝓝 (∫ ω in A, f ω ∂μ)) := by
    have he (n : ℕ) : (∫ ω in A ∩ {ω | τ ω ≤ (n : ℝ≥0)}, f ω ∂μ) =
        ∫ ω in A, {ω | τ ω ≤ (n : ℝ≥0)}.indicator f ω ∂μ :=
      (setIntegral_indicator (μ := μ) (s := A) (f := f)
        ((ℱ.le (n : ℝ≥0)) _ (hτ n))).symm
    simp_rw [he]
    apply tendsto_integral_of_dominated_convergence (fun ω => ‖f ω‖)
      (fun n => (hf.indicator ((ℱ.le (n : ℝ≥0)) _ (hτ n))).integrableOn.aestronglyMeasurable)
      hf.norm.integrableOn
    · intro n
      exact Eventually.of_forall fun ω => norm_indicator_le_norm_self _ _
    · apply Eventually.of_forall
      intro ω
      apply (sourceStop_indicator_tendsto (τ ω) (f ω) (hz ω)).congr'
      apply Eventually.of_forall
      intro n
      classical
      by_cases hn : τ ω ≤ (n : WithTop ℝ≥0) <;> simp [Set.indicator, hn]
  have h1 := hlim V hVint (fun ω hω => (hzero ω hω).1)
  have h2 := hlim W hWint (fun ω hω => (hzero ω hω).2)
  exact tendsto_nhds_unique (h1.congr' (Eventually.of_forall hset)) h2

 

theorem sourceSpatialConditionalMean_proved : SourceSpatialConditionalMeanTarget := by
  intro Ω mΩ P hP κ hκ hκ8 γ a z ε r hε hεr hry
  let : IsProbabilityMeasure P := hP
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  let τ (ω : a.samples) := spatialHitTime (γ ω) z r
  let σ (ω : a.samples) := spatialHitTime (γ ω) z ε
  have hτ : IsStoppingTime a.filtration τ :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  have hσ : IsStoppingTime a.filtration σ :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z ε
  refine ⟨hτ, ?_⟩
  let W (v : ℝ) (ω : a.samples) := spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z v
  change μ[W ε | hτ.measurableSpace] =ᵐ[μ] W r ∧
    ∀ Y : a.samples → ℝ, Integrable Y μ → Y ≤ᵐ[μ] W ε →
      μ[Y | hτ.measurableSpace] ≤ᵐ[μ] W r
  have hr : 0 < r := hε.trans_le hεr
  have hz : z ∈ upperHalfPlane := hr.trans_le hry
  have hεy : ε ≤ z.im := hεr.trans hry
  have hτσ : τ ≤ σ := by
    intro ω
    apply spatialHitTime_antitone_radius (a.trace_continuous ω) z hεr
    rw [(a.witness ω).2.1, dist_zero_left]
    exact hry.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  let u := Real.log (4 * z.im / ε)
  have hratio : 0 < 4 * z.im / ε := div_pos (mul_pos (by norm_num) hz) hε
  have hu : 0 ≤ u := Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  have hlev : (2 * z.im) * Real.exp (-u) = ε / 2 := by
    dsimp only [u]
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp [(show 0 < z.im from hz).ne']
    ring
  have hlevelε : (2 * z.im) * Real.exp (-u) < ε := by rw [hlev]; linarith
  have hlevelr := hlevelε.trans_le hεr
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  obtain ⟨M, Z, hM, hZ, hMb, hZb, hClosed, hStop, heq, hNoHit⟩ :=
    exists_physical_green_stopping_regular a.brownian hBm a.continuous_B a.zero_B
      κ hκ hκ8 (γ ∘ Subtype.val) a.G a.F (Eventually.of_forall a.witness) z hz u hu
  have hVlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (sourceStopTruncate τ n ω) ω)
      atTop (𝓝 (W r ω)) := by
    filter_upwards [heq, hNoHit] with ω he hn
    simpa only [he.1, τ, W, sourceStopTruncate, boundedSpatialHit, Function.comp_apply] using
      (a.witness ω).spatialGreen_limit ((a.continuous_B ω).const_mul _)
        κ z r hr hry u hlevelr hn
  have hWlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (sourceStopTruncate σ n ω) ω)
      atTop (𝓝 (W ε ω)) := by
    filter_upwards [heq, hNoHit] with ω he hn
    simpa only [he.1, σ, W, sourceStopTruncate, boundedSpatialHit, Function.comp_apply] using
      (a.witness ω).spatialGreen_limit ((a.continuous_B ω).const_mul _)
        κ z ε hε hεy u hlevelε hn
  have hzero : ∀ ω, τ ω = ⊤ → W r ω = 0 ∧ W ε ω = 0 := by
    intro ω hω
    have hσtop : σ ω = ⊤ := top_unique (hω ▸ hτσ ω)
    simp only [τ] at hω
    simp only [σ] at hσtop
    simp [W, spatialGreenWeight, hω, hσtop]
  have hterm : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, τ ω ≤ (t : WithTop ℝ≥0) →
      M (sourceStopTruncate τ t ω) ω = W r ω := by
    filter_upwards [heq] with ω he
    intro t ht
    have hn : spatialHitTime (γ ω) z r ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top ht
    have htrunc : sourceStopTruncate τ t ω = (spatialHitTime (γ ω) z r).untopD 0 := by
      exact congrArg (fun v : WithTop ℝ≥0 => v.untopD 0) (min_eq_left ht)
    have hle : (((spatialHitTime (γ ω) z r).untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤
        spatialHitTime (γ ω) z r := by
      obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hn
      rw [← hv, WithTop.untopD_coe]
    change M (sourceStopTruncate τ t ω) ω =
      if spatialHitTime (γ ω) z r = ⊤ then 0 else
        greenDensity κ (fun s => Real.sqrt κ * a.B s ω) (γ ω) (a.G ω)
          ((spatialHitTime (γ ω) z r).untopD 0) z
    rw [ite_eq_right hn, htrunc, he.1]
    exact (a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z r hr hry u hlevelr _ hle
  have hcond := source_nested_stops_condExp a.filtration τ σ hτ hσ hτσ M Z (W r) (W ε)
    hZ hStop (Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
    (fun t ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hMb t ω).1]; exact (hMb t ω).2)
    hVlim hWlim hzero hterm
  refine ⟨hcond, ?_⟩
  intro Y hY hYW
  have hWi := (a.spatialGreen_expectation hκ hκ8 z ε hε hεy).1
  have hle := condExp_mono (m := hτ.measurableSpace) hY hWi hYW
  filter_upwards [hcond, hle] with ω hω hi
  exact hi.trans_eq hω

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

 

lemma source_condExp_le_changed_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 mΩ) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hle : σ ≤ τ) (A : Set Ω) (hA : MeasurableSet[hσ.measurableSpace] A)
    (heq : ∀ ω ∈ A, τ ω = σ ω)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hgm : StronglyMeasurable[hσ.measurableSpace] g)
    (hf0 : ∀ ω ∉ A, f ω = 0) (hg0 : ∀ ω ∉ A, g ω = 0)
    (hbound : μ[f | hσ.measurableSpace] ≤ᵐ[μ] g) :
    μ[f | hτ.measurableSpace] ≤ᵐ[μ] g := by
  have hm := hσ.measurableSpace_mono hτ hle
  apply source_condExp_le_of_setIntegral_le hτ.measurableSpace_le hf hg (hgm.mono hm)
  intro E hE
  have hEA : MeasurableSet[hσ.measurableSpace] (E ∩ A) := by
    have hh := hτ.measurableSet_inter_le hσ E hE
    have hraw : MeasurableSet[hσ.measurableSpace] (E ∩ {ω | τ ω ≤ σ ω}) :=
      (IsStoppingTime.measurableSet_min_iff hτ hσ _).mp hh |>.2
    have hsub : A ⊆ {ω | τ ω ≤ σ ω} := fun ω hω => (heq ω hω).le
    convert hraw.inter hA using 1
    all_goals try with_reducible_and_instances rfl
    exact (Set.inter_assoc _ _ _ |>.trans (congrArg (Set.inter E) (Set.inter_eq_right.mpr hsub))).symm
  have hfi : A.indicator f = f := by
    funext ω
    by_cases hω : ω ∈ A
    · exact Set.indicator_of_mem hω _
    · rw [Set.indicator_of_notMem hω, hf0 ω hω]
  have hgi : A.indicator g = g := by
    funext ω
    by_cases hω : ω ∈ A
    · exact Set.indicator_of_mem hω _
    · rw [Set.indicator_of_notMem hω, hg0 ω hω]
  have hAm := hσ.measurableSpace_le _ hA
  rw [← hfi, setIntegral_indicator hAm, ← hgi, setIntegral_indicator hAm]
  rw [← setIntegral_condExp hσ.measurableSpace_le hf hEA]
  exact setIntegral_mono_ae integrable_condExp.integrableOn hg.integrableOn hbound

lemma source_windowHB_range (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) :
    (sourceSpatialWindowH γ z r ε R = 0 ∨ sourceSpatialWindowH γ z r ε R = 1) ∧
    (sourceSpatialWindowB γ z r ε R = 0 ∨ sourceSpatialWindowB γ z r ε R = 1) := by
  constructor <;> (first | unfold sourceSpatialWindowH | unfold sourceSpatialWindowB) <;>
    split_ifs <;> simp

lemma source_windowHB_zero {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (hs : liveSpatialHitTime γ z r = ⊤) :
    sourceSpatialWindowH γ z r ε R = 0 ∧ sourceSpatialWindowB γ z r ε R = 0 := by
  have ht : sourceSpatialWindowTime γ z r ε R = ⊤ :=
    top_unique (by simpa only [hs] using source_window_start_le hc z r ε R)
  simp only [sourceSpatialWindowH,sourceSpatialWindowB,ht,ne_eq,not_true_eq_false,false_and,ite_false,and_self]

lemma source_windowH_le_indicator {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    sourceSpatialWindowH γ z r ε R ≤
      (if liveSpatialHitTime γ z ε = ⊤ then (0:ℝ) else 1) := by
  rcases (source_windowHB_range γ z r ε R).1 with h | h
  · rw [h]; split_ifs <;> norm_num
  · rw [h, ite_eq_right ((source_windowH_iff hc z r ε R her hs).mp h).2]

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

lemma source_window_change_live_mean
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (z : ℂ) (r : ℝ) (hy : r ≤ z.im)
    (hraw : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r))
    (hs : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r))
    (f g : a.samples → ℝ)
    (hf : Integrable f (P.comap Subtype.val)) (hg : Integrable g (P.comap Subtype.val))
    (hgm : StronglyMeasurable[hraw.measurableSpace] g)
    (hf0 : ∀ ω : a.samples, liveSpatialHitTime (γ ω) z r = ⊤ → f ω = 0)
    (hg0 : ∀ ω : a.samples, liveSpatialHitTime (γ ω) z r = ⊤ → g ω = 0)
    (hbound : (P.comap Subtype.val)[f | hraw.measurableSpace] ≤ᵐ[P.comap Subtype.val] g) :
    (P.comap Subtype.val)[f | hs.measurableSpace] ≤ᵐ[P.comap Subtype.val] g := by
  let : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  let A := {ω : a.samples | z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z r).untopA}
  have hA : MeasurableSet[hraw.measurableSpace] A := source_live_stopped_measurable a z hraw
  have he (ω : a.samples) : liveSpatialHitTime (γ ω) z r =
      if ω ∈ A then spatialHitTime (γ ω) z r else ⊤ :=
    source_liveTime_eq_killed (a.trace_continuous ω) z r (source_window_origin_bound a z r hy ω)
  have hle : (fun ω : a.samples => spatialHitTime (γ ω) z r) ≤
      (fun ω : a.samples => liveSpatialHitTime (γ ω) z r) := by
    intro ω; dsimp only; rw [he]; split_ifs <;> first | exact le_rfl | exact le_top
  apply source_condExp_le_changed_stop a.filtration hraw hs hle A hA
    (fun ω hω => by rw [he,ite_eq_left hω]) hf hg hgm
  · intro ω hω; exact hf0 ω (by rw [he,ite_eq_right hω])
  · intro ω hω; exact hg0 ω (by rw [he,ite_eq_right hω])
  · exact hbound

lemma source_window_weight_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r : ℝ)
    (hy : r ≤ z.im) (ω : a.samples) (h : liveSpatialHitTime (γ ω) z r = ⊤) :
    spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r = 0 := by
  rw [spatialGreenWeight_eq_live (a.trace_continuous ω) κ _ _ z r
    (source_window_origin_bound a z r hy ω),ite_eq_left h]

lemma source_windowH_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r ε R : ℝ)
    (hy : r ≤ z.im) :
    Integrable (fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R) (P.comap Subtype.val) := by
  let : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  have hτ := source_window_stopping a z r ε R hy
  have hm := (source_windowHB_stopped_measurable a z r ε R hτ).1.mono hτ.measurableSpace_le le_rfl
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    rcases (source_windowHB_range (γ ω) z r ε R).1 with h|h <;> simp only [h,norm_zero,norm_one,zero_le_one,le_refl]

lemma source_windowV_integrable_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (hk : 0 < κ) (hk8 : κ < 8)
    (z : ℂ) (r ε R : ℝ) (he : 0 < ε) (her : ε ≤ r) (hy : r ≤ z.im) :
    let W := fun ω : a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z ε
    let V := fun ω : a.samples => W ω*sourceSpatialWindowH (γ ω) z r ε R
    Integrable V (P.comap Subtype.val) ∧ V ≤ᵐ[P.comap Subtype.val] W := by
  dsimp only
  let W := fun ω : a.samples => spatialGreenWeight κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z ε
  let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R
  have hτ := source_window_stopping a z r ε R hy
  have hHm : Measurable H :=
    (source_windowHB_stopped_measurable a z r ε R hτ).1.mono hτ.measurableSpace_le le_rfl
  have hVm : Measurable (fun ω => W ω * H ω) :=
    (source_windowV_stopped_measurable a z r ε R her hy hτ).mono hτ.measurableSpace_le le_rfl
  have hWi := (a.spatialGreen_expectation hk hk8 z ε he (her.trans hy)).1
  have hW0 (ω : a.samples) : 0 ≤ W ω :=
    ((a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _) hk hk8 he z (her.trans hy)).1
  constructor
  · apply Integrable.mono' hWi hVm.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖W ω * H ω‖ ≤ W ω
    dsimp only [H]
    rcases (source_windowHB_range (γ ω) z r ε R).1 with h|h
    · simp only [h,mul_zero,norm_zero]; exact hW0 ω
    · simp only [h,mul_one,Real.norm_eq_abs,abs_of_nonneg (hW0 ω),le_refl]
  · filter_upwards [] with ω
    rcases (source_windowHB_range (γ ω) z r ε R).1 with h|h
    · simpa only [h,mul_zero] using hW0 ω
    · simp only [h,mul_one,le_refl]

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_windowH_mean_of_raw
    {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hk : 0 < κ) (hk8 : κ < 8) (z : ℂ) (ε r R C : ℝ)
    (he : 0 < ε) (her : ε ≤ r) (hy : r ≤ z.im)
    (hraw : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r))
    (hs : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r))
    (hbound : (P.comap Subtype.val)[(fun ω : a.samples =>
      if liveSpatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else 1) | hraw.measurableSpace]
      ≤ᵐ[P.comap Subtype.val] (fun ω : a.samples => C*ε^codimension κ*
        spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r)) :
    (P.comap Subtype.val)[(fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R) | hs.measurableSpace]
      ≤ᵐ[P.comap Subtype.val] (fun ω : a.samples => C*ε^codimension κ*
        spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r) := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  have hi := source_windowH_integrable a z r ε R hy
  have hWi := (a.spatialGreen_expectation hk hk8 z r (he.trans_le her) hy).1
  have hWm := source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
    (fun ω : a.samples => γ ω) a.G a.F a.witness z r hraw
  have hfi : Integrable (fun ω : a.samples => if liveSpatialHitTime (γ ω) z ε = ⊤ then (0:ℝ) else 1) μ := by
    apply Integrable.of_bound (source_liveIndicator_measurable a z ε (her.trans hy)).aestronglyMeasurable 1
    exact Eventually.of_forall fun ω => by split_ifs <;> norm_num
  have hcomp := condExp_mono (m := hraw.measurableSpace) hi hfi
    (Eventually.of_forall fun ω => source_windowH_le_indicator (a.trace_continuous ω) z r ε R her
      (source_window_origin_bound a z r hy ω))
  apply source_window_change_live_mean a z r hy hraw hs _ _ hi (hWi.const_mul _)
      (measurable_const.mul hWm).stronglyMeasurable
  · intro ω hω; exact (source_windowHB_zero (a.trace_continuous ω) z r ε R hω).1
  · intro ω hω; rw [source_window_weight_zero a z r hy ω hω,mul_zero]
  · exact hcomp.trans hbound

lemma source_windowV_mean
    {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hk : 0 < κ) (hk8 : κ < 8) (z : ℂ) (ε r R : ℝ)
    (he : 0 < ε) (her : ε ≤ r) (hy : r ≤ z.im)
    (hs : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r)) :
    let W := fun v (ω : a.samples) => spatialGreenWeight κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
    (P.comap Subtype.val)[(fun ω : a.samples => r^codimension κ*W ε ω*
      sourceSpatialWindowH (γ ω) z r ε R) | hs.measurableSpace]
      ≤ᵐ[P.comap Subtype.val] (fun ω : a.samples => r^codimension κ*W r ω) := by
  dsimp only
  let μ : Measure a.samples := P.comap Subtype.val
  let W := fun v (ω : a.samples) => spatialGreenWeight κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
  let V := fun ω : a.samples => W ε ω*sourceSpatialWindowH (γ ω) z r ε R
  have hi := source_windowV_integrable_le a hk hk8 z r ε R he her hy
  have hWi := (a.spatialGreen_expectation hk hk8 z r (he.trans_le her) hy).1
  obtain ⟨hraw,_,hvbound⟩ := sourceSpatialConditionalMean_proved Ω m P inferInstance κ hk hk8 γ a z ε r he her hy
  have hWm := source_spatialWeight_stopping_measurable a.measurable_B a.continuous_B κ
    (fun ω : a.samples => γ ω) a.G a.F a.witness z r hraw
  have hv : μ[V | hs.measurableSpace] ≤ᵐ[μ] W r := by
    apply source_window_change_live_mean a z r hy hraw hs V (W r) hi.1 hWi hWm.stronglyMeasurable
    · intro ω hω; dsimp only [V]; rw [(source_windowHB_zero (a.trace_continuous ω) z r ε R hω).1,mul_zero]
    · exact source_window_weight_zero a z r hy
    · exact hvbound V hi.1 hi.2
  change μ[(fun ω => r^codimension κ*W ε ω*sourceSpatialWindowH (γ ω) z r ε R) |
    hs.measurableSpace] ≤ᵐ[μ] (fun ω => r^codimension κ*W r ω)
  have heqv : (fun ω => r^codimension κ*W ε ω*sourceSpatialWindowH (γ ω) z r ε R) =
      (fun ω => r^codimension κ*V ω) := by funext ω; dsimp only [V]; ring
  rw [heqv]
  filter_upwards [condExp_smul (μ := μ) (r^codimension κ) V hs.measurableSpace, hv] with ω hc hv
  change μ[(fun ω => r^codimension κ*V ω) | hs.measurableSpace] ω =
    r^codimension κ*μ[V | hs.measurableSpace] ω at hc
  rw [hc]
  exact mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg (he.trans_le her).le _)

lemma source_window_HV_mean :
    ∀ κ : ℝ, 0 < κ → κ < 8 → ∃ C q : ℝ, 0 < C ∧ 0 < q ∧ q < 1 ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
      (z : ℂ) (ε r R : ℝ), 0 < ε → ε ≤ q*r → r ≤ z.im →
    ∃ hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r),
      let μ := P.comap (Subtype.val : a.samples → Ω)
      let W := fun v (ω : a.samples) => spatialGreenWeight κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z v
      let H := fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R
      μ[H | hσ.measurableSpace] ≤ᵐ[μ] (fun ω => C*ε^codimension κ*W r ω) ∧
      μ[(fun ω => r^codimension κ*W ε ω*H ω) | hσ.measurableSpace] ≤ᵐ[μ]
        (fun ω => r^codimension κ*W r ω) := by
  intro κ hk hk8
  obtain ⟨C,hC,q,hq,hq1,happ⟩ := sourceConditionalApproach_proved κ hk hk8
  refine ⟨C,q,hC,hq,hq1,?_⟩
  intro Ω m P hP γ a z ε r R he heq hy
  let : IsProbabilityMeasure P := hP
  have hr : 0 < r := by
    by_contra! hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hq.le hn
    linarith
  have her : ε < r := heq.trans_lt (by nlinarith)
  have hs := source_liveHit_stopping a z r hy
  obtain ⟨hraw,hbound⟩ := happ Ω m P hP γ a z ε r he heq hy
  exact ⟨hs,source_windowH_mean_of_raw a hk hk8 z ε r R C he her.le hy hraw hs hbound,
    source_windowV_mean a hk hk8 z ε r R he her.le hy hs⟩

end
end SLEExactGauge

end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_WindowBGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Window BGeometry for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_witness_initial_domain
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) : survivingDomain γ 0 = upperHalfPlane := by
  apply Set.Subset.antisymm (fun _ hz => hz.1.1)
  intro z hz
  have hf : F 0 z ∈ survivingDomain γ 0 := h.2.2.2.2.2.2.1 0 hz
  have he : F 0 z = z := (h.initial_value (F 0 z) hf.1.1).symm.trans (h.2.2.2.2.2.2.2.2.1 0 z hz)
  rwa [he] at hf

lemma source_window_initial_ball
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r : ℝ)
    (hy : r < z.im) (ω : a.samples) : closedBall z r ⊆ survivingDomain (γ ω) 0 := by
  rw [source_witness_initial_domain (a.witness ω)]
  intro w hw
  have hi := (le_abs_self (z.im-w.im)).trans (Complex.abs_im_le_norm (z-w))
  have hd : ‖z-w‖ ≤ r := by simpa only [mem_closedBall,dist_comm,dist_eq_norm] using hw
  change 0 < w.im
  linarith

lemma source_window_first_geometry
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r : ℝ)
    (hy : r < z.im) (ω : a.samples) (hfin : liveSpatialHitTime (γ ω) z r ≠ ⊤) :
    ∃ T s : ℝ≥0, liveSpatialHitTime (γ ω) z r = T ∧ s ≤ T ∧
      closedBall z r ⊆ survivingDomain (γ ω) s ∧ dist (γ ω T) z = r ∧
      (∀ t ∈ Ico s T, dist (γ ω t) z ≠ r) ∧ z ∈ survivingDomain (γ ω) T := by
  obtain ⟨T,hT⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hmem := source_liveHit_mem (a.trace_continuous ω) z r
    (source_window_origin_bound a z r hy.le ω) T hT.symm
  have he := source_liveTime_eq_sphere_of_finite (a.trace_continuous ω) z r
    (source_window_origin_bound a z r hy.le ω) hfin
  refine ⟨T,0,hT.symm,bot_le,source_window_initial_ball a z r hy ω,hmem.2,?_,hmem.1⟩
  intro t ht hd
  have hh := (spatialHitTime_le_iff (a.trace_continuous ω) z r t).mpr ⟨t,⟨bot_le,le_rfl⟩,hd⟩
  rw [← he,← hT] at hh
  exact ht.2.not_ge (WithTop.coe_le_coe.mp hh)

lemma source_windowB_le_disk
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r ε R : ℝ)
    (her : ε ≤ r) (hrR : r < R) (hy : r ≤ z.im) (ω : a.samples) :
    sourceSpatialWindowB (γ ω) z r ε R ≤
      (if liveSpatialHitTime (γ ω) z r ≠ ⊤ ∧ ∃ t : ℝ≥0,
        z ∈ survivingDomain (γ ω) ((liveSpatialHitTime (γ ω) z r).untopD 0+t) ∧
        R ≤ dist (γ ω ((liveSpatialHitTime (γ ω) z r).untopD 0+t)) z then (1:ℝ) else 0) := by
  rcases (source_windowHB_range (γ ω) z r ε R).2 with h|h
  · rw [h]; split_ifs <;> norm_num
  obtain ⟨T,hσ,hz,hd,_⟩ := source_windowB_before (a.trace_continuous ω) z r ε R her hrR
    (source_window_origin_bound a z r hy ω) h
  have hn := ne_top_of_le_ne_top WithTop.coe_ne_top hσ
  obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hn
  have hst : s ≤ T := WithTop.coe_le_coe.mp (by simpa only [← hs] using hσ)
  have he : (liveSpatialHitTime (γ ω) z r).untopD 0 + (T-s) = T := by
    rw [← hs,WithTop.untopD_coe,add_tsub_cancel_of_le hst]
  rw [h,ite_eq_left ⟨hn,T-s,by rwa [he],by rwa [he]⟩]

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable

lemma source_condExp_bound_supported
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {m : MeasurableSpace Ω}
    {f g : Ω → ℝ} {A : Set Ω} (hA : MeasurableSet[m] A)
    (hf : Integrable f μ) (hg : Integrable g μ) (hgf : g ≤ᵐ[μ] f)
    (hg0 : ∀ ω ∉ A, g ω = 0) (K : ℝ)
    (hbound : ∀ᵐ ω ∂μ, ω ∈ A → μ[f | m] ω ≤ K) :
    μ[g | m] ≤ᵐ[μ] (fun ω => K*(if ω ∈ A then 1 else 0)) := by
  have heq : A.indicator g = g := by
    funext ω
    by_cases hω : ω ∈ A
    · exact Set.indicator_of_mem hω _
    · rw [Set.indicator_of_notMem hω,hg0 ω hω]
  have he := condExp_indicator hg hA
  rw [heq] at he
  filter_upwards [he,condExp_mono (m := m) hg hf hgf,hbound] with ω he hh hb
  by_cases hω : ω ∈ A
  · simpa only [ite_eq_left hω,mul_one] using hh.trans (hb hω)
  · rw [he,Set.indicator_of_notMem hω,ite_eq_right hω,mul_zero]

lemma source_windowB_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ) (r ε R : ℝ)
    (hy : r ≤ z.im) :
    Integrable (fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε R) (P.comap Subtype.val) := by
  let : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  have hτ := source_window_stopping a z r ε R hy
  have hm := (source_windowHB_stopped_measurable a z r ε R hτ).2.mono hτ.measurableSpace_le le_rfl
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by
    rcases (source_windowHB_range (γ ω) z r ε R).2 with h|h <;> simp only [h,norm_zero,norm_one,zero_le_one,le_refl]

lemma source_windowB_mean :
    ∀ κ : ℝ, 4 < κ → κ < 8 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
      (z : ℂ) (ε r L : ℝ), 0 < r → ε ≤ r → r < z.im → 1 < L →
    ∀ hσ : IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r),
      (P.comap Subtype.val)[(fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε (L*r)) | hσ.measurableSpace]
        ≤ᵐ[P.comap Subtype.val] (fun ω : a.samples => C*L^(-c)*
          (if liveSpatialHitTime (γ ω) z r = ⊤ then 0 else 1)) := by
  intro κ hk hk8
  obtain ⟨C,c,hC,hc,hdisk⟩ := sourcePhysicalDisk_proved κ hk hk8
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω m P hP γ a z ε r L hr her hy hL hσ
  let : IsProbabilityMeasure P := hP
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  let σ := fun ω : a.samples => liveSpatialHitTime (γ ω) z r
  let A := {ω : a.samples | σ ω ≠ ⊤}
  have hA : MeasurableSet[hσ.measurableSpace] A :=
    (measurableSet_eq_fun hσ.measurable measurable_const).compl
  let E := {ω : a.samples | σ ω ≠ ⊤ ∧ ∃ t : ℝ≥0,
    z ∈ survivingDomain (γ ω) ((σ ω).untopD 0+t) ∧
    L*r ≤ dist (γ ω ((σ ω).untopD 0+t)) z}
  let f := E.indicator (fun _ => (1:ℝ))
  have hEm : MeasurableSet E := by
    apply (hσ.measurableSpace_le _ hA).inter
    exact source_physical_closed_exit_measurable
      (fun ω : a.samples => ⟨γ ω,a.trace_continuous ω⟩) (source_tracePath_measurable a)
      (fun ω => (σ ω).untopD 0) (hσ.measurable'.untopD 0) z (L*r)
  have hf : Integrable f μ := (integrable_const (1:ℝ)).indicator hEm
  have hf_def : f = (fun ω : a.samples => if ω ∈ E then 1 else 0) := by
    funext ω; exact Set.indicator_apply _ _ _
  have hgeom : ∀ ω ∈ A, ∃ T s : ℝ≥0, σ ω = T ∧ s ≤ T ∧
      closedBall z r ⊆ survivingDomain (γ ω) s ∧ dist (γ ω T) z = r ∧
      (∀ t ∈ Ico s T, dist (γ ω t) z ≠ r) ∧ z ∈ survivingDomain (γ ω) T :=
    fun ω hω => source_window_first_geometry a z r hy ω hω
  have hd := hdisk a.samples inferInstance μ inferInstance a.B a.brownian a.measurable_B
    a.continuous_B (fun ω : a.samples => γ ω) a.G a.F a.witness σ hσ z r hr A hA hgeom L hL.le
  have hb : ∀ᵐ ω ∂μ, ω ∈ A → μ[f | hσ.measurableSpace] ω ≤ C*L^(-c) := by
    rw [hf_def]
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hi := source_windowB_integrable a z r ε (L*r) hy.le
  have hgf : (fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε (L*r)) ≤ᵐ[μ] f := by
    rw [hf_def]
    exact Eventually.of_forall fun ω => source_windowB_le_disk a z r ε (L*r) her
      (by nlinarith) hy.le ω
  have hh := source_condExp_bound_supported hA hf hi hgf
    (fun ω hω => (source_windowHB_zero (a.trace_continuous ω) z r ε (L*r) (by
      simpa only [A,σ,Set.mem_ofPred_eq,ne_eq,not_not] using hω)).2) (C*L^(-c)) hb
  filter_upwards [hh] with ω hω
  by_cases htop : liveSpatialHitTime (γ ω) z r = ⊤ <;>
    simpa [A, σ, htop] using hω

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable


theorem sourceSpatialWindowMeans_proved : SourceSpatialWindowMeansTarget := by
  intro κ hk hk8
  have hk0 : 0 < κ := by linarith
  obtain ⟨C,q,hC,hq,hq1,hHV⟩ := source_window_HV_mean κ hk0 hk8
  obtain ⟨Cbad,c,hCb,hc,hB⟩ := source_windowB_mean κ hk hk8
  refine ⟨C,Cbad,c,q,hC,hCb,hc,hq,hq1,?_⟩
  intro Ω m P hP γ a z ε r L he heq hy hL
  have hr : 0 < r := by
    by_contra! hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hq.le hn
    linarith
  have her : ε ≤ r := heq.trans (by nlinarith)
  obtain ⟨hs,hH,hV⟩ := hHV Ω m P hP γ a z ε r (L*r) he heq hy.le
  exact ⟨hs,hH,hV,hB Ω m P hP γ a z ε r L hr her hy hL hs⟩
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

lemma source_mesh_power_growth {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃ u β : ℝ, 1 < u ∧ u*q < 1 ∧ 1 < q^p/(u*q) ∧ β = (q^p/(u*q))^2 ∧ 1 < β ∧
      ∀ c : ℝ, 0 < c → 0 < u^(-c) ∧ u^(-c) < 1 := by
  have hqp : q < q^p := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt hq hq1 hp1
    simpa only [Real.rpow_one] using hh
  have hqp1 : q^p < 1 := Real.rpow_lt_one hq.le hq1 hp
  let u := (1+q^p/q)/2
  have hu : 1 < u := by dsimp [u]; have : 1 < q^p/q := (lt_div_iff₀ hq).mpr (by simpa using hqp); linarith
  have huq : u*q < q^p := by dsimp [u]; field_simp; nlinarith
  have hratio : 1 < q^p/(u*q) := (lt_div_iff₀ (mul_pos (by linarith) hq)).mpr (by simpa using huq)
  refine ⟨u,(q^p/(u*q))^2,hu,huq.trans hqp1,hratio,rfl,by nlinarith,?_⟩
  intro c hc
  refine ⟨Real.rpow_pos_of_pos (by linarith) _,?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg hu (neg_neg_of_pos hc)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_mesh_choose_large {c A : ℝ} (hc : 0 < c) :
    ∃ L : ℝ, 1 < L ∧ A*L^(-c) ≤ 1/2 := by
  have ht : Tendsto (fun L : ℝ => A*L^(-c)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hc).const_mul A
  have hh := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨max N 2,lt_of_lt_of_le (by norm_num) (le_max_right _ _),(hN _ (le_max_left _ _)).le⟩

end
end SLEExactGauge
end


section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

lemma source_mesh_parameters_oai (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
    Nonempty (SourceMeshParameters κ) := by
  obtain ⟨C,Cbad,c,q,hC,hCb,hc,hq,hq1,hmean⟩ := sourceSpatialWindowMeans_proved κ hκ hκ8
  have hp : 0 < codimension κ := by dsimp [codimension,dimension]; linarith
  have hp1 : codimension κ < 1 := by dsimp [codimension,dimension]; linarith
  obtain ⟨u,β,hu,huq,hratio,hβdef,hβ,htheta⟩ := source_mesh_power_growth hp hp1 hq hq1
  obtain ⟨L,hL,hlarge⟩ := source_mesh_choose_large (A := Cbad*q^(-codimension κ)) hc
  refine ⟨⟨C,Cbad,c,q,u,L,hC,hCb,hc,hq,hq1,hu,huq,hratio,hL,?_,hmean⟩⟩
  calc
    Cbad*L^(-c)*q^(-codimension κ) = (Cbad*q^(-codimension κ))*L^(-c) := by ring
    _ ≤ 1/2 := hlarge

end
end SLEExactGauge
end


end OAI
end

theorem solution : type_of% @OAI.SLEExactGauge.source_mesh_parameters_oai := @OAI.SLEExactGauge.source_mesh_parameters_oai
