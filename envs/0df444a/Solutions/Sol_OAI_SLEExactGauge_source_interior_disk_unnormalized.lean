-- Prove2me | solution 1 for OAI.SLEExactGauge.source_interior_disk_unnormalized
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:41:35.153071+00:00
-- url     : https://prove2.me/submissions/4513ee26-40b6-4e09-ad65-c82fe92b3739

import Mathlib
import Definitions.Def_SLELowerPositivity
import Definitions.Def_OAIQ27Sle000

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
-- module Solutions.OAIQ27_SLE.SLE_LoewnerReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Loewner Reflection for chordal SLE. -/

section
section

open Set Filter Complex Metric ComplexConjugate
open scoped Topology NNReal
namespace SLEExactGauge



lemma loewnerMirror_bounded (s : Set ℂ) :
    Bornology.IsBounded (loewnerMirror '' s) ↔ Bornology.IsBounded s := by
  rw [Metric.isBounded_image_iff,Metric.isBounded_iff]
  simp only [loewnerMirror_dist]

lemma loewnerMirror_free (γ : ℝ≥0 → ℂ) (t : ℝ≥0) (z : ℂ) :
    loewnerMirror z ∈ upperHalfPlane \ ((loewnerMirror ∘ γ) '' Icc 0 t) ↔
      z ∈ upperHalfPlane \ (γ '' Icc 0 t) := by
  constructor
  · rintro ⟨hup,hn⟩
    refine ⟨by simpa only [upperHalfPlane,mem_ofPred_eq,loewnerMirror_im] using hup,?_⟩
    rintro ⟨u,hu,rfl⟩
    exact hn ⟨u,hu,rfl⟩
  · rintro ⟨hup,hn⟩
    refine ⟨by simpa only [upperHalfPlane,mem_ofPred_eq,loewnerMirror_im] using hup,?_⟩
    rintro ⟨u,hu,he⟩
    exact hn ⟨u,hu,loewnerMirror.injective he⟩

lemma loewnerMirror_free_image (γ : ℝ≥0 → ℂ) (t : ℝ≥0) :
    loewnerMirror '' (upperHalfPlane \ (γ '' Icc 0 t)) =
      upperHalfPlane \ ((loewnerMirror ∘ γ) '' Icc 0 t) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (loewnerMirror_free γ t w).mpr hw
  · intro hz
    refine ⟨loewnerMirror z,?_,loewnerMirror_twice z⟩
    apply (loewnerMirror_free γ t (loewnerMirror z)).mp
    simpa only [loewnerMirror_twice] using hz

lemma loewnerMirror_surviving (γ : ℝ≥0 → ℂ) (t : ℝ≥0) (z : ℂ) :
    loewnerMirror z ∈ survivingDomain (loewnerMirror ∘ γ) t ↔
      z ∈ survivingDomain γ t := by
  have hcc (hz : z ∈ upperHalfPlane \ (γ '' Icc 0 t)) :
      loewnerMirror '' connectedComponentIn (upperHalfPlane \ (γ '' Icc 0 t)) z =
        connectedComponentIn (upperHalfPlane \ ((loewnerMirror ∘ γ) '' Icc 0 t)) (loewnerMirror z) := by
    rw [loewnerMirror.image_connectedComponentIn hz,loewnerMirror_free_image]
  constructor
  · rintro ⟨hz,hun⟩
    have hz' := (loewnerMirror_free γ t z).mp hz
    refine ⟨hz',?_⟩
    intro hb
    apply hun
    rw [← hcc hz']
    exact (loewnerMirror_bounded _).mpr hb
  · rintro ⟨hz,hun⟩
    refine ⟨(loewnerMirror_free γ t z).mpr hz,?_⟩
    intro hb
    apply hun
    apply (loewnerMirror_bounded _).mp
    rwa [hcc hz]

lemma mirror_conjugate_differentiable {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (loewnerMirror z)) :
    DifferentiableAt ℂ (fun w => loewnerMirror (f (loewnerMirror w))) z := by
  have hg : DifferentiableAt ℂ (fun w => f (-w)) (conj z) :=
    hf.comp (conj z) (differentiableAt_id.neg)
  have hh := hg.conj_conj.neg
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Complex.conj_conj]

end SLEExactGauge

namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.mirror
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) :
    IsCapacityTwoWitness (fun t => -U t) (loewnerMirror ∘ γ)
      (fun t z => loewnerMirror (G t (loewnerMirror z)))
      (fun t z => loewnerMirror (F t (loewnerMirror z))) := by
  have hm (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain (loewnerMirror ∘ γ) t) :
      loewnerMirror z ∈ survivingDomain γ t := by
    apply (loewnerMirror_surviving γ t (loewnerMirror z)).mp
    simpa only [loewnerMirror_twice] using hz
  have hup (z : ℂ) : loewnerMirror z ∈ upperHalfPlane ↔ z ∈ upperHalfPlane := by
    simp only [upperHalfPlane,mem_ofPred_eq,loewnerMirror_im]
  rcases h with ⟨hc,h0,him,hG,hF,hGm,hFm,hFG,hGF,hG0,hode,hnorm,htip⟩
  refine ⟨loewnerMirror.continuous.comp hc,by simp [h0],?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t; simpa only [Function.comp_apply,loewnerMirror_im] using him t
  · intro t z hz
    exact (mirror_conjugate_differentiable ((hG t (loewnerMirror z) (hm t z hz)).differentiableAt
      ((isOpen_survivingDomain hc t).mem_nhds (hm t z hz)))).differentiableWithinAt
  · intro t z hz
    exact (mirror_conjugate_differentiable ((hF t (loewnerMirror z) ((hup z).mpr hz)).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds ((hup z).mpr hz)))).differentiableWithinAt
  · intro t z hz
    exact (hup _).mpr (hGm t (hm t z hz))
  · intro t z hz
    exact (loewnerMirror_surviving γ t _).mpr (hFm t ((hup z).mpr hz))
  · intro t z hz
    dsimp only
    rw [loewnerMirror_twice,hFG t _ (hm t z hz),loewnerMirror_twice]
  · intro t z hz
    dsimp only
    rw [loewnerMirror_twice,hGF t _ ((hup z).mpr hz),loewnerMirror_twice]
  · intro z hz
    dsimp only
    rw [hG0 _ ((hup z).mpr hz),loewnerMirror_twice]
  · intro t z hz
    have hd := (hode t (loewnerMirror z) (hm t z hz)).star.neg
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only
    simp only [loewnerMirror_apply,Complex.ofReal_neg,neg_sub_neg,Complex.star_def]
    rw [← neg_sub,div_neg]
    simp only [map_div₀,map_sub,map_ofNat,Complex.conj_ofReal]
  · intro t
    have hmir : Tendsto loewnerMirror
        (cocompact ℂ ⊓ 𝓟 (survivingDomain (loewnerMirror ∘ γ) t))
        (cocompact ℂ ⊓ 𝓟 (survivingDomain γ t)) := by
      apply tendsto_inf.mpr
      constructor
      · exact (show Tendsto loewnerMirror (cocompact ℂ) (cocompact ℂ) from
          le_of_eq loewnerMirror.map_cocompact).mono_left inf_le_left
      · apply tendsto_principal.mpr
        exact (eventually_inf_principal.mpr (Filter.Eventually.of_forall fun z hz => hm t z hz))
    have hh := Complex.continuous_conj.continuousAt.tendsto.comp ((hnorm t).comp hmir)
    convert! hh using 1
    · ext z
      simp only [Function.comp_def,loewnerMirror_apply,map_mul,map_sub,map_neg,
        Complex.conj_conj]
      ring
    · simp only [map_mul,map_ofNat,Complex.conj_ofReal]
  · intro t
    have hh := loewnerMirror.continuous.continuousAt.tendsto.comp (htip t)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    apply Complex.ext <;> simp [add_comm]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma rightCenter_re (a u : ℝ) (z : ℂ) : (rightCenter a u z).re = max a (z.re-u) := by
  simp [rightCenter]

lemma rightCenter_norm (a u : ℝ) (z : ℂ) : a ≤ ‖rightCenter a u z‖ :=
  (le_max_left a (z.re-u)).trans ((rightCenter_re a u z).symm.le.trans (Complex.re_le_norm _))

lemma rightCenter_ne_zero {a : ℝ} (ha : 0 < a) (u : ℝ) (z : ℂ) : rightCenter a u z ≠ 0 :=
  norm_pos_iff.mp (ha.trans_le (rightCenter_norm a u z))

lemma rightCenter_eq {a u : ℝ} {z : ℂ} (hz : a ≤ z.re-u) : rightCenter a u z = z - (u : ℂ) := by
  apply Complex.ext <;> simp [rightCenter, max_eq_right hz]

lemma rightCenter_dist (a u : ℝ) (z w : ℂ) :
    dist (rightCenter a u z) (rightCenter a u w) ≤ 2 * dist z w := by
  have hr : |max a (z.re-u) - max a (w.re-u)| ≤ ‖z-w‖ := by
    have h := ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_max a).dist_le_mul
      (z.re-u) (w.re-u)
    have hh : |max a (z.re-u) - max a (w.re-u)| ≤ |z.re-w.re| := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul,id_eq,sub_sub_sub_cancel_right] using h
    exact hh.trans (Complex.abs_re_le_norm (z-w))
  have hi : |z.im-w.im| ≤ ‖z-w‖ := Complex.abs_im_le_norm (z-w)
  have he : rightCenter a u z - rightCenter a u w =
      ((max a (z.re-u) - max a (w.re-u) : ℝ) : ℂ) + ((z.im-w.im : ℝ) : ℂ)*I := by
    simp only [rightCenter,Complex.ofReal_sub]; ring
  rw [dist_eq_norm,he]
  have hb := norm_add_le ((max a (z.re-u)-max a (w.re-u) : ℝ) : ℂ) (((z.im-w.im : ℝ) : ℂ)*I)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at hb
  rw [dist_eq_norm]
  linarith

lemma rightField_bound {a : ℝ} (ha : 0 < a) (u : ℝ) (z : ℂ) :
    ‖rightField a u z‖ ≤ 2 * a⁻¹ := by
  have hi : ‖(rightCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ ha (rightCenter_norm a u z)
  simpa only [rightField, norm_mul, norm_ofNat] using mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)

lemma rightField_lipschitz {a : ℝ} (ha : 0 < a) (u : ℝ) :
    LipschitzWith ⟨4 * a⁻¹ ^ 2, by positivity⟩ (rightField a u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hz : ‖(rightCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ ha (rightCenter_norm a u z)
  have hw : ‖(rightCenter a u w)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ ha (rightCenter_norm a u w)
  rw [dist_eq_norm, rightField, rightField, ← mul_sub, norm_mul, norm_ofNat,
    inv_sub_inv' (rightCenter_ne_zero ha _ _) (rightCenter_ne_zero ha _ _), norm_mul, norm_mul]
  calc
    _ ≤ 2 * (a⁻¹ * (2 * dist z w) * a⁻¹) := by
      gcongr
      simpa only [← dist_eq_norm, dist_comm] using rightCenter_dist a u z w
    _ = _ := by change 2 * (a⁻¹ * (2 * dist z w) * a⁻¹) = (4 * a⁻¹ ^ 2) * dist z w; ring

lemma continuous_rightField {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × ℂ => rightField a p.1 p.2) := by
  apply continuous_const.mul
  apply Continuous.inv₀
  · exact ((Complex.continuous_ofReal.comp (continuous_const.max
      ((Complex.continuous_re.comp continuous_snd).sub continuous_fst))).add
      ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp continuous_snd)).mul continuous_const))
  · intro p; exact rightCenter_ne_zero ha _ _

lemma rightField_eq {a u : ℝ} {z : ℂ} (hz : a ≤ z.re-u) :
    rightField a u z = 2/(z-(u:ℂ)) := by
  simp only [rightField,rightCenter_eq hz,div_eq_mul_inv]

end SLEExactGauge
end


section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma exists_measurable_right_flow
    {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ → Ω → ℝ) (hUm : Measurable (fun p : ℝ × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω))
    (w : Ω → ℂ) (hwm : Measurable w) {a : ℝ} (ha : 0 < a) :
    ∃ Q : ℝ → Ω → ℂ,
      Measurable (fun p : ℝ × Ω => Q p.1 p.2) ∧
      (∀ ω, Q 0 ω = w ω) ∧
      (∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
        (rightField a (U t ω) (Q t ω)) (Ici 0) t) := by
  have hm : Measurable (fun p : (ℝ × Ω) × ℂ => rightField a (U p.1.1 p.1.2) p.2) := by
    have hj : Measurable (fun p : (ℝ × Ω) × ℂ => (U p.1.1 p.1.2, p.2)) :=
      (hUm.comp measurable_fst).prodMk measurable_snd
    have hf : Measurable (fun q : ℝ × ℂ => rightField a q.1 q.2) :=
      (continuous_rightField ha).measurable
    exact Measurable.comp (g := fun q : ℝ × ℂ => rightField a q.1 q.2)
      (f := fun p : (ℝ × Ω) × ℂ => (U p.1.1 p.1.2, p.2)) hf hj
  have hc (ω : Ω) (z : ℂ) : Continuous (fun t : ℝ => rightField a (U t ω) z) :=
    Continuous.comp (g := fun q : ℝ × ℂ => rightField a q.1 q.2)
      (f := fun t : ℝ => (U t ω, z)) (continuous_rightField ha)
      ((hUc ω).prodMk continuous_const)
  exact exists_random_initial_bounded_flow (fun t ω z => rightField a (U t ω) z)
    w hwm ⟨2 * a⁻¹, by positivity⟩ ⟨4 * a⁻¹ ^ 2, by positivity⟩ hm hc
      (fun ω t => rightField_lipschitz ha _) (fun ω t z => rightField_bound ha _ _)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge



lemma positiveBoundaryField_eq {a u x : ℝ} (h : a ≤ x-u) :
    positiveBoundaryField a u x = 2/(x-u) := by
  simp only [positiveBoundaryField,max_eq_right h,div_eq_mul_inv]

lemma positiveBoundaryField_bound {a : ℝ} (ha : 0 < a) (u x : ℝ) :
    ‖positiveBoundaryField a u x‖ ≤ 2*a⁻¹ := by
  have hp : 0 < max a (x-u) := ha.trans_le (le_max_left _ _)
  simp only [positiveBoundaryField,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_inv,
    abs_of_pos hp]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ ha (le_max_left _ _)) (by norm_num)

lemma positiveBoundaryField_lipschitz {a : ℝ} (ha : 0 < a) (u : ℝ) :
    LipschitzWith ⟨2*a⁻¹^2,by positivity⟩ (positiveBoundaryField a u) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 0 < max a (x-u) := ha.trans_le (le_max_left _ _)
  have hy : 0 < max a (y-u) := ha.trans_le (le_max_left _ _)
  have hi (z : ℝ) : ‖(max a (z-u))⁻¹‖ ≤ a⁻¹ := by
    rw [Real.norm_eq_abs,abs_inv,abs_of_pos (ha.trans_le (le_max_left _ _))]
    exact inv_anti₀ ha (le_max_left _ _)
  have hm : ‖max a (y-u)-max a (x-u)‖ ≤ dist x y := by
    have hh := ((LipschitzWith.id : LipschitzWith 1 (fun z : ℝ => z)).const_max a).dist_le_mul
      (y-u) (x-u)
    simpa only [NNReal.coe_one,one_mul,id_eq,dist_sub_right,dist_eq_norm,norm_sub_rev,sub_sub_sub_cancel_right] using hh
  rw [dist_eq_norm,positiveBoundaryField,positiveBoundaryField,← mul_sub,norm_mul,
    Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    inv_sub_inv' hx.ne' hy.ne',norm_mul,norm_mul]
  calc
    _ ≤ 2*(a⁻¹ * dist x y * a⁻¹) := by gcongr <;> exact hi _
    _ = _ := by change 2*(a⁻¹*dist x y*a⁻¹)=(2*a⁻¹^2)*dist x y; ring

lemma continuous_positiveBoundaryField {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × ℝ => positiveBoundaryField a p.1 p.2) := by
  apply continuous_const.mul
  apply Continuous.inv₀
  · exact continuous_const.max (continuous_snd.sub continuous_fst)
  · intro p; exact (ha.trans_le (le_max_left a (p.2-p.1))).ne'

end SLEExactGauge
end


section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma clipped_real_inv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖(max a x)⁻¹‖ ≤ a⁻¹ := by
  rw [Real.norm_eq_abs,abs_inv,abs_of_pos (ha.trans_le (le_max_left _ _))]
  exact inv_anti₀ ha (le_max_left _ _)

lemma clipped_real_inv_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith ⟨a⁻¹^2,by positivity⟩ (fun x : ℝ => (max a x)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : max a x ≠ 0 := (ha.trans_le (le_max_left _ _)).ne'
  have hy : max a y ≠ 0 := (ha.trans_le (le_max_left _ _)).ne'
  have hmax : ‖max a y-max a x‖ ≤ dist x y := by
    have hh := ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_max a).dist_le_mul y x
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,id_eq,Real.norm_eq_abs,abs_sub_comm] using hh
  rw [dist_eq_norm,inv_sub_inv' hx hy,norm_mul,norm_mul]
  calc
    _ ≤ a⁻¹*dist x y*a⁻¹ := by gcongr <;> exact clipped_real_inv_bound ha _
    _ = _ := by change a⁻¹*dist x y*a⁻¹ = a⁻¹^2*dist x y; ring

lemma boundaryClockField_bound {a : ℝ} (ha : 0 < a) (u : ℝ) (q : ℂ) :
    ‖boundaryClockField a u q‖ ≤ 2*a⁻¹+a⁻¹^2 := by
  have h0 := positiveBoundaryField_bound ha u q.re
  have h1 := clipped_real_inv_bound ha (q.re-u)
  have h2 : ‖(max a (q.re-u))⁻¹^2‖ ≤ a⁻¹^2 := by
    rw [norm_pow]
    gcongr
  have hh := norm_add_le (positiveBoundaryField a u q.re : ℂ) (((max a (q.re-u))⁻¹^2 : ℝ)*I)
  simp only [norm_mul,Complex.norm_real,Complex.norm_I,mul_one] at hh
  exact hh.trans (add_le_add h0 h2)

lemma boundaryClockField_lipschitz {a : ℝ} (ha : 0 < a) (u : ℝ) :
    LipschitzWith ⟨2*a⁻¹^2+2*a⁻¹^3,by positivity⟩ (boundaryClockField a u) := by
  apply LipschitzWith.of_dist_le_mul
  intro q w
  have hd : dist (q.re-u) (w.re-u) ≤ dist q w := by
    simpa only [dist_sub_right,dist_eq_norm,Complex.sub_re,Real.norm_eq_abs,sub_sub_sub_cancel_right] using Complex.abs_re_le_norm (q-w)
  have hi : ‖(max a (q.re-u))⁻¹-(max a (w.re-u))⁻¹‖ ≤ a⁻¹^2*dist q w := by
    exact ((clipped_real_inv_lipschitz ha).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd (sq_nonneg _))
  have hsum : ‖(max a (q.re-u))⁻¹+(max a (w.re-u))⁻¹‖ ≤ 2*a⁻¹ := by
    exact (norm_add_le _ _).trans (by linarith [clipped_real_inv_bound ha (q.re-u),clipped_real_inv_bound ha (w.re-u)])
  have hsq : ‖(max a (q.re-u))⁻¹^2-(max a (w.re-u))⁻¹^2‖ ≤ 2*a⁻¹^3*dist q w := by
    rw [sq_sub_sq,norm_mul,mul_comm]
    calc
      _ ≤ (a⁻¹^2*dist q w)*(2*a⁻¹) := mul_le_mul hi hsum (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hr := (positiveBoundaryField_lipschitz ha u).dist_le_mul q.re w.re
  have hr' : ‖positiveBoundaryField a u q.re-positiveBoundaryField a u w.re‖ ≤ 2*a⁻¹^2*dist q w := by
    rw [← dist_eq_norm]
    apply hr.trans
    change (2*a⁻¹^2)*dist q.re w.re ≤ (2*a⁻¹^2)*dist q w
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_sub_right] using hd) (by positivity)
  rw [dist_eq_norm]
  have he : boundaryClockField a u q-boundaryClockField a u w =
    ((positiveBoundaryField a u q.re-positiveBoundaryField a u w.re:ℝ):ℂ)+
    (((max a (q.re-u))⁻¹^2-(max a (w.re-u))⁻¹^2:ℝ):ℂ)*I := by
    simp only [boundaryClockField,Complex.ofReal_sub]; ring
  rw [he]
  have hn := norm_add_le ((positiveBoundaryField a u q.re-positiveBoundaryField a u w.re:ℝ):ℂ)
    ((((max a (q.re-u))⁻¹^2-(max a (w.re-u))⁻¹^2:ℝ):ℂ)*I)
  simp only [norm_mul,Complex.norm_real,Complex.norm_I,mul_one] at hn
  calc
    _ ≤ 2*a⁻¹^2*dist q w+2*a⁻¹^3*dist q w := hn.trans (add_le_add hr' hsq)
    _ = _ := by change _ = (2*a⁻¹^2+2*a⁻¹^3)*dist q w; ring

lemma continuous_boundaryClockField {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × ℂ => boundaryClockField a p.1 p.2) := by
  apply Continuous.add
  · exact Complex.continuous_ofReal.comp ((continuous_positiveBoundaryField ha).comp
      (continuous_fst.prodMk (Complex.continuous_re.comp continuous_snd)))
  · apply Continuous.mul _ continuous_const
    apply Complex.continuous_ofReal.comp
    apply Continuous.pow
    apply Continuous.inv₀
    · exact continuous_const.max ((Complex.continuous_re.comp continuous_snd).sub continuous_fst)
    · intro p; exact (ha.trans_le (le_max_left _ _)).ne'

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SLEExactGauge

 

theorem boundary_clock_global_adapted_solution
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hU : Measurable (fun q : ℝ≥0 × Ω => U q.1 q.2))
    (hc : ∀ ω, Continuous (fun t : ℝ≥0 => U t ω))
    (κ a : ℝ) (ha : 0 < a) (q₀ : ℂ) :
    ∃ (L : ℝ≥0) (Q : ℝ → Ω → ℂ),
      Measurable (fun q : ℝ × Ω => Q q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => Q t ω)) ∧
      (∀ ω, Q 0 ω = q₀) ∧
      (∀ ω t, 0 ≤ t →
        HasDerivWithinAt (fun s => Q s ω)
          (boundaryClockField a (Real.sqrt κ*U t.toNNReal ω) (Q t ω))
          (Ici 0) t) ∧
      Adapted (Filtration.natural U (fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable))
        (fun t : ℝ≥0 => Q t) := by
  let L : ℝ≥0 := ⟨2*a⁻¹+a⁻¹^2,by positivity⟩
  let K : ℝ≥0 := ⟨2*a⁻¹^2+2*a⁻¹^3,by positivity⟩
  have hbound := boundaryClockField_bound ha
  have hlip := boundaryClockField_lipschitz ha
  let V (t : ℝ) (ω : Ω) (q : ℂ) := boundaryClockField a (Real.sqrt κ*U t.toNNReal ω) q
  have hF : Continuous (fun p : ℝ × ℂ => boundaryClockField a (Real.sqrt κ*p.1) p.2) :=
    (continuous_boundaryClockField ha).comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hUr : Measurable (fun q : ℝ × Ω => U q.1.toNNReal q.2) :=
    hU.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun q : (ℝ × Ω) × (ℂ) => V q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ) => boundaryClockField a (Real.sqrt κ*p.1) p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ) => (U q.1.1.toNNReal q.1.2, q.2)))
    exact hF.measurable.comp ((hUr.comp measurable_fst).prodMk measurable_snd)
  have hcont (ω : Ω) (q : ℂ) : Continuous (fun t : ℝ => V t ω q) := by
    change Continuous ((fun p : ℝ × (ℂ) => boundaryClockField a (Real.sqrt κ*p.1) p.2) ∘
      (fun t : ℝ => (U t.toNNReal ω, q)))
    exact hF.comp (((hc ω).comp continuous_real_toNNReal).prodMk continuous_const)
  obtain ⟨Q, hQm, hQl, hQ0, hQd, hQconv⟩ :=
    exists_measurable_global_bounded_ode_picard V q₀ L K hm hcont
      (fun ω t => hlip (Real.sqrt κ*U t.toNNReal ω)) (fun ω t q => hbound (Real.sqrt κ*U t.toNNReal ω) q)
  refine ⟨L, Q, hQm, hQl, hQ0, hQd, ?_⟩
  intro t
  have hUfrozen := measurable_driver_frozen U hU hc t
  let m := Filtration.natural U (fun t => (hU.comp measurable_prodMk_left).stronglyMeasurable) t
  let : MeasurableSpace Ω := m
  let W (s : ℝ) (ω : Ω) (q : ℂ) :=
    boundaryClockField a (Real.sqrt κ*U (min s.toNNReal t) ω) q
  have hW : Measurable (fun q : (ℝ × Ω) × (ℂ) => W q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ) => boundaryClockField a (Real.sqrt κ*p.1) p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ) => (U (min q.1.1.toNNReal t) q.1.2, q.2)))
    exact hF.measurable.comp ((hUfrozen.comp measurable_fst).prodMk measurable_snd)
  have heq (n : ℕ) (ω : Ω) : picardApprox W q₀ n (t : ℝ) ω = picardApprox V q₀ n (t : ℝ) ω := by
    apply picardApprox_congr_on q₀ (t : ℝ) _ n (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩ ω
    intro s hs ω q
    have hh : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    simp only [W, V, min_eq_left hh]
  apply measurable_of_tendsto_metrizable (f := fun n ω => picardApprox W q₀ n (t : ℝ) ω)
  · intro n
    exact (picardApprox_measurable W q₀ hW n).comp measurable_prodMk_left
  · apply tendsto_pi_nhds.mpr
    intro ω
    simpa only [heq, max_eq_right t.coe_nonneg] using hQconv t ω

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma exists_boundaryClockSolution
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ a : ℝ) (ha : 0 < a) (q₀ : ℂ) :
    Nonempty (BoundaryClockSolution B hm κ a q₀) := by
  obtain ⟨L,Q,hQm,hQl,hQ0,hQd,hQa⟩ := boundary_clock_global_adapted_solution B hBm hBc κ a ha q₀
  exact ⟨⟨L,Q,hQm,hQl,hQ0,hQd,hQa⟩⟩

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

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge



lemma smoothPositiveGap_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 < smoothPositiveGap a x := by
  by_cases hx : x ≤ a
  · have he : 1 ≤ (2*a-x)/a := (le_div_iff₀ ha).mpr (by linarith)
    simp only [smoothPositiveGap,Real.smoothTransition.one_of_one_le he,sub_self,mul_zero,add_zero]
    exact ha
  · have ht := Real.smoothTransition.le_one ((2*a-x)/a)
    have hm : 0 ≤ (x-a)*(1-Real.smoothTransition ((2*a-x)/a)) := mul_nonneg (by linarith) (by linarith)
    unfold smoothPositiveGap
    linarith

lemma smoothPositiveGap_eq {a x : ℝ} (ha : 0 < a) (hx : 2*a ≤ x) :
    smoothPositiveGap a x = x := by
  have he : (2*a-x)/a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  simp only [smoothPositiveGap,Real.smoothTransition.zero_of_nonpos he,sub_zero,mul_one]
  ring

lemma smoothPositiveGap_contDiff (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPositiveGap a) := by
  unfold smoothPositiveGap
  fun_prop

lemma smoothBoundaryDensity_contDiff (κ α β : ℝ) {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ => smoothBoundaryDensity κ α β a p.1 p.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ => p.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ => p.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℝ => smoothPositiveGap a (p.1.re-Real.sqrt κ*p.2)) :=
    (smoothPositiveGap_contDiff a).comp (hre.sub (contDiff_const.mul contDiff_snd))
  exact ((contDiff_const.mul him).sub (contDiff_const.mul
    (hg.log (fun p => (smoothPositiveGap_pos ha _).ne')))).exp

lemma smoothBoundaryDensity_eq {κ α β a : ℝ} {q : ℂ} {b : ℝ}
    (ha : 0 < a) (hx : 2*a ≤ q.re-Real.sqrt κ*b) :
    smoothBoundaryDensity κ α β a q b = boundaryDensity κ α β q b := by
  simp only [smoothBoundaryDensity,boundaryDensity,smoothPositiveGap_eq ha hx]

lemma smoothBoundaryDensity_eventuallyEq (κ α β : ℝ) {a : ℝ} (ha : 0 < a)
    (p : ℂ × ℝ) (hp : 2*a < p.1.re-Real.sqrt κ*p.2) :
    (fun q : ℂ × ℝ => smoothBoundaryDensity κ α β a q.1 q.2) =ᶠ[𝓝 p]
      (fun q : ℂ × ℝ => boundaryDensity κ α β q.1 q.2) := by
  have he : ∀ᶠ q : ℂ × ℝ in 𝓝 p, 2*a < q.1.re-Real.sqrt κ*q.2 :=
    ((Complex.continuous_re.comp continuous_fst).sub
      (continuous_const.mul continuous_snd)).continuousAt.eventually (lt_mem_nhds hp)
  filter_upwards [he] with q hq
  simp only [smoothBoundaryDensity,boundaryDensity,smoothPositiveGap_eq ha hq.le]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma boundaryDensity_contDiffAt (κ α β : ℝ) (p : ℂ × ℝ)
    (hp : p.1.re-Real.sqrt κ*p.2 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => boundaryDensity κ α β r.1 r.2) p := by
  have hre : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => r.1.re) p :=
    (Complex.reCLM.contDiff.comp contDiff_fst).contDiffAt
  have him : ContDiffAt ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => r.1.im) p :=
    (Complex.imCLM.contDiff.comp contDiff_fst).contDiffAt
  exact ((contDiffAt_const.mul him).sub (contDiffAt_const.mul
    ((hre.sub (contDiffAt_const.mul contDiffAt_snd)).log hp))).exp

lemma boundaryDensity_spatial_derivative (κ α β : ℝ) (q : ℂ) (b : ℝ)
    (hp : q.re-Real.sqrt κ*b ≠ 0) :
    HasDerivAt (boundaryDensity κ α β q)
      (boundaryDensity κ α β q b*(β*Real.sqrt κ/(q.re-Real.sqrt κ*b))) b := by
  have hX := (hasDerivAt_const b q.re).sub ((hasDerivAt_id b).const_mul (Real.sqrt κ))
  have hd := ((hasDerivAt_const b (-β*α*q.im)).sub ((hX.log hp).const_mul β)).exp
  convert hd using 1 <;> try rfl
  dsimp only [boundaryDensity,Pi.sub_apply,Pi.mul_apply,Pi.div_apply,Function.comp_def,id_eq]
  ring

lemma boundaryDensity_spatial_second (κ α β : ℝ) (hκ : 0 ≤ κ) (q : ℂ) (b : ℝ)
    (hp : q.re-Real.sqrt κ*b ≠ 0) :
    iteratedDeriv 2 (boundaryDensity κ α β q) b =
      boundaryDensity κ α β q b*κ*β*(β+1)/(q.re-Real.sqrt κ*b)^2 := by
  have hn : ∀ᶠ y : ℝ in 𝓝 b, q.re-Real.sqrt κ*y ≠ 0 :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne hp
  have hd : deriv (boundaryDensity κ α β q) =ᶠ[𝓝 b]
      (fun y => boundaryDensity κ α β q y*(β*Real.sqrt κ/(q.re-Real.sqrt κ*y))) := by
    filter_upwards [hn] with y hy
    exact (boundaryDensity_spatial_derivative κ α β q y hy).deriv
  have hX := (hasDerivAt_const b q.re).sub ((hasDerivAt_id b).const_mul (Real.sqrt κ))
  have hh := (boundaryDensity_spatial_derivative κ α β q b hp).mul
    ((hasDerivAt_const b (β*Real.sqrt κ)).div hX hp)
  dsimp only [Pi.mul_apply,Pi.div_apply,Pi.sub_apply,id_eq] at hh
  change HasDerivAt (fun y => boundaryDensity κ α β q y*(β*Real.sqrt κ/(q.re-Real.sqrt κ*y))) _ b at hh
  rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,hd.deriv_eq,hh.deriv]
  have hs := Real.sq_sqrt hκ
  generalize boundaryDensity κ α β q b = f
  generalize q.re-Real.sqrt κ*b = X
  generalize Real.sqrt κ = r at *
  rw [← hs]
  field_simp
  ring

lemma boundaryDensity_directional (κ α β : ℝ) (q v : ℂ) (b : ℝ)
    (hp : q.re-Real.sqrt κ*b ≠ 0) :
    fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b) (v,0) =
      boundaryDensity κ α β q b * (-β*α*v.im - β*v.re/(q.re-Real.sqrt κ*b)) := by
  have hr : HasDerivAt (fun t : ℝ => (q+t • v).re) v.re 0 := by
    simpa only [Complex.add_re,Complex.smul_re,smul_eq_mul,id_eq,one_mul] using
      ((hasDerivAt_id (0:ℝ)).mul_const v.re).const_add q.re
  have hi : HasDerivAt (fun t : ℝ => (q+t • v).im) v.im 0 := by
    simpa only [Complex.add_im,Complex.smul_im,smul_eq_mul,id_eq,one_mul] using
      ((hasDerivAt_id (0:ℝ)).mul_const v.im).const_add q.im
  have hd := ((hi.const_mul (-β*α)).sub
    (((hr.sub_const (Real.sqrt κ*b)).log (by simpa only [zero_smul,add_zero] using hp)).const_mul β)).exp
  have hline : HasDerivAt (fun t : ℝ => boundaryDensity κ α β (q+t • v) b)
      (boundaryDensity κ α β q b * (-β*α*v.im-β*v.re/(q.re-Real.sqrt κ*b))) 0 := by
    convert hd using 1 <;> try rfl
    simp only [zero_smul,add_zero,boundaryDensity,Pi.sub_apply]
    ring
  have haff : HasDerivAt (fun t : ℝ => (q+t • v,b)) (v,0) 0 := by
    simpa only [id_eq,one_smul] using (((hasDerivAt_id (0:ℝ)).smul_const v).const_add q).prodMk (hasDerivAt_const 0 b)
  have hfd : HasFDerivAt (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2)
      (fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b)) (q+(0:ℝ) • v,b) := by
    simpa only [zero_smul,add_zero] using ((boundaryDensity_contDiffAt κ α β (q,b) hp).differentiableAt (by simp)).hasFDerivAt
  have hh := hfd.comp_hasDerivAt 0 haff
  exact hh.unique hline

lemma boundaryDensity_generator (κ α β : ℝ) (hκ : 0 ≤ κ) (q : ℂ) (b : ℝ)
    (hp : q.re-Real.sqrt κ*b ≠ 0) :
    fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b)
      (((2/(q.re-Real.sqrt κ*b):ℝ):ℂ) + (((q.re-Real.sqrt κ*b)⁻¹^2:ℝ):ℂ)*I,0) +
      (1/2:ℝ)*iteratedDeriv 2 (boundaryDensity κ α β q) b =
      boundaryDensity κ α β q b * β * (-α-2+κ*(β+1)/2)/(q.re-Real.sqrt κ*b)^2 := by
  rw [boundaryDensity_directional κ α β q _ b hp,boundaryDensity_spatial_second κ α β hκ q b hp]
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
    Complex.I_re,mul_zero,add_zero,zero_add,Complex.add_re,Complex.mul_re,sub_zero]
  field_simp

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma exists_compact_boundary_field (κ α β a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) :
    ∃ φ : ℂ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ q b, ‖(q,b)‖ ≤ R → 2*a < q.re-Real.sqrt κ*b → φ (q,b) = boundaryDensity κ α β q b) ∧
      (∀ q b, ‖(q,b)‖ ≤ R → 2*a < q.re-Real.sqrt κ*b →
        fderiv ℝ φ (q,b) = fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b)) ∧
      (∀ q b, ‖(q,b)‖ ≤ R → 2*a < q.re-Real.sqrt κ*b →
        iteratedDeriv 2 (fun x => φ (q,x)) b = iteratedDeriv 2 (boundaryDensity κ α β q) b) := by
  let cut : ContDiffBump (0 : ℂ × ℝ) := ⟨R+1,R+2,by linarith,by linarith⟩
  let φ (p : ℂ × ℝ) := cut p*smoothBoundaryDensity κ α β a p.1 p.2
  have hnear (p : ℂ × ℝ) (hball : ‖p‖ ≤ R) (hp : 2*a < p.1.re-Real.sqrt κ*p.2) :
      φ =ᶠ[𝓝 p] (fun z : ℂ × ℝ => boundaryDensity κ α β z.1 z.2) := by
    have hb : p ∈ Metric.ball (0:ℂ × ℝ) cut.rIn := by
      simpa only [Metric.mem_ball,dist_zero_right] using (show ‖p‖ < R+1 by linarith)
    filter_upwards [cut.eventuallyEq_one_of_mem_ball hb,smoothBoundaryDensity_eventuallyEq κ α β ha p hp] with z hz he
    simp only [φ,hz,Pi.one_apply,one_mul,he]
  refine ⟨φ,cut.contDiff.mul (smoothBoundaryDensity_contDiff κ α β ha),cut.hasCompactSupport.mul_right,
    (fun q b h h' => (hnear (q,b) h h').eq_of_nhds),?_,?_⟩
  · intro q b h h'
    exact (hnear (q,b) h h').fderiv_eq
  · intro q b h h'
    exact ((hnear (q,b) h h').comp_tendsto ((continuous_const.prodMk continuous_id).tendsto b)).iteratedDeriv_eq 2

lemma compact_boundary_drift_zero (κ α β a : ℝ) (hκ : 0 < κ) (ha : 0 < a)
    (hβ : -α-2+κ*(β+1)/2 = 0) (φ : ℂ × ℝ → ℝ) (q : ℂ) (b : ℝ)
    (hD : fderiv ℝ φ (q,b) = fderiv ℝ (fun p : ℂ × ℝ => boundaryDensity κ α β p.1 p.2) (q,b))
    (h2 : iteratedDeriv 2 (fun x => φ (q,x)) b = iteratedDeriv 2 (boundaryDensity κ α β q) b)
    (hx : 2*a < q.re-Real.sqrt κ*b) :
    fderiv ℝ φ (q,b) (boundaryClockField a (Real.sqrt κ*b) q,0) +
      (1/2:ℝ)*iteratedDeriv 2 (fun x => φ (q,x)) b = 0 := by
  have hgap : a ≤ q.re-Real.sqrt κ*b := by linarith
  have he : boundaryClockField a (Real.sqrt κ*b) q =
      ((2/(q.re-Real.sqrt κ*b):ℝ):ℂ) + (((q.re-Real.sqrt κ*b)⁻¹^2:ℝ):ℂ)*I := by
    simp only [boundaryClockField,positiveBoundaryField_eq hgap,max_eq_right hgap]
  rw [hD,h2,he,boundaryDensity_generator κ α β hκ.le q b (by linarith),hβ,mul_zero,zero_div]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

theorem BoundaryClockSolution.stopped_boundary_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ a : ℝ} {q₀ : ℂ}
    (c : BoundaryClockSolution B hm κ a q₀)
    (hκ : 0 < κ) (ha : 0 < a) (α β : ℝ)
    (hβ : -α-2+κ*(β+1)/2 = 0)
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ 2*a < (c.Q t ω).re-Real.sqrt κ*B t ω) :
    Integrable (fun ω => boundaryDensity κ α β (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, boundaryDensity κ α β (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
        boundaryDensity κ α β q₀ 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_boundary_field κ α β a R ha hR
  let L₀ : ℝ≥0 := ⟨2*a⁻¹+a⁻¹^2,by positivity⟩
  have hL₀ := boundaryClockField_bound ha
  let V (t : ℝ) (ω : Ω) :=
    boundaryClockField a (Real.sqrt κ * B t.toNNReal ω) (c.Q t ω)
  have hBr : Measurable (fun p : ℝ × Ω => Real.sqrt κ * B p.1.toNNReal p.2) :=
    (hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      measurable_snd)).const_mul _
  have hpair : Measurable (fun p : ℝ × Ω =>
      (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)) := hBr.prodMk c.measurable
  have hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2) := by
    change Measurable ((fun p : ℝ × ℂ => boundaryClockField a p.1 p.2) ∘
      (fun p : ℝ × Ω => (Real.sqrt κ * B p.1.toNNReal p.2, c.Q p.1 p.2)))
    exact (continuous_boundaryClockField ha).measurable.comp hpair
  have hVb (t : ℝ) (ω : Ω) : ‖V t ω‖ ≤ (max c.L L₀ : ℝ≥0) :=
    (hL₀ _ _).trans (by exact_mod_cast le_max_right c.L L₀)
  obtain ⟨K, hfield⟩ := compact_state_smooth_brownian_field B hm c.Q V (max c.L L₀)
    c.measurable c.adapted (fun ω => (c.lipschitz ω).weaken (le_max_left _ _)) hVm hVb
    (fun t ω ht => c.derivative ω t ht) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (c.Q t ω, x)
  let drift (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (c.Q t ω, x) (V t ω, 0)
  have hzero (ω : Ω) (u : ℝ) (hu : 0 ≤ u) (hut : u < (τ ω : ℝ)) :
      brownianFieldDrift B F drift u ω = 0 := by
    have ht : u.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr hut.le
    obtain ⟨hball, hgap⟩ := hinside ω u.toNNReal ht
    change fderiv ℝ φ (c.Q (u.toNNReal : ℝ) ω, B u.toNNReal ω)
      (V (u.toNNReal : ℝ) ω, 0) + _ = 0
    dsimp only [V]
    rw [Real.toNNReal_coe]
    exact compact_boundary_drift_zero κ α β a hκ ha hβ φ _ _
      (hφD _ _ hball hgap) (hφ2 _ _ hball hgap) hgap
  have hopt := brownian_time_field_optional hB hm hBm hBc K F drift hfield τ hτ T hb hzero
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
      boundaryDensity κ α β (c.Q (τ ω) ω) (B (τ ω) ω) :=
    hφeq _ _ (hinside ω (τ ω) le_rfl).1 (hinside ω (τ ω) le_rfl).2
  refine ⟨hfi.congr (Eventually.of_forall hfeq), ?_⟩
  calc
    _ = ∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (hfeq ω).symm)
    _ = ∫ ω, F 0 ω (B 0 ω) ∂P := hopt
    _ = ∫ _, boundaryDensity κ α β q₀ 0 ∂P := by
      apply integral_congr_ae
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hB0
      change φ (c.Q 0 ω, B 0 ω) = _
      have hh : ‖(c.Q 0 ω, B 0 ω)‖ ≤ R := by
        simpa only [NNReal.coe_zero] using (hinside ω 0 zero_le).1
      rw [hφeq _ _ hh (hinside ω 0 zero_le).2, c.initial ω, hB0]
    _ = boundaryDensity κ α β q₀ 0 := by simp

end SLEExactGauge
end

 
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

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma radialLogPower_contDiff (κ β : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => radialLogPower κ β zz.1 zz.2) := by
  have hre : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => zz.1.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst.fst
  have him : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => zz.1.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst.fst
  have hN : ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => greenLogNormSq κ zz.1 zz.2) :=
    ((hre.sub (contDiff_const.mul contDiff_snd)).pow 2).add ((contDiff_const.mul him).exp)
  exact (contDiff_const.mul (hN.log (fun zz => (greenLogNormSq_pos κ zz.1 zz.2).ne'))).exp

lemma heightLogPower_contDiff (β : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => heightLogPower β zz.1) :=
  (contDiff_const.mul (Complex.imCLM.contDiff.comp contDiff_fst.fst)).exp

lemma swallowLyapunov_contDiff (κ β C : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun zz : (ℂ × ℝ) × ℝ => swallowLyapunov κ β C zz.1 zz.2) :=
  (radialLogPower_contDiff κ β).add (contDiff_const.mul (heightLogPower_contDiff β))

lemma radialLogPower_directional (κ β : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q v =
      radialLogPower κ β q x * β *
        ((q.1.re-Real.sqrt κ*x)*v.1.re + Real.exp (2*q.1.im)*v.1.im) /
          greenLogNormSq κ q x := by
  have hzre : HasDerivAt (fun t : ℝ => (q+t • v).1.re) v.1.re 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_re, Complex.smul_re, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.re).const_add q.1.re
  have hzim : HasDerivAt (fun t : ℝ => (q+t • v).1.im) v.1.im 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_im, Complex.smul_im, smul_eq_mul,
      id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v.1.im).const_add q.1.im
  have hN : HasDerivAt (fun t : ℝ => greenLogNormSq κ (q+t • v) x)
      (2*(q.1.re-Real.sqrt κ*x)*v.1.re + 2*Real.exp (2*q.1.im)*v.1.im) 0 := by
    convert ((hzre.sub_const (Real.sqrt κ*x)).pow 2).add ((hzim.const_mul 2).exp) using 1 <;> try rfl
    simp only [zero_smul, add_zero, Nat.cast_ofNat]
    ring
  have hcalc := ((hN.log (by simpa only [zero_smul, add_zero] using
    (greenLogNormSq_pos κ q x).ne')).const_mul (β/2)).exp
  have hline : HasDerivAt (fun t : ℝ => radialLogPower κ β (q+t • v) x)
      (radialLogPower κ β q x * β *
        ((q.1.re-Real.sqrt κ*x)*v.1.re+Real.exp (2*q.1.im)*v.1.im)/greenLogNormSq κ q x) 0 := by
    convert hcalc using 1 <;> try rfl
    simp only [zero_smul, add_zero]
    dsimp only [radialLogPower]
    ring
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℂ × ℝ => radialLogPower κ β r x) :=
    (radialLogPower_contDiff κ β).comp (contDiff_id.prodMk contDiff_const)
  have haff : HasDerivAt (fun t : ℝ => q+t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (fun r : ℂ × ℝ => radialLogPower κ β r x)
      (fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q) (q+(0 : ℝ) • v) := by
    simpa using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hchain := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hchain.unique hline

lemma radialLogPower_spatial_deriv (κ β : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    HasDerivAt (radialLogPower κ β q)
      (-radialLogPower κ β q x*β*Real.sqrt κ*(q.1.re-Real.sqrt κ*x)/greenLogNormSq κ q x) x := by
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2*(q.1.re-Real.sqrt κ*x)*(-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2*q.1.im)) using 1 <;> try rfl
    simp
  convert ((hN.log (greenLogNormSq_pos κ q x).ne').const_mul (β/2)).exp using 1 <;> try rfl
  dsimp only [radialLogPower]
  ring

lemma radialLogPower_spatial_second (κ β : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    iteratedDeriv 2 (radialLogPower κ β q) x =
      radialLogPower κ β q x*κ*β*
        ((β-1)*(q.1.re-Real.sqrt κ*x)^2+Real.exp (2*q.1.im))/(greenLogNormSq κ q x)^2 := by
  have hd : deriv (radialLogPower κ β q) = fun x =>
      -radialLogPower κ β q x*β*Real.sqrt κ*(q.1.re-Real.sqrt κ*x)/greenLogNormSq κ q x :=
    funext fun x => (radialLogPower_spatial_deriv κ β q x).deriv
  have hX := (hasDerivAt_const x q.1.re).sub ((hasDerivAt_id x).const_mul (Real.sqrt κ))
  have hN : HasDerivAt (greenLogNormSq κ q)
      (2*(q.1.re-Real.sqrt κ*x)*(-Real.sqrt κ)) x := by
    convert (hX.pow 2).add_const (Real.exp (2*q.1.im)) using 1 <;> try rfl
    simp
  have hs := ((((radialLogPower_spatial_deriv κ β q x).neg.mul_const β).mul_const (Real.sqrt κ)).mul hX).div hN
    (greenLogNormSq_pos κ q x).ne'
  rw [show (2 : ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd]
  dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.neg_apply, id_eq] at hs
  change HasDerivAt (fun y => -radialLogPower κ β q y * β * Real.sqrt κ *
    (q.1.re-Real.sqrt κ*y)/greenLogNormSq κ q y) _ x at hs
  rw [hs.deriv]
  have hn := (greenLogNormSq_pos κ q x).ne'
  dsimp only [greenLogNormSq] at hn ⊢
  generalize radialLogPower κ β q x = f
  generalize q.1.re-Real.sqrt κ*x = X at hn ⊢
  generalize Real.exp (2*q.1.im) = Y at hn ⊢
  have hk := Real.sq_sqrt hκ
  generalize Real.sqrt κ = r at *
  rw [← hk]
  field_simp [hn]
  ring

lemma radialLogPower_generator (κ β : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q
        (physicalLogLoewnerField (Real.sqrt κ*x) q) +
      (1/2 : ℝ)*iteratedDeriv 2 (radialLogPower κ β q) x =
      β*radialLogPower κ β q x*
        ((2+κ*(β-1)/2)*(q.1.re-Real.sqrt κ*x)^2+(κ/2-2)*Real.exp (2*q.1.im)) /
          (greenLogNormSq κ q x)^2 := by
  rw [radialLogPower_directional, radialLogPower_spatial_second κ β hκ]
  obtain ⟨hre,him,_⟩ := physicalLogLoewnerField_components κ q x
  rw [hre,him]
  ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma heightLogPower_directional (β : ℝ) (q v : ℂ × ℝ) :
    fderiv ℝ (heightLogPower β) q v = heightLogPower β q * β * v.1.im := by
  have hzim : HasDerivAt (fun t : ℝ => (q+t • v).1.im) v.1.im 0 := by
    simpa only [Prod.fst_add, Prod.smul_fst, Complex.add_im, Complex.smul_im,
      smul_eq_mul, id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const v.1.im).const_add q.1.im
  have hline : HasDerivAt (fun t : ℝ => heightLogPower β (q+t • v))
      (heightLogPower β q*β*v.1.im) 0 := by
    convert (hzim.const_mul β).exp using 1 <;> try rfl
    simp only [zero_smul, add_zero, heightLogPower]
    ring
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (heightLogPower β) :=
    (contDiff_const.mul (Complex.imCLM.contDiff.comp contDiff_fst)).exp
  have haff : HasDerivAt (fun t : ℝ => q+t • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q
  have hfd : HasFDerivAt (heightLogPower β) (fderiv ℝ (heightLogPower β) q)
      (q+(0 : ℝ) • v) := by
    simpa using ((hcd.differentiable (by simp)) q).hasFDerivAt
  have hc := hfd.comp_hasDerivAt 0 haff
  simpa only [Function.comp_def] using hc.unique hline

lemma swallowLyapunov_generator (κ β C : ℝ) (hκ : 0 ≤ κ) (q : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => swallowLyapunov κ β C r x) q
        (physicalLogLoewnerField (Real.sqrt κ*x) q) +
      (1/2 : ℝ)*iteratedDeriv 2 (swallowLyapunov κ β C q) x =
      swallowGenerator κ β C q x := by
  have hr : DifferentiableAt ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q :=
    (((radialLogPower_contDiff κ β).comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp)) q
  have hh : DifferentiableAt ℝ (heightLogPower β) q :=
    ((show ContDiff ℝ (⊤ : ℕ∞) (heightLogPower β) from
      (contDiff_const.mul (Complex.imCLM.contDiff.comp contDiff_fst)).exp).differentiable (by simp)) q
  have hd : fderiv ℝ (fun r : ℂ × ℝ => swallowLyapunov κ β C r x) q =
      fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q +
        C • fderiv ℝ (heightLogPower β) q := by
    exact (hr.hasFDerivAt.add (hh.hasFDerivAt.const_mul C)).fderiv
  have h2 : iteratedDeriv 2 (swallowLyapunov κ β C q) x =
      iteratedDeriv 2 (radialLogPower κ β q) x := by
    unfold swallowLyapunov
    simp_rw [add_comm]
    exact iteratedDeriv_const_add (by decide) _
  rw [hd, h2, add_apply, smul_apply,
    smul_eq_mul, heightLogPower_directional]
  have he := radialLogPower_generator κ β hκ q x
  obtain ⟨_, him, _⟩ := physicalLogLoewnerField_components κ q x
  rw [him]
  unfold swallowGenerator
  calc
    _ = (fderiv ℝ (fun r : ℂ × ℝ => radialLogPower κ β r x) q
        (physicalLogLoewnerField (Real.sqrt κ*x) q) +
        (1/2 : ℝ)*iteratedDeriv 2 (radialLogPower κ β q) x) -
        2*C*β*heightLogPower β q/greenLogNormSq κ q x := by ring
    _ = _ := by rw [he]

lemma radialLogPower_pos (κ β : ℝ) (q : ℂ × ℝ) (x : ℝ) :
    0 < radialLogPower κ β q x := Real.exp_pos _
lemma heightLogPower_pos (β : ℝ) (q : ℂ × ℝ) :
    0 < heightLogPower β q := Real.exp_pos _

 

lemma height_radial_ratio (κ β : ℝ) (_hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (q : ℂ × ℝ) (x : ℝ) :
    radialLogPower κ β q x * Real.exp (2*q.1.im) ≤
      heightLogPower β q * greenLogNormSq κ q x := by
  have hN := greenLogNormSq_pos κ q x
  have hle : Real.exp (2*q.1.im) ≤ greenLogNormSq κ q x := by
    unfold greenLogNormSq
    nlinarith [sq_nonneg (q.1.re-Real.sqrt κ*x)]
  have hlog : 2*q.1.im ≤ Real.log (greenLogNormSq κ q x) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hle
  unfold radialLogPower heightLogPower
  rw [← Real.exp_add, ← Real.exp_log hN, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Real.log_exp]
  nlinarith [mul_nonneg (sub_nonneg.mpr hβ2) (sub_nonneg.mpr hlog)]

lemma swallowGenerator_negative (κ : ℝ) (hκ : 4 < κ) (q : ℂ × ℝ) (x : ℝ) :
    swallowGenerator κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q x ≤
      -((κ-4)/(2*κ))*((κ-4)/4)*radialLogPower κ ((κ-4)/(2*κ)) q x /
        greenLogNormSq κ q x := by
  let β := (κ-4)/(2*κ)
  have hk : 0 < κ := by linarith
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ2 : β ≤ 2 := by dsimp [β]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hratio := height_radial_ratio κ β hβ.le hβ2 q x
  have hn := greenLogNormSq_pos κ q x
  have hc : 2+κ*(β-1)/2 = -(κ-4)/4 := by dsimp [β]; field_simp; ring
  change swallowGenerator κ β (3*(κ-4)/8) q x ≤ -β*((κ-4)/4)*radialLogPower κ β q x /
    greenLogNormSq κ q x
  unfold swallowGenerator
  rw [hc]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hn)).mp
  field_simp [hn.ne']
  dsimp only [greenLogNormSq] at hratio ⊢
  nlinarith [mul_nonneg (mul_nonneg hβ.le (sub_nonneg.mpr hκ.le)) (sub_nonneg.mpr hratio)]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma greenLogNormSq_continuous (κ : ℝ) :
    Continuous (fun v : (ℂ × ℝ) × ℝ => greenLogNormSq κ v.1 v.2) := by
  unfold greenLogNormSq
  fun_prop

lemma exists_radialLocalization
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (R : ℝ) (T : ℝ≥0)
    (hN : greenLogNormSq κ q₀ 0 ≤ R^2) (hlo : lo ≤ q₀.1.im) :
    Nonempty (RadialLocalization c R T) := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let D (t : ℝ≥0) (ω : Ω) := min (R^2-greenLogNormSq κ (c.Q t ω) (B t ω)) ((c.Q t ω).1.im-lo)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hDa : Adapted f D := by
    intro t
    have hQ := c.adapted t
    let : MeasurableSpace Ω := f t
    exact (measurable_const.sub ((greenLogNormSq_continuous κ).measurable.comp
      (hQ.prodMk (hBa t)))).min ((Complex.continuous_im.measurable.comp hQ.fst).sub_const lo)
  have hDc (ω : Ω) : Continuous (fun t => D t ω) := by
    have hQ := (c.lipschitz ω).continuous.comp NNReal.continuous_coe
    exact (continuous_const.sub ((greenLogNormSq_continuous κ).comp (hQ.prodMk (hBc ω)))).min
      ((Complex.continuous_im.comp hQ.fst).sub continuous_const)
  have hD0 (ω : Ω) : 0 ≤ D 0 ω := by
    simpa only [D, NNReal.coe_zero, c.initial, hB0, le_min_iff, sub_nonneg] using And.intro hN hlo
  obtain ⟨τ,hτ,hb,hin,hpre,hbd⟩ := first_margin_stopping f D hDa hDc hD0 T
  refine ⟨⟨τ,hτ,hb,?_,?_,?_⟩⟩
  · intro ω t ht
    simpa only [D, le_min_iff, sub_nonneg] using hin ω t ht
  · intro ω t ht
    simpa only [D, lt_min_iff, sub_pos] using hpre ω t ht
  · intro ω ht
    have hh := hbd ω ht
    dsimp only [D] at hh
    rw [min_eq_iff] at hh
    rcases hh with ⟨h,_⟩ | ⟨h,_⟩
    · exact Or.inl (sub_eq_zero.mp h).symm
    · exact Or.inr (sub_eq_zero.mp h)

namespace RadialLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    {c : ClippedLogSolution B hm κ lo hi hle q₀} {R : ℝ} {T : ℝ≥0}
lemma height_le_initial (a : RadialLocalization c R T) (ω : Ω) (t : ℝ≥0) (ht : t ≤ a.τ ω) :
    (c.Q t ω).1.im ≤ q₀.1.im := by
  have hd : ∀ s ∈ Icc 0 (T : ℝ), HasDerivWithinAt (fun s => c.Q s ω)
      (clippedLogLoewnerField lo hi hle (Real.sqrt κ*B s.toNNReal ω) (c.Q s ω))
      (Icc 0 (T : ℝ)) s := by
    intro s hs
    exact (c.derivative ω s hs.1).mono (fun s hs => hs.1)
  have hanti : AntitoneOn (fun s : ℝ => (c.Q s ω).1.im) (Icc 0 (T : ℝ)) :=
    clipped_log_height_antitone (U := fun u => Real.sqrt κ*B u ω)
      (Q := fun s => c.Q s ω) T hd
  have htT : (t : ℝ) ≤ T := NNReal.coe_le_coe.mpr (ht.trans (a.bounded ω))
  have hh : (c.Q t ω).1.im ≤ (c.Q 0 ω).1.im :=
    hanti ⟨le_rfl,T.coe_nonneg⟩ ⟨t.coe_nonneg,htT⟩ t.coe_nonneg
  rw [c.initial ω] at hh
  exact hh

lemma chart_identification (a : RadialLocalization c R T)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) {z : ℂ} (hz : z ∈ upperHalfPlane)
    (hq : q₀ = initialLogCoordinates z) (hhi : q₀.1.im ≤ hi)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) γ G F) :
    z ∈ survivingDomain γ (a.τ ω) ∧
      ∀ t : ℝ≥0, t ≤ a.τ ω → c.Q t ω = logLoewnerCoordinates G z t := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 (a.τ ω : ℝ)) := (c.derivative ω s hs.1).mono
    (show Icc (0 : ℝ) (a.τ ω : ℝ) ⊆ Ici 0 from fun s hs => hs.1)
  obtain ⟨hl,he⟩ := clipped_log_identification_of_endpoint ((hBc ω).const_mul _) hw
    (a.τ ω) z hz lo hi hle (fun t => c.Q t ω) ((c.initial ω).trans hq) hd
    (a.inside ω (a.τ ω) le_rfl).2
    (by simpa [hq, initialLogCoordinates] using hhi)
  exact ⟨hl,fun t ht => he ⟨t.coe_nonneg,by exact_mod_cast ht⟩⟩
end RadialLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma radialLogPower_le (κ β : ℝ) (hβ : 0 ≤ β) (q : ℂ × ℝ) (x R : ℝ)
    (_hR : 0 < R) (hN : greenLogNormSq κ q x ≤ R^2) :
    radialLogPower κ β q x ≤ Real.exp (β*Real.log R) := by
  have hl := Real.log_le_log (greenLogNormSq_pos κ q x) hN
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  unfold radialLogPower
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hl)]

lemma heightLogPower_le (κ β : ℝ) (hβ : 0 ≤ β) (q : ℂ × ℝ) (x R : ℝ)
    (_hR : 0 < R) (hN : greenLogNormSq κ q x ≤ R^2) :
    heightLogPower β q ≤ Real.exp (β*Real.log R) := by
  have hy : Real.exp (2*q.1.im) ≤ R^2 := by
    unfold greenLogNormSq at hN
    nlinarith [sq_nonneg (q.1.re-Real.sqrt κ*x)]
  have hl := Real.log_le_log (Real.exp_pos _) hy
  rw [Real.log_exp,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  unfold heightLogPower
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hβ (sub_nonneg.mpr hl)]

lemma radialLogPower_div_lower (κ β : ℝ) (hβ : β ≤ 2) (q : ℂ × ℝ) (x R : ℝ)
    (_hR : 0 < R) (hN : greenLogNormSq κ q x ≤ R^2) :
    Real.exp ((β-2)*Real.log R) ≤ radialLogPower κ β q x/greenLogNormSq κ q x := by
  have hl := Real.log_le_log (greenLogNormSq_pos κ q x) hN
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have he : radialLogPower κ β q x/greenLogNormSq κ q x =
      Real.exp ((β/2-1)*Real.log (greenLogNormSq κ q x)) := by
    unfold radialLogPower
    conv_lhs => rhs; rw [← Real.exp_log (greenLogNormSq_pos κ q x)]
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr hl)]

lemma swallowGenerator_uniform_negative (κ : ℝ) (hκ : 4 < κ) (q : ℂ × ℝ) (x R : ℝ)
    (hR : 0 < R) (hN : greenLogNormSq κ q x ≤ R^2) :
    swallowGenerator κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q x ≤
      -(((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) := by
  let β := (κ-4)/(2*κ)
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ2 : β ≤ 2 := by dsimp [β]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hr := radialLogPower_div_lower κ β hβ2 q x R hR hN
  have ha : 0 ≤ β*((κ-4)/4) := by positivity
  have hm := mul_le_mul_of_nonneg_left hr ha
  have hg := swallowGenerator_negative κ hκ q x
  change swallowGenerator κ β (3*(κ-4)/8) q x ≤ -(β*((κ-4)/4)*Real.exp ((β-2)*Real.log R))
  dsimp only [β] at hm ⊢
  apply hg.trans
  convert neg_le_neg hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma norm_driver_of_radial_bound (κ R K : ℝ) (hκ : 0 < κ) (hR : 0 ≤ R)
    (q : ℂ × ℝ) (x : ℝ) (hq : ‖q‖ ≤ K) (hN : greenLogNormSq κ q x ≤ R^2) :
    |x| ≤ (K+R)/Real.sqrt κ := by
  have hX : |q.1.re-Real.sqrt κ*x| ≤ R := by
    rw [abs_le]
    have hp := Real.exp_pos (2*q.1.im)
    unfold greenLogNormSq at hN
    constructor <;> nlinarith
  have hqre : |q.1.re| ≤ K := (Complex.abs_re_le_norm _).trans ((norm_fst_le q).trans hq)
  have hx : |Real.sqrt κ*x| ≤ K+R := by
    calc
      _ = |q.1.re-(q.1.re-Real.sqrt κ*x)| := by congr 1; ring
      _ ≤ |q.1.re|+|q.1.re-Real.sqrt κ*x| := abs_sub _ _
      _ ≤ K+R := add_le_add hqre hX
  rw [abs_mul,abs_of_pos (Real.sqrt_pos.2 hκ)] at hx
  exact (le_div_iff₀ (Real.sqrt_pos.2 hκ)).mpr (by simpa only [mul_comm] using hx)

lemma swallowLyapunov_nonneg (κ β C : ℝ) (hC : 0 ≤ C) (q : ℂ × ℝ) (x : ℝ) :
    0 ≤ swallowLyapunov κ β C q x := by
  exact add_nonneg (radialLogPower_pos κ β q x).le (mul_nonneg hC (heightLogPower_pos β q).le)

lemma radialLogPower_at_boundary (κ β : ℝ) (q : ℂ × ℝ) (x R : ℝ)
    (hN : greenLogNormSq κ q x = R^2) :
    radialLogPower κ β q x = Real.exp (β*Real.log R) := by
  unfold radialLogPower
  rw [hN, Real.log_pow]
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

lemma continuous_swallowGenerator (κ β C : ℝ) :
    Continuous (fun v : (ℂ × ℝ) × ℝ => swallowGenerator κ β C v.1 v.2) := by
  have hN : Continuous (fun v : (ℂ × ℝ) × ℝ => greenLogNormSq κ v.1 v.2) := by
    unfold greenLogNormSq
    fun_prop
  have hf := (radialLogPower_contDiff κ β).continuous
  have hh := (heightLogPower_contDiff β).continuous
  unfold swallowGenerator
  apply Continuous.sub
  · apply Continuous.div
    · exact (continuous_const.mul hf).mul (by fun_prop)
    · exact hN.pow 2
    · intro v; exact pow_ne_zero 2 (greenLogNormSq_pos κ v.1 v.2).ne'
  · exact (continuous_const.mul hh).div hN (fun v => (greenLogNormSq_pos κ v.1 v.2).ne')

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma swallowLyapunov_pair_directional (κ p a : ℝ) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun zz : (ℂ × ℝ) × ℝ => swallowLyapunov κ p a zz.1 zz.2) (q, x) (v, 0) =
      fderiv ℝ (fun r : ℂ × ℝ => swallowLyapunov κ p a r x) q v := by
  have hd := ((swallowLyapunov_contDiff κ p a).differentiable (by simp)) (q, x)
  have hp := (hasFDerivAt_id (𝕜 := ℝ) q).prodMk (hasFDerivAt_const (𝕜 := ℝ) (E := ℂ × ℝ) x q)
  have hc := (hd.hasFDerivAt.comp q hp).fderiv
  have he := congrArg (fun D : (ℂ × ℝ) →L[ℝ] ℝ => D v) hc
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, id_eq, zero_apply] using he.symm

 

lemma exists_compact_swallow_field (κ p a R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : (ℂ × ℝ) × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ q x, ‖(q, x)‖ ≤ R → φ (q, x) = swallowLyapunov κ p a q x) ∧
      (∀ q x, ‖(q, x)‖ ≤ R →
        fderiv ℝ φ (q, x) = fderiv ℝ (fun zz : (ℂ × ℝ) × ℝ => swallowLyapunov κ p a zz.1 zz.2) (q, x)) ∧
      (∀ q x, ‖(q, x)‖ ≤ R → iteratedDeriv 2 (fun y => φ (q, y)) x =
        iteratedDeriv 2 (swallowLyapunov κ p a q) x) := by
  let b : ContDiffBump (0 : (ℂ × ℝ) × ℝ) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let φ (zz : (ℂ × ℝ) × ℝ) : ℝ := b zz * swallowLyapunov κ p a zz.1 zz.2
  have hnear (zz : (ℂ × ℝ) × ℝ) (hp : ‖zz‖ ≤ R) :
      φ =ᶠ[𝓝 zz] (fun r : (ℂ × ℝ) × ℝ => swallowLyapunov κ p a r.1 r.2) := by
    have hball : zz ∈ Metric.ball (0 : (ℂ × ℝ) × ℝ) b.rIn := by
      simp only [Metric.mem_ball, dist_zero_right]
      change ‖zz‖ < R + 1
      linarith
    filter_upwards [b.eventuallyEq_one_of_mem_ball hball] with r hr
    simp only [φ, hr, Pi.one_apply, one_mul]
  refine ⟨φ, b.contDiff.mul (swallowLyapunov_contDiff κ p a), b.hasCompactSupport.mul_right,
    (fun q x h => (hnear (q, x) h).eq_of_nhds), ?_, ?_⟩
  · intro q x h
    exact (hnear (q, x) h).fderiv_eq
  · intro q x h
    have he := (hnear (q, x) h).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)
    exact he.iteratedDeriv_eq 2

end SLEExactGauge
end

 
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

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma compact_swallow_drift
    (κ p α : ℝ) (hκ : 0 ≤ κ) (lo hi : ℝ) (hle : lo ≤ hi)
    (φ : (ℂ × ℝ) × ℝ → ℝ) (q : ℂ × ℝ) (x : ℝ)
    (hφD : fderiv ℝ φ (q, x) =
      fderiv ℝ (fun r : (ℂ × ℝ) × ℝ => swallowLyapunov κ p α r.1 r.2) (q, x))
    (hφ2 : iteratedDeriv 2 (fun y => φ (q, y)) x =
      iteratedDeriv 2 (swallowLyapunov κ p α q) x)
    (hq : q.1.im ∈ Icc lo hi) :
    fderiv ℝ φ (q, x)
        (clippedLogLoewnerField lo hi hle (Real.sqrt κ * x) q, 0) +
      (1 / 2 : ℝ) * iteratedDeriv 2 (fun y => φ (q, y)) x =
        swallowGenerator κ p α q x := by
  rw [hφD, hφ2, swallowLyapunov_pair_directional,
    clippedLogLoewnerField_eq_physical lo hi hle _ _ hq]
  exact swallowLyapunov_generator κ p α hκ q x

 

theorem ClippedLogSolution.stopped_swallow_dynkin
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
    Integrable (fun ω => swallowLyapunov κ p α (c.Q (τ ω) ω) (B (τ ω) ω)) P ∧
      (∫ ω, swallowLyapunov κ p α (c.Q (τ ω) ω) (B (τ ω) ω) ∂P) =
        swallowLyapunov κ p α q₀ 0 +
        ∫ ω, (∫ t in (0 : ℝ)..(τ ω : ℝ),
          swallowGenerator κ p α (c.Q t ω) (B t.toNNReal ω)) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_swallow_field κ p α R hR
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
        swallowGenerator κ p α (c.Q t ω) (B t.toNNReal ω) := by
    have ht' : t.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr ht.2
    obtain ⟨hball, hlo, hhi⟩ := hinside ω t.toNNReal ht'
    have he : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.1
    change fderiv ℝ φ (c.Q (t.toNNReal : ℝ) ω, B t.toNNReal ω)
      (V (t.toNNReal : ℝ) ω, 0) + _ = _
    dsimp only [V]
    rw [Real.toNNReal_coe]
    have hh := compact_swallow_drift κ p α hκ lo hi hle φ _ _
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
      swallowLyapunov κ p α (c.Q (τ ω) ω) (B (τ ω) ω) :=
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
          _ = ∫ _, swallowLyapunov κ p α q₀ 0 ∂P := by
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

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

lemma ClippedLogSolution.swallow_generator_measurable
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (β C : ℝ) :
    Measurable (fun p : ℝ × Ω => swallowGenerator κ β C (c.Q p.1 p.2) (B p.1.toNNReal p.2)) := by
  have hBr : Measurable (fun p : ℝ × Ω => B p.1.toNNReal p.2) :=
    hBm.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hp : Measurable (fun p : ℝ × Ω => (c.Q p.1 p.2, B p.1.toNNReal p.2)) :=
    c.measurable.prodMk hBr
  have hh := (continuous_swallowGenerator κ β C).measurable.comp hp
  dsimp only [Function.comp_def] at hh
  with_reducible exact hh

lemma ClippedLogSolution.swallow_generator_continuous
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (β C : ℝ) (ω : Ω) :
    Continuous (fun t : ℝ => swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)) := by
  have hB : Continuous (fun t : ℝ => B t.toNNReal ω) :=
    (hBc ω).comp continuous_real_toNNReal
  have hQ : Continuous (fun t : ℝ => c.Q t ω) := (c.lipschitz ω).continuous
  have hp : Continuous (fun t : ℝ => (c.Q t ω, B t.toNNReal ω)) := hQ.prodMk hB
  have hh := (continuous_swallowGenerator κ β C).comp hp
  dsimp only [Function.comp_def] at hh
  with_reducible exact hh

lemma ClippedLogSolution.swallow_cumulative_integrable
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (c : ClippedLogSolution B hm κ lo hi hle q₀) (β C : ℝ)
    (τ : Ω → ℝ≥0) (hτm : Measurable τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ ω t, t ≤ τ ω → |swallowGenerator κ β C (c.Q t ω) (B t ω)| ≤ D) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(τ ω : ℝ),
      swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)) P := by
  let G (t : ℝ) (ω : Ω) := swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)
  have hGm : Measurable (Function.uncurry G) := c.swallow_generator_measurable hBm β C
  have hGb (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (hτ : t ≤ (τ ω : ℝ)) : |G t ω| ≤ D := by
    have hh := hbound ω t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hτ)
    simpa only [G, Real.coe_toNNReal t ht] using hh
  exact (bounded_stopped_cumulative_integrable (P := P) G hGm τ τ hτm
    (fun _ => le_rfl) T hτT D hD hGb).1

lemma bounded_nnreal_integrable {P : Measure Ω} [IsFiniteMeasure P]
    (τ : Ω → ℝ≥0) (hτm : Measurable τ) (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => (τ ω : ℝ)) P := by
  apply Integrable.of_bound ((NNReal.continuous_coe.measurable.comp hτm).aestronglyMeasurable) T
  exact Eventually.of_forall fun ω => by
    change ‖(τ ω : ℝ)‖ ≤ (T : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (τ ω).coe_nonneg]
    exact NNReal.coe_le_coe.mpr (hb ω)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RadialLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    {c : ClippedLogSolution B hm κ lo hi hle q₀} {R : ℝ} {T : ℝ≥0}

lemma exists_compact_bound (a : RadialLocalization c R T) (hκ : 0 < κ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω t, t ≤ a.τ ω → ‖(c.Q t ω, B t ω)‖ ≤ K := by
  let M : ℝ := ‖q₀‖+c.L*T
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨max M ((M+R)/Real.sqrt κ), le_max_of_le_left hM, ?_⟩
  intro ω t ht
  have hQ : ‖c.Q t ω‖ ≤ M := c.norm_le ω t T (ht.trans (a.bounded ω))
  have hB := norm_driver_of_radial_bound κ R M hκ hR (c.Q t ω) (B t ω) hQ (a.inside ω t ht).1
  rw [Prod.norm_def]
  exact max_le_max hQ (by simpa only [Real.norm_eq_abs] using hB)

lemma exists_generator_bound (a : RadialLocalization c R T)
    (hκ : 0 < κ) (hR : 0 ≤ R) (β C : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ω t, t ≤ a.τ ω →
      |swallowGenerator κ β C (c.Q t ω) (B t ω)| ≤ D := by
  obtain ⟨K,hK,hbound⟩ := a.exists_compact_bound hκ hR
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0 : (ℂ × ℝ) × ℝ) K).exists_bound_of_continuousOn
    (continuous_swallowGenerator κ β C).continuousOn
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro ω t ht
  have hmem : (c.Q t ω, B t ω) ∈ Metric.closedBall (0 : (ℂ × ℝ) × ℝ) K := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound ω t ht
  exact (hD _ hmem).trans (le_max_left _ _)

lemma generator_cumulative_integrable {P : Measure Ω} [IsFiniteMeasure P]
    (a : RadialLocalization c R T)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hκ : 0 < κ) (hR : 0 ≤ R) (β C : ℝ) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..(a.τ ω : ℝ),
      swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)) P := by
  obtain ⟨D,hD,hbound⟩ := a.exists_generator_bound hκ hR β C
  exact c.swallow_cumulative_integrable hBm β C a.τ
    (stopping_time_measurable_nnreal a.stopping) T a.bounded D hD hbound

lemma stopped_lyapunov_bound {P : Measure Ω}
    (a : RadialLocalization c R T)
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 4 < κ) (hR : 0 < R) (hhi : q₀.1.im ≤ hi) :
    Integrable (fun ω => swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8)
      (c.Q (a.τ ω) ω) (B (a.τ ω) ω)) P ∧
    (∫ ω, swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8)
      (c.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) +
      (((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) *
        (∫ ω, (a.τ ω : ℝ) ∂P) ≤ swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q₀ 0 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  let β := (κ-4)/(2*κ)
  let C := 3*(κ-4)/8
  let d := β*((κ-4)/4)*Real.exp ((β-2)*Real.log R)
  let G (t : ℝ) (ω : Ω) := swallowGenerator κ β C (c.Q t ω) (B t.toNNReal ω)
  obtain ⟨K,hK,hbound⟩ := a.exists_compact_bound hk hR.le
  have hmean := c.stopped_swallow_dynkin hB hBm hBc hk.le β C K hK a.τ a.stopping
    T a.bounded (fun ω t ht => ⟨hbound ω t ht, (a.inside ω t ht).2,
      (a.height_le_initial ω t ht).trans hhi⟩)
  refine ⟨hmean.1, ?_⟩
  have hτi : Integrable (fun ω => (a.τ ω : ℝ)) P :=
    bounded_nnreal_integrable a.τ (stopping_time_measurable_nnreal a.stopping) T a.bounded
  have hGi : Integrable (fun ω => ∫ t in (0 : ℝ)..(a.τ ω : ℝ), G t ω) P :=
    a.generator_cumulative_integrable hBm hk hR.le β C
  have hGle (ω : Ω) : (∫ t in (0 : ℝ)..(a.τ ω : ℝ), G t ω) ≤ -d*(a.τ ω : ℝ) := by
    have hGc : Continuous (fun t : ℝ => G t ω) := c.swallow_generator_continuous hBc β C ω
    have hh := intervalIntegral.integral_mono_on (a.τ ω).coe_nonneg
      (hGc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _ :
        IntervalIntegrable (fun _ : ℝ => -d) volume 0 (a.τ ω)) (fun t ht => by
          have hh := swallowGenerator_uniform_negative κ hκ (c.Q t.toNNReal ω)
            (B t.toNNReal ω) R hR
            (a.inside ω t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2)).1
          simpa only [G, Real.coe_toNNReal t ht.1] using hh)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hh
  have htotal := integral_mono hGi (hτi.const_mul (-d)) hGle
  rw [integral_const_mul] at htotal
  change (∫ ω, swallowLyapunov κ β C (c.Q (a.τ ω) ω) (B (a.τ ω) ω) ∂P) +
    d*(∫ ω, (a.τ ω : ℝ) ∂P) ≤ swallowLyapunov κ β C q₀ 0
  rw [hmean.2]
  linarith

end RadialLocalization
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

lemma nonnegative_integral_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Y : Ω → ℝ) (hYi : Integrable Y P) (hY0 : ∀ ω, 0 ≤ Y ω)
    (M a : ℝ) (ha : 0 < a) (hmean : (∫ ω, Y ω ∂P) ≤ M) :
    P {ω | a ≤ Y ω} ≤ ENNReal.ofReal (M/a) := by
  have hmark := meas_ge_le_lintegral_div hYi.aemeasurable.ennreal_ofReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top
  calc
    P {ω | a ≤ Y ω} ≤ P {ω | ENNReal.ofReal a ≤ ENNReal.ofReal (Y ω)} :=
      measure_mono (fun ω hω => ENNReal.ofReal_le_ofReal hω)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Y ω) ∂P) / ENNReal.ofReal a := hmark
    _ = ENNReal.ofReal (∫ ω, Y ω ∂P) / ENNReal.ofReal a := by
      rw [ofReal_integral_eq_lintegral_ofReal hYi (Eventually.of_forall hY0)]
    _ ≤ ENNReal.ofReal M / ENNReal.ofReal a :=
      ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hmean) _
    _ = ENNReal.ofReal (M/a) := (ENNReal.ofReal_div_of_pos ha).symm

namespace RadialLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    {c : ClippedLogSolution B hm κ lo hi hle q₀} {R : ℝ} {T : ℝ≥0}

lemma exit_probability {P : Measure Ω}
    (a : RadialLocalization c R T)
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 4 < κ) (hR : 0 < R) (hhi : q₀.1.im ≤ hi)
    (b : ℝ) (hb : 0 < b)
    (hbR : b ≤ Real.exp (((κ-4)/(2*κ))*Real.log R))
    (hbT : b ≤ (((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) * T) :
    P {ω | a.τ ω = T ∨ greenLogNormSq κ (c.Q (a.τ ω) ω) (B (a.τ ω) ω) = R^2} ≤
      ENNReal.ofReal (swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q₀ 0 / b) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let β := (κ-4)/(2*κ)
  let C := 3*(κ-4)/8
  let d := β*((κ-4)/4)*Real.exp ((β-2)*Real.log R)
  let F (ω : Ω) := swallowLyapunov κ β C (c.Q (a.τ ω) ω) (B (a.τ ω) ω)
  let Y (ω : Ω) := F ω + d*(a.τ ω : ℝ)
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hF0 (ω : Ω) : 0 ≤ F ω := swallowLyapunov_nonneg κ β C hC _ _
  have hY0 (ω : Ω) : 0 ≤ Y ω := add_nonneg (hF0 ω) (mul_nonneg hd (a.τ ω).coe_nonneg)
  have hmean := a.stopped_lyapunov_bound hB hBm hBc hκ hR hhi
  have hτi : Integrable (fun ω => (a.τ ω : ℝ)) P :=
    bounded_nnreal_integrable a.τ (stopping_time_measurable_nnreal a.stopping) T a.bounded
  have hYi : Integrable Y P := hmean.1.add (hτi.const_mul d)
  have hYmean : (∫ ω, Y ω ∂P) ≤ swallowLyapunov κ β C q₀ 0 := by
    rw [show (∫ ω, Y ω ∂P) = (∫ ω, F ω ∂P)+d*(∫ ω, (a.τ ω : ℝ) ∂P) by
      rw [show Y = fun ω => F ω+d*(a.τ ω : ℝ) from rfl,
        integral_add hmean.1 (hτi.const_mul d), integral_const_mul]]
    exact hmean.2
  apply (measure_mono (show {ω | a.τ ω = T ∨ greenLogNormSq κ (c.Q (a.τ ω) ω) (B (a.τ ω) ω) = R^2}
      ⊆ {ω | b ≤ Y ω} from ?_)).trans (nonnegative_integral_tail Y hYi hY0 _ b hb hYmean)
  intro ω hω
  rcases hω with ht | hn
  · change b ≤ F ω+d*(a.τ ω : ℝ)
    rw [ht]
    exact hbT.trans (le_add_of_nonneg_left (hF0 ω))
  · have hr := radialLogPower_at_boundary κ β (c.Q (a.τ ω) ω) (B (a.τ ω) ω) R hn
    have hh : Real.exp (β*Real.log R) ≤ F ω := by
      change Real.exp (β*Real.log R) ≤ radialLogPower κ β _ _ + C*heightLogPower β _
      rw [hr]
      exact le_add_of_nonneg_right (mul_nonneg hC (heightLogPower_pos β _).le)
    exact (hbR.trans hh).trans (le_add_of_nonneg_right (mul_nonneg hd (a.τ ω).coe_nonneg))

end RadialLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma exists_boundaryLocalization
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ a : ℝ} {q₀ : ℂ} (c : BoundaryClockSolution B hm κ a q₀)
    (ha : 0 < a) (α β R H : ℝ) (T : ℝ≥0)
    (hR : ‖(q₀,(0:ℝ))‖ ≤ R) (hx : 3*a ≤ q₀.re)
    (hH : boundaryDensity κ α β q₀ 0 ≤ H) :
    Nonempty (BoundaryLocalization c α β R H T) := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  let V (p : ℂ × ℝ) := min (R-‖p‖) (min (p.1.re-Real.sqrt κ*p.2-3*a)
    (H-smoothBoundaryDensity κ α β a p.1 p.2))
  have hVc : Continuous V := by
    exact (continuous_const.sub continuous_norm).min
      (((Complex.continuous_re.comp continuous_fst).sub (continuous_const.mul continuous_snd)).sub
        continuous_const |>.min (continuous_const.sub (smoothBoundaryDensity_contDiff κ α β ha).continuous))
  let D (t : ℝ≥0) (ω : Ω) := V (c.Q t ω,B t ω)
  have hBa : Adapted f B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  have hDa : Adapted f D := fun t => hVc.measurable.comp ((c.adapted t).prodMk (hBa t))
  have hDc (ω : Ω) : Continuous (fun t => D t ω) :=
    hVc.comp (((c.lipschitz ω).continuous.comp NNReal.continuous_coe).prodMk (hBc ω))
  have hD0 (ω : Ω) : 0 ≤ D 0 ω := by
    have he : smoothBoundaryDensity κ α β a q₀ 0 = boundaryDensity κ α β q₀ 0 :=
      smoothBoundaryDensity_eq ha (by simpa using (show 2*a ≤ q₀.re by linarith))
    simpa only [D,V,NNReal.coe_zero,c.initial,hB0,mul_zero,sub_zero,he,
      le_min_iff,sub_nonneg] using And.intro hR (And.intro hx hH)
  obtain ⟨τ,hτ,hb,hin,hpre,hbd⟩ := first_margin_stopping f D hDa hDc hD0 T
  have hin' (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ ω) : ‖(c.Q t ω,B t ω)‖ ≤ R ∧
      3*a ≤ (c.Q t ω).re-Real.sqrt κ*B t ω ∧ boundaryDensity κ α β (c.Q t ω) (B t ω) ≤ H := by
    have hh := hin ω t ht
    simp only [D,V,le_min_iff,sub_nonneg] at hh
    rw [smoothBoundaryDensity_eq ha (by linarith [hh.2.1])] at hh
    exact hh
  refine ⟨⟨τ,hτ,hb,hin',?_,?_⟩⟩
  · intro ω t ht
    have hh := hpre ω t ht
    simp only [D,V,lt_min_iff,sub_pos] at hh
    rw [smoothBoundaryDensity_eq ha (by linarith [hh.2.1])] at hh
    exact hh
  · intro ω ht
    have hh := hbd ω ht
    dsimp only [D,V] at hh
    rw [smoothBoundaryDensity_eq ha (by linarith [(hin' ω (τ ω) le_rfl).2.1])] at hh
    rw [min_eq_iff] at hh
    rcases hh with ⟨hh,_⟩ | ⟨hh,_⟩
    · exact Or.inl (sub_eq_zero.mp hh).symm
    · rw [min_eq_iff] at hh
      rcases hh with ⟨hh,_⟩ | ⟨hh,_⟩
      · exact Or.inr (Or.inl (sub_eq_zero.mp hh))
      · exact Or.inr (Or.inr (sub_eq_zero.mp hh).symm)

namespace BoundaryLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ a : ℝ} {q₀ : ℂ} {c : BoundaryClockSolution B hm κ a q₀}
    {α β R H : ℝ} {T : ℝ≥0}

lemma density_crossing_probability {P : Measure Ω}
    (l : BoundaryLocalization c α β R H T)
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (ha : 0 < a) (hβ : -α-2+κ*(β+1)/2=0)
    (hR : 0 ≤ R) (hH : 0 < H) :
    P {ω | H ≤ boundaryDensity κ α β (c.Q (l.τ ω) ω) (B (l.τ ω) ω)} ≤
      ENNReal.ofReal (boundaryDensity κ α β q₀ 0/H) := by
  obtain ⟨hi,he⟩ := c.stopped_boundary_density hB hBm hBc hκ ha α β hβ R hR
    l.τ l.stopping T l.bounded (fun ω t ht =>
      ⟨(l.inside ω t ht).1,by linarith [(l.inside ω t ht).2.1]⟩)
  exact nonnegative_integral_tail _ hi (fun ω => (Real.exp_pos _).le) _ _ hH he.le

end BoundaryLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge



namespace IsPositiveBoundaryClockPath
variable {U : ℝ≥0 → ℝ} {x : ℝ} {T : ℝ≥0} {Q : ℝ → ℂ}

lemma continuousOn (h : IsPositiveBoundaryClockPath U x T Q) :
    ContinuousOn Q (Icc 0 (T:ℝ)) := fun t ht => (h.2.2 t ht).continuousWithinAt

lemma positive_lower_bound (h : IsPositiveBoundaryClockPath U x T Q) (hU : Continuous U) :
    ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Icc 0 (T:ℝ), a ≤ (Q t).re-U t.toNNReal := by
  have hc : ContinuousOn (fun t : ℝ => (Q t).re-U t.toNNReal) (Icc 0 (T:ℝ)) :=
    (Complex.continuous_re.comp_continuousOn h.continuousOn).sub
      ((hU.comp continuous_real_toNNReal).continuousOn)
  obtain ⟨s,hs,hmin⟩ := (isCompact_Icc : IsCompact (Icc 0 (T:ℝ))).exists_isMinOn
    ⟨0,le_rfl,T.coe_nonneg⟩ hc
  exact ⟨_,h.2.1 s hs,fun t ht => hmin ht⟩

lemma clock_identity (h : IsPositiveBoundaryClockPath U x T Q) (hU : Continuous U) :
    (Q T).im = ∫ t in (0:ℝ)..(T:ℝ), ((Q t).re-U t.toNNReal)⁻¹^2 := by
  have hc : ContinuousOn (fun t : ℝ => ((Q t).re-U t.toNNReal)⁻¹^2) (Icc 0 (T:ℝ)) :=
    (((Complex.continuous_re.comp_continuousOn h.continuousOn).sub
      ((hU.comp continuous_real_toNNReal).continuousOn)).inv₀ (fun t ht => (h.2.1 t ht).ne')).pow 2
  have hd (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : HasDerivWithinAt (fun u => (Q u).im)
      (((Q t).re-U t.toNNReal)⁻¹^2) (Icc 0 (T:ℝ)) t := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,Complex.imCLM_apply,Complex.add_im,
      Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
      Complex.I_re,mul_zero,add_zero,zero_add] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (h.2.2 t ht)
  have hdr (t : ℝ) (ht : t ∈ Ioo 0 (T:ℝ)) : HasDerivWithinAt (fun u => (Q u).im)
      (((Q t).re-U t.toNNReal)⁻¹^2) (Ioi t) t := by
    exact (hasDerivWithinAt_Ici_of_Icc ⟨ht.1.le,ht.2⟩
      (hd t ⟨ht.1.le,ht.2.le⟩)).mono Ioi_subset_Ici_self
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le T.coe_nonneg
    (Complex.continuous_im.comp_continuousOn h.continuousOn) hdr
    (hc.intervalIntegrable_of_Icc T.coe_nonneg)
  dsimp only [Function.comp_def] at he
  rw [h.1,Complex.ofReal_im,sub_zero] at he
  exact he.symm

lemma clipped_identification
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {κ a : ℝ}
    (c : BoundaryClockSolution B hm κ a (x:ℂ)) (ha : 0 < a) (ω : Ω)
    (h : IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q)
    (hgap : ∀ t ∈ Icc 0 (T:ℝ), a ≤ (Q t).re-Real.sqrt κ*B t.toNNReal ω) :
    EqOn Q (fun t => c.Q t ω) (Icc 0 (T:ℝ)) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : HasDerivWithinAt Q
      (boundaryClockField a (Real.sqrt κ*B t.toNNReal ω) (Q t)) (Icc 0 (T:ℝ)) t := by
    simpa only [boundaryClockField,positiveBoundaryField_eq (hgap t ht),max_eq_right (hgap t ht)] using h.2.2 t ht
  have hc (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) := (c.derivative ω t ht.1).mono
    (show Icc (0:ℝ) (T:ℝ) ⊆ Ici 0 from fun s hs => hs.1)
  apply ODE_solution_unique (fun t => boundaryClockField_lipschitz ha (Real.sqrt κ*B t.toNNReal ω))
    h.continuousOn
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hd t ⟨ht.1,ht.2.le⟩))
    (c.lipschitz ω).continuous.continuousOn
    (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hc t ⟨ht.1,ht.2.le⟩))
  exact h.1.trans (c.initial ω).symm

end IsPositiveBoundaryClockPath
end SLEExactGauge
end

 
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

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RadialLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}
    {c : ClippedLogSolution B hm κ lo hi hle q₀} {R : ℝ} {T : ℝ≥0}

lemma alive_forces_radial_or_time_boundary (a : RadialLocalization c R T)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) {z : ℂ} (hz : z ∈ upperHalfPlane)
    (hq : q₀ = initialLogCoordinates z) (hhi : q₀.1.im ≤ hi)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) γ G F)
    (hlive : z ∈ survivingDomain γ T) (hlo : lo < Real.log (G T z).im) :
    a.τ ω = T ∨ greenLogNormSq κ (c.Q (a.τ ω) ω) (B (a.τ ω) ω) = R^2 := by
  rcases eq_or_lt_of_le (a.bounded ω) with h | h
  · exact Or.inl h
  rcases a.boundary ω h with hN | hh
  · exact Or.inr hN
  obtain ⟨_,he⟩ := a.chart_identification hBc hz hq hhi ω γ G F hw
  have hheight := (hw.log_height_bounds T z hlive (a.τ ω)
    ⟨(a.τ ω).coe_nonneg, NNReal.coe_le_coe.mpr (a.bounded ω)⟩).1
  rw [he (a.τ ω) le_rfl, logCoordinates_im] at hh
  simp only [Real.toNNReal_coe] at hheight
  exact False.elim (not_le_of_gt hlo (hh ▸ hheight))

end RadialLocalization

lemma measure_eventually_sets_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) (C : ℝ≥0∞) (hC : ∀ n, P (E n) ≤ C) :
    P {ω | ∀ᶠ n : ℕ in atTop, ω ∈ E n} ≤ C := by
  let H (n : ℕ) := ⋂ m ≥ n, E m
  have hH : Monotone H := by
    intro n m hnm ω hω
    simp only [H, mem_iInter] at hω ⊢
    exact fun k hk => hω k (hnm.trans hk)
  have he : {ω | ∀ᶠ n : ℕ in atTop, ω ∈ E n} = ⋃ n, H n := by
    ext ω
    simp only [mem_ofPred_eq, eventually_atTop, mem_iUnion, H, mem_iInter]
  rw [he, hH.measure_iUnion]
  apply iSup_le
  intro n
  apply (measure_mono (show H n ⊆ E n from fun ω hω => by
    exact mem_iInter.mp (mem_iInter.mp hω n) le_rfl)).trans (hC n)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace BoundaryLocalization
variable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ a x : ℝ} {c : BoundaryClockSolution B hm κ a (x:ℂ)}
    {α β R H : ℝ} {T : ℝ≥0}

 

lemma true_crossing_forces_density_boundary
    (l : BoundaryLocalization c α β R H T) (ha : 0 < a)
    (ω : Ω) (S : ℝ≥0) (hS : S < T) (Q : ℝ → ℂ)
    (hQ : IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x S Q)
    (hgap : ∀ t ∈ Icc 0 (S:ℝ), 3*a < (Q t).re-Real.sqrt κ*B t.toNNReal ω)
    (hbound : ∀ t : ℝ≥0, t ≤ S → ‖(Q t,B t ω)‖ < R)
    (hhit : H ≤ boundaryDensity κ α β (Q S) (B S ω)) :
    H ≤ boundaryDensity κ α β (c.Q (l.τ ω) ω) (B (l.τ ω) ω) := by
  have he := hQ.clipped_identification c ha ω (fun t ht => by linarith [hgap t ht])
  have hτS : l.τ ω ≤ S := by
    by_contra h
    have hpre := (l.before ω S (not_le.mp h)).2.2
    have heS : Q S = c.Q S ω := he ⟨S.coe_nonneg,le_rfl⟩
    rw [← heS] at hpre
    exact not_lt_of_ge hhit hpre
  have hτT : l.τ ω < T := hτS.trans_lt hS
  have heτ : Q (l.τ ω) = c.Q (l.τ ω) ω := he ⟨(l.τ ω).coe_nonneg,NNReal.coe_le_coe.mpr hτS⟩
  rcases l.boundary ω hτT with hnorm | hg | hf
  · have hb := hbound (l.τ ω) hτS
    rw [heτ,hnorm] at hb
    exact False.elim (lt_irrefl R hb)
  · have hp := hgap (l.τ ω) ⟨(l.τ ω).coe_nonneg,NNReal.coe_le_coe.mpr hτS⟩
    rw [Real.toNNReal_coe,heτ,hg] at hp
    exact False.elim (lt_irrefl _ hp)
  · exact hf.ge

end BoundaryLocalization
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

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem boundary_maximal_density_regular
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ α β x H : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hH : 0 < H)
    (hβ : -α-2+κ*(β+1)/2=0)
    (hH0 : boundaryDensity κ α β (x:ℂ) 0 ≤ H) :
    P {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (B T ω)} ≤
      ENNReal.ofReal (boundaryDensity κ α β (x:ℂ) 0 / H) := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let a (n : ℕ) : ℝ := (x/6)/((n:ℝ)+1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hax (n : ℕ) : 3*a n ≤ x := by
    have hn : 1 ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hh : a n ≤ x/6 := div_le_self (by positivity) hn
    linarith
  let R (n : ℕ) : ℝ := ‖((x:ℂ),(0:ℝ))‖+(n:ℝ)+1
  have hR (n : ℕ) : 0 ≤ R n := by dsimp [R]; positivity
  have hR0 (n : ℕ) : ‖((x:ℂ),(0:ℝ))‖ ≤ R n := by dsimp [R]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  let t (n : ℕ) : ℝ≥0 := ⟨(n:ℝ)+1,by positivity⟩
  let c (n : ℕ) := Classical.choice (exists_boundaryClockSolution B hm hBm hBc κ (a n) (ha n) (x:ℂ))
  let l (n : ℕ) : BoundaryLocalization (c n) α β (R n) H (t n) := Classical.choice
    (exists_boundaryLocalization hBc hB0 (c n) (ha n) α β (R n) H (t n) (hR0 n)
      (by simpa only [Complex.ofReal_re] using hax n) hH0)
  let E (n : ℕ) : Set Ω := {ω | H ≤ boundaryDensity κ α β ((c n).Q ((l n).τ ω) ω) (B ((l n).τ ω) ω)}
  have hprob (n : ℕ) : P (E n) ≤ ENNReal.ofReal (boundaryDensity κ α β (x:ℂ) 0/H) :=
    (l n).density_crossing_probability hB hBm hBc hκ (ha n) hβ (hR n) hH
  have hsub : {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (B T ω)} ⊆
      {ω | ∀ᶠ n : ℕ in atTop, ω ∈ E n} := by
    rintro ω ⟨S,Q,hQ,hhit⟩
    obtain ⟨g,hg,hgap⟩ := hQ.positive_lower_bound ((hBc ω).const_mul _)
    have hnc : ContinuousOn (fun u : ℝ => ‖(Q u,B u.toNNReal ω)‖) (Icc 0 (S:ℝ)) :=
      (hQ.continuousOn.prodMk (((hBc ω).comp continuous_real_toNNReal).continuousOn)).norm
    obtain ⟨s,hs,hmax⟩ := (isCompact_Icc : IsCompact (Icc 0 (S:ℝ))).exists_isMaxOn
      ⟨0,le_rfl,S.coe_nonneg⟩ hnc
    let M := ‖(Q s,B s.toNNReal ω)‖
    obtain ⟨N,hN⟩ := exists_nat_gt (max (max (S:ℝ) M) (x/(2*g)))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N:ℝ) ≤ n := Nat.cast_le.mpr hn
    have hNS : (S:ℝ) < (n:ℝ)+1 := by have := (le_max_left (S:ℝ) M).trans (le_max_left (max (S:ℝ) M) (x/(2*g))); linarith
    have hNM : M < (n:ℝ)+1 := by have := (le_max_right (S:ℝ) M).trans (le_max_left (max (S:ℝ) M) (x/(2*g))); linarith
    have hNg : x/(2*g) < (n:ℝ)+1 := by have := le_max_right (max (S:ℝ) M) (x/(2*g)); linarith
    have hann : 3*a n < g := by
      have hn0 : 0 < (n:ℝ)+1 := by positivity
      have hh : x < ((n:ℝ)+1)*(2*g) := (div_lt_iff₀ (by positivity)).mp hNg
      rw [show 3*a n = (x/2)/((n:ℝ)+1) by dsimp only [a]; ring]
      apply (div_lt_iff₀ hn0).mpr
      nlinarith
    apply (l n).true_crossing_forces_density_boundary (ha n) ω S
      (NNReal.coe_lt_coe.mp hNS) Q hQ
    · intro u hu
      exact hann.trans_le (hgap u hu)
    · intro u hu
      have hm := hmax ⟨u.coe_nonneg,NNReal.coe_le_coe.mpr hu⟩
      change ‖(Q (u:ℝ),B (u:ℝ).toNNReal ω)‖ ≤ M at hm
      rw [Real.toNNReal_coe] at hm
      have hnorm : 0 ≤ ‖((x:ℂ),(0:ℝ))‖ := norm_nonneg _
      change ‖(Q (u:ℝ),B u ω)‖ < ‖((x:ℂ),(0:ℝ))‖+(n:ℝ)+1
      change ‖(Q (u:ℝ),B u ω)‖ ≤ M at hm
      linarith
    · exact hhit
  exact (measure_mono hsub).trans (measure_eventually_sets_le P E _ hprob)

 

theorem boundary_maximal_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ α β x H : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hH : 0 < H)
    (hβ : -α-2+κ*(β+1)/2=0)
    (hH0 : boundaryDensity κ α β (x:ℂ) 0 ≤ H) :
    P {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (B T ω)} ≤
      ENNReal.ofReal (boundaryDensity κ α β (x:ℂ) 0 / H) := by
  obtain ⟨C,hCm,hCc,hC0,hC,hCB⟩ := exists_regular_brownian_version hB
  apply (measure_mono_ae (show {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (B T ω)} ≤ᵐ[P]
      {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ),
      IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*C t ω) x T Q ∧
      H ≤ boundaryDensity κ α β (Q T) (C T ω)} from ?_)).trans
      (boundary_maximal_density_regular hC hCm hCc hC0 κ α β x H hκ hx hH hβ hH0)
  filter_upwards [hCB] with ω he
  rintro ⟨T,Q,hQ,hF⟩
  refine ⟨T,Q,?_,?_⟩
  · simpa only [he] using hQ
  · simpa only [he] using hF

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

theorem IsCapacityTwoWitness.forward_flow_survives
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (Q : ℝ → ℂ)
    (hpos : ∀ t ∈ Icc 0 (T:ℝ), 0 < (Q t).im)
    (hd : ∀ t ∈ Icc 0 (T:ℝ), HasDerivWithinAt Q
      (2 / (Q t - (U t.toNNReal : ℂ))) (Icc 0 (T:ℝ)) t) :
    Q 0 ∈ survivingDomain γ T ∧ G T (Q 0) = Q T := by
  have hc : ContinuousOn (fun t => (Q t).im) (Icc 0 (T:ℝ)) :=
    Complex.continuous_im.comp_continuousOn (fun t ht => (hd t ht).continuousWithinAt)
  obtain ⟨t₀,ht₀,hmin⟩ := (isCompact_Icc : IsCompact (Icc 0 (T:ℝ))).exists_isMinOn
    ⟨0,le_rfl,T.coe_nonneg⟩ hc
  let a := (Q t₀).im
  have ha : 0 < a := hpos t₀ ht₀
  have hbound (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : a ≤ (Q t).im := hmin ht
  have hmap : MapsTo (fun t : ℝ => (T:ℝ)-t) (Icc 0 (T:ℝ)) (Icc 0 (T:ℝ)) := by
    intro t ht; constructor <;> linarith [ht.1,ht.2]
  have hrev (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) :
      HasDerivWithinAt (fun s : ℝ => Q ((T:ℝ)-s))
        (reverseField a (U ((T:ℝ)-t).toNNReal) (Q ((T:ℝ)-t))) (Icc 0 (T:ℝ)) t := by
    have he := (hd _ (hmap ht)).scomp t
      ((hasDerivAt_id t).const_sub (T:ℝ)).hasDerivWithinAt hmap
    simpa only [Function.comp_def,neg_smul,one_smul,reverseField,
      reverseCenter_eq (hbound _ (hmap ht)),div_eq_mul_inv,neg_mul] using he
  have he := h.reverse_flow_identifies T (Q T) ha
    (hbound T ⟨T.coe_nonneg,le_rfl⟩) (fun s => Q ((T:ℝ)-s))
    (by simp only [sub_zero]) hrev
  simp only [sub_self] at he
  have hlive : F T (Q T) ∈ survivingDomain γ T :=
    h.2.2.2.2.2.2.1 T (hpos T ⟨T.coe_nonneg,le_rfl⟩)
  rw [← he] at hlive
  refine ⟨hlive,?_⟩
  rw [he]
  exact h.2.2.2.2.2.2.2.2.1 T (Q T) (hpos T ⟨T.coe_nonneg,le_rfl⟩)

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

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma reciprocal_real_near_one {z : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2) (hz : ‖z‖ ≤ δ) :
    1 - 2*δ ≤ ((1+z)⁻¹).re := by
  have hl : 1-δ ≤ ‖1+z‖ := by
    have hh := norm_sub_le (1+z) z
    simp only [add_sub_cancel_right, norm_one] at hh
    linarith
  have hn : 0 < ‖1+z‖ := by linarith
  have hne : 1+z ≠ 0 := norm_pos_iff.mp hn
  have he : (1+z)⁻¹ - 1 = -z/(1+z) := by field_simp; ring
  have hb : ‖(1+z)⁻¹ - 1‖ ≤ 2*δ := by
    rw [he,norm_div,norm_neg]
    apply (div_le_iff₀ hn).mpr
    nlinarith
  have hr := Complex.abs_re_le_norm ((1+z)⁻¹-1)
  simp only [sub_re,one_re] at hr
  have := (abs_le.mp (hr.trans hb)).1
  linarith

lemma boundary_difference_coefficient {X δ : ℝ} {D : ℂ}
    (hX : 0 < X) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2) (hD : ‖D‖ ≤ δ*X) :
    (-2 / ((X:ℂ)*((X:ℂ)+D))).re ≤ (-2+4*δ)*X⁻¹^2 := by
  have hx : (X:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hz : ‖D/(X:ℂ)‖ ≤ δ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
    exact (div_le_iff₀ hX).mpr hD
  have hh := reciprocal_real_near_one hδ hδ2 hz
  have he : (-2 / ((X:ℂ)*((X:ℂ)+D))) =
      ((-2*X⁻¹^2:ℝ):ℂ)*(1+D/(X:ℂ))⁻¹ := by
    push_cast
    field_simp
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  nlinarith [sq_nonneg X⁻¹]

 

theorem near_real_difference_bound
    (T : ℝ) (hT : 0 ≤ T) (U Q : ℝ → ℝ) (Z : ℝ → ℂ)
    (hU : ContinuousOn U (Icc 0 T)) (hQ : ContinuousOn Q (Icc 0 T))
    (hZ : ContinuousOn Z (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 < Q t-U t)
    (hQd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q (2/(Q t-U t)) (Icc 0 T) t)
    (hZd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z (2/(Z t-(U t:ℂ))) (Icc 0 T) t)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2)
    (hratio : ∀ t ∈ Icc 0 T, ‖Z t-(Q t:ℂ)‖ ≤ δ*(Q t-U t)) :
    ‖Z T-(Q T:ℂ)‖ ≤ ‖Z 0-(Q 0:ℂ)‖ *
      Real.exp ((-2+4*δ)*(∫ t in (0:ℝ)..T, (Q t-U t)⁻¹^2)) := by
  let X (t : ℝ) := Q t-U t
  let D (t : ℝ) := Z t-(Q t:ℂ)
  have hXc : ContinuousOn X (Icc 0 T) := hQ.sub hU
  have hDc : ContinuousOn D (Icc 0 T) := hZ.sub (Complex.continuous_ofReal.comp_continuousOn hQ)
  have hne (t : ℝ) (ht : t ∈ Icc 0 T) : (X t:ℂ)+D t ≠ 0 := by
    have hl : X t-‖D t‖ ≤ ‖(X t:ℂ)+D t‖ := by
      have hh := norm_sub_le ((X t:ℂ)+D t) (D t)
      simp only [add_sub_cancel_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0 < X t from hpos t ht)] at hh
      linarith
    apply norm_pos_iff.mp
    have hpp := hpos t ht
    have hrr := hratio t ht
    change ‖D t‖ ≤ δ*X t at hrr
    change 0 < X t at hpp
    nlinarith
  let c (t : ℝ) := -2 / ((X t:ℂ)*((X t:ℂ)+D t))
  have hcc : ContinuousOn c (Icc 0 T) := by
    apply continuousOn_const.div
      ((Complex.continuous_ofReal.comp_continuousOn hXc).mul
        ((Complex.continuous_ofReal.comp_continuousOn hXc).add hDc))
    intro t ht
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (hpos t ht).ne') (hne t ht)
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt D (c t*D t) (Icc 0 T) t := by
    have hh := (hZd t ht).sub (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t (hQd t ht))
    have halg : c t*D t = 2/(Z t-(U t:ℂ)) - ((2/(Q t-U t):ℝ):ℂ) := by
      dsimp only [c,D,X]
      have hxn := Complex.ofReal_ne_zero.mpr (hpos t ht).ne'
      have hzn : Z t-(U t:ℂ) ≠ 0 := by
        convert hne t ht using 1
        all_goals try with_reducible_and_instances rfl
        simp only [X,D,Complex.ofReal_sub]
        ring
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_sub]
      rw [show (Q t:ℂ)-(U t:ℂ)+(Z t-(Q t:ℂ))=Z t-(U t:ℂ) by ring]
      have hx' : (Q t:ℂ)-(U t:ℂ) ≠ 0 := by simpa only [Complex.ofReal_sub] using hxn
      field_simp [hx',hzn]
      ring
    convert hh using 1 <;> try rfl
    exact halg
  have he := complex_linear_ode_exp T hT D c hcc hd
  have hci : IntervalIntegrable (fun t => (c t).re) volume 0 T :=
    (Complex.continuous_re.comp_continuousOn hcc).intervalIntegrable_of_Icc hT
  have hxi : IntervalIntegrable (fun t => (-2+4*δ)*(X t)⁻¹^2) volume 0 T := by
    exact (continuousOn_const.mul ((hXc.inv₀ (fun t ht => (hpos t ht).ne')).pow 2)).intervalIntegrable_of_Icc hT
  have hi : (∫ t in (0:ℝ)..T, (c t).re) ≤
      (-2+4*δ)*(∫ t in (0:ℝ)..T, (X t)⁻¹^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT hci hxi
    intro t ht
    exact boundary_difference_coefficient (hpos t ht) hδ hδ2 (hratio t ht)
  change ‖D T‖ ≤ _
  have hir : (∫ t in (0:ℝ)..T, (c t).re) = (∫ t in (0:ℝ)..T, c t).re :=
    Complex.reCLM.intervalIntegral_comp_comm (hcc.intervalIntegrable_of_Icc hT)
  rw [he,norm_mul,Complex.norm_exp,← hir]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hi) (norm_nonneg _)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma BoundaryComparisonFailure.density_crossing
    {U : ℝ≥0 → ℝ} {x r δ β κ : ℝ}
    (hU : Continuous U) (hr : 0 < r) (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) (hβ : 0 < β)
    (hfail : BoundaryComparisonFailure U x r δ)
    (B : ℝ≥0 → ℝ) (heU : ∀ t, U t = Real.sqrt κ*B t) :
    ∃ (T : ℝ≥0) (Q : ℝ → ℂ), IsPositiveBoundaryClockPath U x T Q ∧
      Real.exp (β*Real.log (δ/r)) ≤ boundaryDensity κ (2-4*δ) β (Q T) (B T) := by
  obtain ⟨T,Q,Z,hQ,hZd,hZ0,hratio,hend⟩ := hfail
  have hQd (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : HasDerivWithinAt (fun u => (Q u).re)
      (2/((Q t).re-U t.toNNReal)) (Icc 0 (T:ℝ)) t := by
    simpa only [Function.comp_def,Complex.reCLM_apply,Complex.add_re,Complex.ofReal_re,
      Complex.mul_re,Complex.I_re,mul_zero,Complex.ofReal_im,Complex.I_im,mul_one,
      sub_zero,add_zero] using Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hQ.2.2 t ht)
  have hn := near_real_difference_bound (T:ℝ) T.coe_nonneg
    (fun t => U t.toNNReal) (fun t => (Q t).re) Z
    (hU.comp continuous_real_toNNReal).continuousOn
    (Complex.continuous_re.comp_continuousOn hQ.continuousOn)
    (fun t ht => (hZd t ht).continuousWithinAt) hQ.2.1 hQd hZd δ hδ.le hδ2 hratio
  have hc := hQ.clock_identity hU
  have hq0 : ((Q 0).re:ℂ) = (x:ℂ) := by rw [hQ.1,Complex.ofReal_re]
  rw [hq0,← hc] at hn
  have hD : δ*((Q T).re-U T) ≤ r*Real.exp (-(2-4*δ)*(Q T).im) := by
    have hh := hn.trans (mul_le_mul_of_nonneg_right hZ0 (Real.exp_pos _).le)
    rw [show -2+4*δ = -(2-4*δ) by ring] at hh
    exact hend.trans hh
  have hX : 0 < (Q T).re-U T := by simpa only [Real.toNNReal_coe] using hQ.2.1 T ⟨T.coe_nonneg,le_rfl⟩
  have hquot : δ/r ≤ Real.exp (-(2-4*δ)*(Q T).im)/((Q T).re-U T) :=
    (div_le_div_iff₀ hr hX).mpr (by nlinarith [hD])
  have hlog := Real.log_le_log (div_pos hδ hr) hquot
  rw [Real.log_div (Real.exp_pos _).ne' hX.ne',Real.log_exp] at hlog
  refine ⟨T,Q,hQ,?_⟩
  unfold boundaryDensity
  rw [← heU T]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hlog hβ.le]

lemma boundary_density_threshold_initial {κ α β x r δ : ℝ}
    (hx : 0 < x) (hr : 0 < r) (_hδ : 0 < δ) (hβ : 0 ≤ β) (hrx : r ≤ δ*x) :
    boundaryDensity κ α β (x:ℂ) 0 ≤ Real.exp (β*Real.log (δ/r)) := by
  have hq : x⁻¹ ≤ δ/r := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hx hr).mpr
    simpa only [one_mul] using hrx
  have hl := Real.log_le_log (inv_pos.mpr hx) hq
  rw [Real.log_inv] at hl
  simp only [boundaryDensity,Complex.ofReal_im,mul_zero,zero_sub,Complex.ofReal_re,sub_zero]
  exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hl hβ])

lemma boundary_density_threshold_quotient {κ α β x r δ : ℝ}
    (hx : 0 < x) (hr : 0 < r) (hδ : 0 < δ) :
    boundaryDensity κ α β (x:ℂ) 0 / Real.exp (β*Real.log (δ/r)) =
      (r/(δ*x))^β := by
  simp only [boundaryDensity,Complex.ofReal_im,mul_zero,zero_sub,Complex.ofReal_re,sub_zero]
  rw [← Real.exp_sub,Real.rpow_def_of_pos (div_pos hr (mul_pos hδ hx)),
    Real.log_div hr.ne' (mul_pos hδ hx).ne',Real.log_mul hδ.ne' hx.ne',
    Real.log_div hδ.ne' hr.ne']
  congr 1
  ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 
lemma near_real_first_contact {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 T)) (h0 : f 0 < 0) (hTval : 0 ≤ f T) :
    ∃ s ∈ Icc 0 T, f s = 0 ∧ ∀ t ∈ Icc 0 s, f t ≤ 0 := by
  let F (t : ℝ) := f (projIcc 0 T hT t)
  have hFc : Continuous F := hc.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc 0 T hT t).property)
  have hFe (t : ℝ) (ht : t ∈ Icc 0 T) : F t = f t := by
    simp only [F,projIcc_of_mem hT ht]
  obtain ⟨u,hu,hfu⟩ := intermediate_value_Icc hT hc ⟨h0.le,hTval⟩
  let A := Icc 0 T ∩ F ⁻¹' {0}
  have hAc : IsCompact A := isCompact_Icc.inter_right (isClosed_singleton.preimage hFc)
  have hAn : A.Nonempty := ⟨u,hu,by simpa only [mem_preimage,mem_singleton_iff,hFe u hu] using hfu⟩
  obtain ⟨s,hs,hmin⟩ := hAc.exists_isMinOn hAn continuousOn_id
  have hfs : f s = 0 := (hFe s hs.1).symm.trans hs.2
  refine ⟨s,hs.1,hfs,?_⟩
  intro t ht
  by_contra hn
  have htp : 0 < f t := lt_of_not_ge hn
  have hsub : Icc 0 t ⊆ Icc 0 T := fun v hv => ⟨hv.1,hv.2.trans (ht.2.trans hs.1.2)⟩
  obtain ⟨v,hv,hfv⟩ := intermediate_value_Icc ht.1 (hc.mono hsub) ⟨h0.le,htp.le⟩
  have hvA : v ∈ A := ⟨hsub hv,by simpa only [mem_preimage,mem_singleton_iff,hFe v (hsub hv)] using hfv⟩
  have hst : s ≤ t := (hmin hvA).trans hv.2
  have hts : t = s := le_antisymm ht.2 hst
  exact htp.ne' (hts ▸ hfs)

lemma rightField_im (a u : ℝ) (z : ℂ) :
    (rightField a u z).im = (-2 / Complex.normSq (rightCenter a u z))*z.im := by
  simp only [rightField,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,add_zero,Complex.inv_im]
  have him : (rightCenter a u z).im = z.im := by simp [rightCenter]
  rw [him]
  ring

 

lemma right_flow_im_pos {U : ℝ → ℝ} (hU : Continuous U) {a : ℝ} (ha : 0 < a)
    {Z : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z
      (rightField a (U t) (Z t)) (Icc 0 T) t)
    (h0 : 0 < (Z 0).im) : 0 < (Z T).im := by
  have hZc : ContinuousOn Z (Icc 0 T) := fun t ht => (hd t ht).continuousWithinAt
  let c (t : ℝ) := -2 / Complex.normSq (rightCenter a (U t) (Z t))
  have hcenter : ContinuousOn (fun t => rightCenter a (U t) (Z t)) (Icc 0 T) := by
    unfold rightCenter
    fun_prop
  have hcc : ContinuousOn c (Icc 0 T) :=
    continuousOn_const.div (Complex.continuous_normSq.comp_continuousOn hcenter)
      (fun t ht => (Complex.normSq_pos.mpr (rightCenter_ne_zero ha _ _)).ne')
  have hfd (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt
      (fun s => ((Z s).im:ℂ)) ((c t:ℂ)*((Z t).im:ℂ)) (Icc 0 T) t := by
    have hh := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt t
      (Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t (hd t ht))
    simpa only [Function.comp_def,Complex.ofRealCLM_apply,Complex.imCLM_apply,
      rightField_im,Complex.ofReal_mul,c] using hh
  have he := complex_linear_ode_exp T hT (fun t => ((Z t).im:ℂ)) (fun t => (c t:ℂ))
    (Complex.continuous_ofReal.comp_continuousOn hcc) hfd
  have hint : (∫ t in (0:ℝ)..T, (c t:ℂ)) = ((∫ t in (0:ℝ)..T, c t : ℝ):ℂ) := by
    exact Complex.ofRealCLM.intervalIntegral_comp_comm (hcc.intervalIntegrable_of_Icc hT)
  rw [hint,← Complex.ofReal_exp,← Complex.ofReal_mul] at he
  have heR : (Z T).im = (Z 0).im * Real.exp (∫ t in (0:ℝ)..T, c t) := Complex.ofReal_injective he
  rw [heR]
  exact mul_pos h0 (Real.exp_pos _)

lemma right_flow_unclipped_of_ratio {a δ X u q : ℝ} {z : ℂ}
    (haX : a ≤ X) (hX : 0 ≤ X) (hδ : δ ≤ 1/2)
    (hXeq : X = q-u) (hratio : ‖z-(q:ℂ)‖ ≤ δ*X) :
    a/2 ≤ z.re-u := by
  have hn : q-z.re ≤ ‖z-(q:ℂ)‖ := by
    have hh := Complex.re_le_norm (-(z-(q:ℂ)))
    simpa only [Complex.neg_re,Complex.sub_re,Complex.ofReal_re,neg_sub,norm_neg,norm_sub_rev] using hh
  have hmul := mul_le_mul_of_nonneg_right hδ hX
  nlinarith

 

lemma no_boundary_failure_gives_complex_flow
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {x r δ : ℝ} (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ)
    {T : ℝ≥0} {Q : ℝ → ℂ} (hQ : IsPositiveBoundaryClockPath U x T Q)
    (w : ℂ) (hw : ‖w-(x:ℂ)‖ ≤ r) :
    ∃ Z : ℝ → ℂ, Z 0 = w ∧
      (∀ t ∈ Icc 0 (T:ℝ), HasDerivWithinAt Z
        (2/(Z t-(U t.toNNReal:ℂ))) (Icc 0 (T:ℝ)) t) ∧
      (∀ t ∈ Icc 0 (T:ℝ), ‖Z t-((Q t).re:ℂ)‖ < δ*((Q t).re-U t.toNNReal)) := by
  obtain ⟨a,ha,hgap⟩ := hQ.positive_lower_bound hU
  have hUc : Continuous (fun t : ℝ => U t.toNNReal) := hU.comp continuous_real_toNNReal
  obtain ⟨Y,hYm,hY0,hYd⟩ := exists_measurable_right_flow
    (fun t (_ : Unit) => U t.toNNReal)
    (hUc.measurable.comp measurable_fst) (fun _ => hUc)
    (fun _ => w) measurable_const (half_pos ha)
  let Z (t : ℝ) := Y t ()
  have hZ0 : Z 0 = w := hY0 ()
  have hZd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt Z
      (rightField (a/2) (U t.toNNReal) (Z t)) (Ici 0) t := hYd () t ht
  have hZc : ContinuousOn Z (Icc 0 (T:ℝ)) :=
    fun t ht => ((hZd t ht.1).mono (fun s hs => hs.1)).continuousWithinAt
  let f (t : ℝ) := ‖Z t-((Q t).re:ℂ)‖-δ*((Q t).re-U t.toNNReal)
  have hfc : ContinuousOn f (Icc 0 (T:ℝ)) := by
    exact (hZc.sub (Complex.continuous_ofReal.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn hQ.continuousOn))).norm.sub
      (continuousOn_const.mul ((Complex.continuous_re.comp_continuousOn hQ.continuousOn).sub hUc.continuousOn))
  have hf0 : f 0 < 0 := by
    dsimp only [f]
    rw [hZ0,hQ.1,Complex.ofReal_re,Real.toNNReal_zero,hU0,sub_zero]
    linarith
  have hratio (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : f t < 0 := by
    by_contra hn
    have hsub : Icc 0 t ⊆ Icc 0 (T:ℝ) := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
    obtain ⟨s,hs,hfs,hbefore⟩ := near_real_first_contact ht.1 (hfc.mono hsub) hf0 (le_of_not_gt hn)
    let S : ℝ≥0 := ⟨s,hs.1⟩
    have hsubS : Icc 0 (S:ℝ) ⊆ Icc 0 (T:ℝ) := fun v hv => ⟨hv.1,hv.2.trans (hs.2.trans ht.2)⟩
    have hcomp (v : ℝ) (hv : v ∈ Icc 0 (S:ℝ)) :
        ‖Z v-((Q v).re:ℂ)‖ ≤ δ*((Q v).re-U v.toNNReal) := sub_nonpos.mp (hbefore v hv)
    have hreal (v : ℝ) (hv : v ∈ Icc 0 (S:ℝ)) : a/2 ≤ (Z v).re-U v.toNNReal :=
      right_flow_unclipped_of_ratio (hgap v (hsubS hv)) (hQ.2.1 v (hsubS hv)).le hδ2 rfl (hcomp v hv)
    apply hno
    refine ⟨S,Q,Z,⟨hQ.1,fun v hv => hQ.2.1 v (hsubS hv),
      fun v hv => (hQ.2.2 v (hsubS hv)).mono hsubS⟩,?_,?_,hcomp,?_⟩
    · intro v hv
      rw [← rightField_eq (hreal v hv)]
      exact (hZd v hv.1).mono (fun u hu => hu.1)
    · simpa only [hZ0] using hw
    · have hh : ‖Z s-((Q s).re:ℂ)‖ = δ*((Q s).re-U s.toNNReal) := sub_eq_zero.mp hfs
      have hS : s.toNNReal = S := by
        apply NNReal.eq
        exact Real.coe_toNNReal s hs.1
      change δ*((Q s).re-U S) ≤ ‖Z s-((Q s).re:ℂ)‖
      rw [← hS]
      exact hh.ge
  have hreal (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : a/2 ≤ (Z t).re-U t.toNNReal :=
    right_flow_unclipped_of_ratio (hgap t ht) (hQ.2.1 t ht).le hδ2 rfl (sub_neg.mp (hratio t ht)).le
  refine ⟨Z,hZ0,?_,fun t ht => sub_neg.mp (hratio t ht)⟩
  intro t ht
  rw [← rightField_eq (hreal t ht)]
  exact (hZd t ht.1).mono (fun s hs => hs.1)

 

theorem IsCapacityTwoWitness.half_ball_survives_before_boundary_collision
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    {x r δ : ℝ} (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ)
    {T : ℝ≥0} {Q : ℝ → ℂ} (hQ : IsPositiveBoundaryClockPath U x T Q) :
    ∀ w : ℂ, 0 < w.im → ‖w-(x:ℂ)‖ ≤ r →
      w ∈ survivingDomain γ T ∧
      ‖G T w-((Q T).re:ℂ)‖ < δ*((Q T).re-U T) := by
  intro w hwp hw
  obtain ⟨Z,hZ0,hZd,hratio⟩ := no_boundary_failure_gives_complex_flow hU hU0 hrx hδ2 hno hQ w hw
  obtain ⟨a,ha,hgap⟩ := hQ.positive_lower_bound hU
  have hclip (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : a/2 ≤ (Z t).re-U t.toNNReal :=
    right_flow_unclipped_of_ratio (hgap t ht) (hQ.2.1 t ht).le hδ2 rfl (hratio t ht).le
  have hZp (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : 0 < (Z t).im := by
    have hsub : Icc 0 t ⊆ Icc 0 (T:ℝ) := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
    apply right_flow_im_pos (hU.comp continuous_real_toNNReal) (half_pos ha) ht.1
    · intro s hs
      dsimp only [Function.comp_def]
      rw [rightField_eq (hclip s (hsub hs))]
      exact (hZd s (hsub hs)).mono hsub
    · simpa only [hZ0] using hwp
  obtain ⟨hlive,he⟩ := h.forward_flow_survives T Z hZp hZd
  rw [hZ0] at hlive he
  refine ⟨hlive,?_⟩
  rw [he]
  simpa only [Real.toNNReal_coe] using hratio T ⟨T.coe_nonneg,le_rfl⟩

end SLEExactGauge
end


section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma ball_subset_upperHalfPlane {z : ℂ} {r : ℝ} (hr : r ≤ z.im) :
    ball z r ⊆ upperHalfPlane := by
  intro w hw
  have hh : ‖w - z‖ < r := mem_ball_iff_norm.mp hw
  have hi := Complex.abs_im_le_norm (w - z)
  simp only [Complex.sub_im] at hi
  change 0 < w.im
  have hx := neg_le_abs (w.im - z.im)
  linarith



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

open Set Filter MeasureTheory Complex Metric
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.boundary_path_of_half_ball_survivor
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    {x r δ : ℝ} (hx : 0 < x) (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ)
    (T : ℝ≥0) (w : ℂ) (hw : ‖w-(x:ℂ)‖ ≤ r)
    (hlive : w ∈ survivingDomain γ T) :
    ∃ Q : ℝ → ℂ, IsPositiveBoundaryClockPath U x T Q := by
  let a := min (x/2) (G T w).im
  have hy : 0 < (G T w).im := h.imag_positive T w hlive
  have ha : 0 < a := lt_min (half_pos hx) hy
  have hax : a < x := (min_le_left _ _).trans_lt (half_lt_self hx)
  have hay : a ≤ (G T w).im := min_le_right _ _
  obtain ⟨L,Y,hYm,hYl,hY0,hYd,hYa⟩ := boundary_clock_global_adapted_solution
    (fun t (_ : Unit) => U t) (hU.measurable.comp measurable_fst) (fun _ => hU)
    1 a ha (x:ℂ)
  let Q (t : ℝ) := Y t ()
  have hQ0 : Q 0 = (x:ℂ) := hY0 ()
  have hQd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt Q
      (boundaryClockField a (U t.toNNReal) (Q t)) (Ici 0) t := by
    simpa only [Real.sqrt_one,one_mul] using hYd () t ht
  have hQc : Continuous Q := (hYl ()).continuous
  let f (t : ℝ) := a-((Q t).re-U t.toNNReal)
  have hfc : Continuous f := continuous_const.sub
    ((Complex.continuous_re.comp hQc).sub (hU.comp continuous_real_toNNReal))
  have hf0 : f 0 < 0 := by
    dsimp only [f]
    rw [hQ0,Complex.ofReal_re,Real.toNNReal_zero,hU0,sub_zero]
    exact sub_neg.mpr hax
  have hgap (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : a < (Q t).re-U t.toNNReal := by
    by_contra hn
    obtain ⟨s,hs,hfs,hbefore⟩ := near_real_first_contact ht.1 hfc.continuousOn hf0
      (sub_nonneg.mpr (le_of_not_gt hn))
    let S : ℝ≥0 := ⟨s,hs.1⟩
    have hS : s.toNNReal = S := by apply NNReal.eq; exact Real.coe_toNNReal s hs.1
    have hST : S ≤ T := hs.2.trans ht.2
    have hgapS (v : ℝ) (hv : v ∈ Icc 0 (S:ℝ)) : a ≤ (Q v).re-U v.toNNReal :=
      sub_nonpos.mp (hbefore v hv)
    have hpath : IsPositiveBoundaryClockPath U x S Q := by
      refine ⟨hQ0,fun v hv => ha.trans_le (hgapS v hv),?_⟩
      intro v hv
      simpa only [boundaryClockField,positiveBoundaryField_eq (hgapS v hv),max_eq_right (hgapS v hv)] using
        (hQd v hv.1).mono (show Icc (0:ℝ) (S:ℝ) ⊆ Ici 0 from fun u hu => hu.1)
    have hratio := (h.half_ball_survives_before_boundary_collision hU hU0 hrx hδ2 hno hpath
      w hlive.1.1 hw).2
    have hgapEq : (Q S).re-U S = a := by
      change (Q s).re-U S = a
      rw [← hS]
      exact (sub_eq_zero.mp hfs).symm
    rw [hgapEq] at hratio
    have him : (G S w).im ≤ ‖G S w-((Q S).re:ℂ)‖ := by
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using
        Complex.im_le_norm (G S w-((Q S).re:ℂ))
    have hmono : (G T w).im ≤ (G S w).im := by
      have hh := h.imag_antitoneOn T w hlive ⟨S.coe_nonneg,hST⟩ ⟨T.coe_nonneg,le_rfl⟩ hST
      simpa only [Real.toNNReal_coe] using hh
    have hδa : δ*a ≤ a/2 := by nlinarith [mul_le_mul_of_nonneg_right hδ2 ha.le]
    linarith
  refine ⟨Q,hQ0,fun t ht => ha.trans (hgap t ht),?_⟩
  intro t ht
  simpa only [boundaryClockField,positiveBoundaryField_eq (hgap t ht).le,max_eq_right (hgap t ht).le] using
    (hQd t ht.1).mono (show Icc (0:ℝ) (T:ℝ) ⊆ Ici 0 from fun s hs => hs.1)

lemma IsCapacityTwoWitness.tip_avoids_half_ball_of_boundary_path
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    {x r δ : ℝ} (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ)
    {T : ℝ≥0} {Q : ℝ → ℂ} (hQ : IsPositiveBoundaryClockPath U x T Q) :
    r ≤ ‖γ T-(x:ℂ)‖ := by
  by_contra hn
  have hnear : ∀ᶠ y : ℝ in 𝓝[>] 0,
      ‖F T ((U T:ℂ)+(y:ℂ)*I)-(x:ℂ)‖ < r := by
    apply (tendsto_order.1 ((h.2.2.2.2.2.2.2.2.2.2.2.2 T).sub tendsto_const_nhds).norm).2
    exact lt_of_not_ge hn
  obtain ⟨y,hynear,hy⟩ := (hnear.and (show ∀ᶠ y : ℝ in 𝓝[>] 0, 0 < y from self_mem_nhdsWithin)).exists
  have hupper : (U T:ℂ)+(y:ℂ)*I ∈ upperHalfPlane := by
    change 0 < ((U T:ℂ)+(y:ℂ)*I).im
    simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,mul_one,Complex.I_re,mul_zero,add_zero,zero_add] using hy
  have hlive := h.2.2.2.2.2.2.1 T hupper
  have hratio := (h.half_ball_survives_before_boundary_collision hU hU0 hrx hδ2 hno hQ
    _ hlive.1.1 hynear.le).2
  have hg := h.2.2.2.2.2.2.2.2.1 T _ hupper
  rw [hg] at hratio
  have hX : 0 < (Q T).re-U T := by
    simpa only [Real.toNNReal_coe] using hQ.2.1 T ⟨T.coe_nonneg,le_rfl⟩
  have hmargin := right_flow_unclipped_of_ratio (a := (Q T).re-U T) le_rfl hX.le hδ2 rfl hratio.le
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,mul_zero,
    Complex.ofReal_im,Complex.I_im,zero_mul,add_zero,sub_self] at hmargin
  linarith

 

theorem IsCapacityTwoWitness.all_time_real_center_avoidance
    {U : ℝ≥0 → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    {x r δ : ℝ} (hx : 0 < x) (hrx : r < δ*x) (hδ2 : δ ≤ 1/2)
    (hno : ¬ BoundaryComparisonFailure U x r δ) :
    ∀ T : ℝ≥0, r ≤ ‖γ T-(x:ℂ)‖ := by
  intro T
  by_contra hn
  have htip : γ T ∈ ball (x:ℂ) r := by
    rw [mem_ball,dist_eq_norm]
    exact lt_of_not_ge hn
  obtain ⟨w,hwb,hw⟩ := mem_closure_iff.mp (h.trace_mem_closure_surviving T T le_rfl)
    (ball (x:ℂ) r) isOpen_ball htip
  have hwn : ‖w-(x:ℂ)‖ ≤ r := (by simpa only [mem_ball,dist_eq_norm] using hwb : ‖w-(x:ℂ)‖ < r).le
  obtain ⟨Q,hQ⟩ := h.boundary_path_of_half_ball_survivor hU hU0 hx hrx hδ2 hno T w hwn hw
  exact hn (h.tip_avoids_half_ball_of_boundary_path hU hU0 hrx hδ2 hno hQ)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma boundary_comparison_failure_probability_regular
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ β x r δ : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hr : 0 < r)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) (hβ : 0 < β)
    (heq : -(2-4*δ)-2+κ*(β+1)/2=0) :
    P {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ≤
      ENNReal.ofReal ((r/(δ*x))^β) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  by_cases hrx : r ≤ δ*x
  · have hprob := boundary_maximal_density hB κ (2-4*δ) β x
      (Real.exp (β*Real.log (δ/r))) hκ hx (Real.exp_pos _) heq
        (boundary_density_threshold_initial hx hr hδ hβ.le hrx)
    rw [boundary_density_threshold_quotient hx hr hδ] at hprob
    apply (measure_mono (show {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ⊆
      {ω | ∃ (T : ℝ≥0) (Q : ℝ → ℂ), IsPositiveBoundaryClockPath (fun t => Real.sqrt κ*B t ω) x T Q ∧
        Real.exp (β*Real.log (δ/r)) ≤ boundaryDensity κ (2-4*δ) β (Q T) (B T ω)} from ?_)).trans hprob
    intro ω hω
    exact hω.density_crossing ((hBc ω).const_mul _) hr hδ hδ2 hβ (fun t => B t ω) (fun t => rfl)
  · have hq : 1 ≤ r/(δ*x) := (le_div_iff₀ (mul_pos hδ hx)).mpr (by linarith)
    have hp := Real.one_le_rpow hq hβ.le
    exact prob_le_one.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)

 

theorem boundary_comparison_failure_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ β x r δ : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hr : 0 < r)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1/2) (hβ : 0 < β)
    (heq : -(2-4*δ)-2+κ*(β+1)/2=0) :
    P {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ≤
      ENNReal.ofReal ((r/(δ*x))^β) := by
  obtain ⟨C,hCm,hCc,hC0,hC,hCB⟩ := exists_regular_brownian_version hB
  apply (measure_mono_ae (show {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ} ≤ᵐ[P]
      {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*C t ω) x r δ} from ?_)).trans
      (boundary_comparison_failure_probability_regular hC hCc κ β x r δ hκ hx hr hδ hδ2 hβ heq)
  filter_upwards [hCB] with ω he
  intro h
  change BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r δ at h
  show BoundaryComparisonFailure (fun t => Real.sqrt κ*C t ω) x r δ
  simpa only [he] using h

 
theorem boundary_comparison_failure_sle_exponent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ x r : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (hx : 0 < x) (hr : 0 < r) :
    P {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r ((8-κ)/32)} ≤
      ENNReal.ofReal ((r/(((8-κ)/32)*x))^(3*(8-κ)/(4*κ))) := by
  apply boundary_comparison_failure_probability hB κ _ x r _ hκ hx hr
  · positivity
  · linarith
  · positivity
  · field_simp
    ring

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

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem ordinary_positive_real_center_approach
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    P {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} ≤
      ENNReal.ofReal ((r/(((8-κ)/32)*x))^(3*(8-κ)/(4*κ))) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hδ : 0 < (8-κ)/32 := by positivity
  have hδ2 : (8-κ)/32 ≤ 1/2 := by linarith
  have hβ : 0 < 3*(8-κ)/(4*κ) := by positivity
  by_cases hrx : r < ((8-κ)/32)*x
  · apply (measure_mono_ae (show {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} ≤ᵐ[P]
      {ω | BoundaryComparisonFailure (fun t => Real.sqrt κ*B t ω) x r ((8-κ)/32)} from ?_)).trans
      (boundary_comparison_failure_sle_exponent hB κ x r hκ hκ8 hx hr)
    filter_upwards [hw,hB.cont,hB.eval_zero_ae_eq_zero] with ω hω hc h0
    rintro ⟨t,ht⟩
    by_contra hn
    have hh := hω.all_time_real_center_avoidance (hc.const_mul _) (by simp only [h0,mul_zero])
      hx hrx hδ2 hn t
    exact (not_lt_of_ge hh) (by simpa only [dist_eq_norm] using ht)
  · have hq : 1 ≤ r/(((8-κ)/32)*x) :=
      (le_div_iff₀ (mul_pos hδ hx)).mpr (by simpa only [one_mul] using le_of_not_gt hrx)
    have hh := ENNReal.ofReal_le_ofReal (Real.one_le_rpow hq hβ.le)
    rw [ENNReal.ofReal_one] at hh
    exact prob_le_one.trans hh

 

theorem sle_positive_real_center_approach
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    P {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} ≤
      ENNReal.ofReal ((r/(((8-κ)/32)*x))^(3*(8-κ)/(4*κ))) := by
  classical
  obtain ⟨B,hB,htrace⟩ := hSLE.2
  have hchoice (ω : Ω) : ∃ G F : ℝ≥0 → ℂ → ℂ,
      IsCapacityTwoTrace (fun t => Real.sqrt κ*B t ω) (γ ω) →
        IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) G F := by
    by_cases h : IsCapacityTwoTrace (fun t => Real.sqrt κ*B t ω) (γ ω)
    · obtain ⟨G,F,hw⟩ := h
      exact ⟨G,F,fun _ => hw⟩
    · exact ⟨fun _ _ => 0,fun _ _ => 0,fun hh => False.elim (h hh)⟩
  choose G F hw using hchoice
  exact ordinary_positive_real_center_approach hB κ hκ hκ8 γ G F
    (htrace.mono fun ω hω => hw ω hω) x r hx hr

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Complex ComplexConjugate
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsOrdinaryChordalSLE.mirror
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (h : IsOrdinaryChordalSLE κ γ P) :
    IsOrdinaryChordalSLE κ (fun ω => loewnerMirror ∘ γ ω) P := by
  obtain ⟨hm,B,hB,hw⟩ := h
  refine ⟨fun t => loewnerMirror.continuous.measurable.comp (hm t),-B,hB.neg,?_⟩
  filter_upwards [hw] with ω hω
  obtain ⟨G,F,hGF⟩ := hω
  refine ⟨fun t z => loewnerMirror (G t (loewnerMirror z)),
    fun t z => loewnerMirror (F t (loewnerMirror z)),?_⟩
  simpa only [Pi.neg_apply,mul_neg] using hGF.mirror

 
theorem sle_real_center_approach
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (x r : ℝ) (hx : x ≠ 0) (hr : 0 < r) :
    P {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} ≤
      ENNReal.ofReal ((r/(((8-κ)/32)*|x|))^(3*(8-κ)/(4*κ))) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hh := sle_positive_real_center_approach κ hκ hκ8
      (fun ω => loewnerMirror ∘ γ ω) hSLE.mirror (-x) r (neg_pos.mpr hx) hr
    have he : {ω | ∃ t : ℝ≥0, dist ((loewnerMirror ∘ γ ω) t) ((-x:ℝ):ℂ) < r} =
        {ω | ∃ t : ℝ≥0, dist (γ ω t) (x:ℂ) < r} := by
      ext ω
      have hrx : ((-x:ℝ):ℂ) = loewnerMirror (x:ℂ) := by simp
      simp only [Function.comp_apply,hrx,loewnerMirror_dist]
    rw [he] at hh
    simpa only [abs_of_neg hx] using hh
  · simpa only [abs_of_pos hx] using
      sle_positive_real_center_approach κ hκ hκ8 γ hSLE x r hx hr

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
-- module Solutions.OAIQ27_SLE.SLE_IntervalDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interval Density for chordal SLE. -/

section

section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge

lemma smoothingWidth_tendsto : Tendsto smoothingWidth atTop (𝓝 0) := by
  unfold smoothingWidth
  simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right _ (2 : ℝ) tendsto_natCast_atTop_atTop))

lemma intervalBump_radii (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    l/4 ≤ (intervalBump a l hl n).rIn ∧ (intervalBump a l hl n).rOut < l/2 := by
  dsimp [intervalBump]
  constructor
  · have h := smoothingWidth_le n
    nlinarith
  · have h := smoothingWidth_pos n
    nlinarith

lemma intervalDensity_smooth (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    ContDiff ℝ ∞ (intervalDensity a l hl n) :=
  (intervalBump a l hl n).contDiff_normed

lemma intervalDensity_nonneg (a l : ℝ) (hl : 0 < l) (n : ℕ) (x : ℝ) :
    0 ≤ intervalDensity a l hl n x :=
  (intervalBump a l hl n).nonneg_normed x

lemma intervalDensity_compact (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    HasCompactSupport (intervalDensity a l hl n) :=
  (intervalBump a l hl n).hasCompactSupport_normed

lemma intervalDensity_integrable (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    Integrable (intervalDensity a l hl n) :=
  (intervalBump a l hl n).integrable_normed

lemma intervalDensity_integral (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    ∫ x, intervalDensity a l hl n x = 1 :=
  (intervalBump a l hl n).integral_normed

lemma intervalDensity_support (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    tsupport (intervalDensity a l hl n) ⊆ Ioo a (a+l) := by
  rw [intervalDensity, (intervalBump a l hl n).tsupport_normed_eq]
  intro x hx
  rw [Real.closedBall_eq_Icc] at hx
  have ho := (intervalBump_radii a l hl n).2
  constructor <;> linarith [hx.1, hx.2]

lemma intervalDensity_bound (a l : ℝ) (hl : 0 < l) (n : ℕ) (x : ℝ) :
    intervalDensity a l hl n x ≤ 2/l := by
  have hh := (intervalBump a l hl n).normed_le_div_measure_closedBall_rIn volume x
  have hp := (intervalBump a l hl n).rIn_pos
  rw [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)] at hh
  apply hh.trans
  apply (div_le_div_iff₀ (by positivity) hl).2
  have ha := (intervalBump_radii a l hl n).1
  linarith

lemma intervalBump_integral_tendsto (a l : ℝ) (hl : 0 < l) :
    Tendsto (fun n => ∫ x, intervalBump a l hl n x) atTop (𝓝 l) := by
  have hlow (n : ℕ) : 2*(intervalBump a l hl n).rIn ≤
      ∫ x, intervalBump a l hl n x := by
    have hh := (intervalBump a l hl n).measure_closedBall_le_integral volume
    simpa [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal,
      (intervalBump a l hl n).rIn_pos.le] using hh
  have hupp (n : ℕ) : (∫ x, intervalBump a l hl n x) ≤
      2*(intervalBump a l hl n).rOut := by
    have hh := (intervalBump a l hl n).integral_le_measure_closedBall volume
    simpa [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal,
      (intervalBump a l hl n).rOut_pos.le] using hh
  have hlo : Tendsto (fun n => 2*(intervalBump a l hl n).rIn) atTop (𝓝 l) := by
    have hh := (smoothingWidth_tendsto.const_sub 1).const_mul (2*(l/2))
    simp only [sub_zero, mul_one, show 2*(l/2)=l by ring] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    dsimp [intervalBump]
    ring
  have hup : Tendsto (fun n => 2*(intervalBump a l hl n).rOut) atTop (𝓝 l) := by
    have hh := ((smoothingWidth_tendsto.div_const 2).const_sub 1).const_mul (2*(l/2))
    simp only [zero_div, sub_zero, mul_one, show 2*(l/2)=l by ring] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    dsimp [intervalBump]
    ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup hlow hupp

lemma intervalDensity_support_exact (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    tsupport (intervalDensity a l hl n) =
      Icc (a+l*smoothingWidth n/4) (a+l-l*smoothingWidth n/4) := by
  rw [intervalDensity, (intervalBump a l hl n).tsupport_normed_eq,
    Real.closedBall_eq_Icc]
  congr 1 <;> dsimp [intervalBump] <;> ring

lemma intervalDensity_tendsto (a l : ℝ) (hl : 0 < l) (x : ℝ) :
    Tendsto (fun n => intervalDensity a l hl n x) atTop
      (𝓝 ((Ioo a (a+l)).indicator (fun _ => 1/l) x)) := by
  by_cases hx : x ∈ Ioo a (a+l)
  · have hd : dist x (a+l/2) < l/2 := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hrin : Tendsto (fun n => (intervalBump a l hl n).rIn) atTop (𝓝 (l/2)) := by
      have hh := (smoothingWidth_tendsto.const_sub 1).const_mul (l/2)
      simpa [intervalBump] using hh
    have he : ∀ᶠ n in atTop, dist x (a+l/2) ≤ (intervalBump a l hl n).rIn := by
      filter_upwards [hrin.eventually (eventually_gt_nhds hd)] with n hn
      exact hn.le
    have hb : Tendsto (fun n => intervalBump a l hl n x) atTop (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      exact ((intervalBump a l hl n).one_of_mem_closedBall hn).symm
    rw [indicator_of_mem hx]
    exact hb.div (intervalBump_integral_tendsto a l hl) (ne_of_gt hl)
  · have hh (n : ℕ) : intervalDensity a l hl n x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (intervalDensity_support a l hl n h))
    simp only [indicator_of_notMem hx]
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hh n).symm)


lemma densityPrimitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (densityPrimitive a f) (f x) x := by
  apply intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a x)
  · exact hf.stronglyMeasurable.stronglyMeasurableAtFilter
  · exact hf.continuousAt

lemma densityPrimitive_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (densityPrimitive a f) := by
  rw [contDiff_infty_iff_deriv]
  have hd := densityPrimitive_hasDerivAt hf.continuous a
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  have he : deriv (densityPrimitive a f) = f := funext fun x => (hd x).deriv
  rw [he]
  exact hf

lemma densityPrimitive_support {f : ℝ → ℝ} {a c d : ℝ}
    (hac : a < c) (hs : Function.support f ⊆ Icc c d) (hzero : ∫ t, f t = 0) :
    tsupport (densityPrimitive a f) ⊆ Icc c d := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hh
  have hz : densityPrimitive a f x = 0 := by
    rcases not_and_or.mp hh with hc | hd
    · apply intervalIntegral.integral_zero_ae
      filter_upwards [] with t ht
      have ht' : t < c := lt_of_le_of_lt ht.2 (max_lt hac (lt_of_not_ge hc))
      by_contra h
      have := (hs h).1
      linarith
    · have hdx : d < x := lt_of_not_ge hd
      rw [densityPrimitive, intervalIntegral.integral_eq_integral_of_support_subset]
      · exact hzero
      · intro t ht
        have hh := hs ht
        exact ⟨hac.trans_le hh.1, hh.2.trans hdx.le⟩
  exact hx hz

lemma densityPrimitive_bound {f : ℝ → ℝ} (hf : Integrable f) (a x : ℝ) :
    |densityPrimitive a f x| ≤ ∫ t, |f t| := by
  calc
    _ ≤ ∫ t in Set.uIoc a x, |f t| := by
      simpa only [densityPrimitive, Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := f) (a := a) (b := x) (μ := volume))
    _ ≤ _ := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun t => abs_nonneg _) hf.abs

lemma intervalTransport_contDiff (a l : ℝ) (hl : 0 < l) (a' : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (intervalTransport a l hl a' n) :=
  densityPrimitive_contDiff ((intervalDensity_smooth ..).sub (intervalDensity_smooth ..)) a

lemma intervalTransport_hasDerivAt (a l : ℝ) (hl : 0 < l) (a' : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (intervalTransport a l hl a' n)
      (intervalDensity a' (l/2) (by linarith) n x - intervalDensity a l hl n x) x :=
  densityPrimitive_hasDerivAt
    ((intervalDensity_smooth ..).continuous.sub (intervalDensity_smooth ..).continuous) a x

lemma intervalTransport_support (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    tsupport (intervalTransport a l hl a' n) ⊆
      Icc (a+l*smoothingWidth n/8) (a+l-l*smoothingWidth n/8) := by
  have hp : 0 < l*smoothingWidth n := mul_pos hl (smoothingWidth_pos n)
  apply densityPrimitive_support (by linarith : a < a+l*smoothingWidth n/8)
  · intro x hx
    by_cases hc : intervalDensity a' (l/2) (by linarith) n x ≠ 0
    · have hh : x ∈ tsupport (intervalDensity a' (l/2) (by linarith) n) := subset_closure hc
      rw [intervalDensity_support_exact] at hh
      constructor <;> nlinarith [hh.1,hh.2]
    · simp only [not_not] at hc
      have hc' : intervalDensity a l hl n x ≠ 0 := by
        intro hz
        exact hx (by dsimp; rw [hc,hz]; ring)
      have hh : x ∈ tsupport (intervalDensity a l hl n) := subset_closure hc'
      rw [intervalDensity_support_exact] at hh
      constructor <;> nlinarith [hh.1,hh.2]
  · rw [integral_sub (intervalDensity_integrable ..) (intervalDensity_integrable ..),
      intervalDensity_integral, intervalDensity_integral, sub_self]

lemma intervalTransport_compact (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    HasCompactSupport (intervalTransport a l hl a' n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (intervalTransport_support a l hl a' ha ha' n)

lemma intervalTransport_support_interior (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    tsupport (intervalTransport a l hl a' n) ⊆ Ioo a (a+l) := by
  intro x hx
  have hh := intervalTransport_support a l hl a' ha ha' n hx
  have hp : 0 < l*smoothingWidth n := mul_pos hl (smoothingWidth_pos n)
  constructor <;> linarith [hh.1,hh.2]

lemma intervalTransport_bound (a l : ℝ) (hl : 0 < l) (a' : ℝ) (n : ℕ) (x : ℝ) :
    |intervalTransport a l hl a' n x| ≤ 2 := by
  have hc := intervalDensity_integrable a' (l/2) (by linarith) n
  have hp := intervalDensity_integrable a l hl n
  apply (densityPrimitive_bound (hc.sub hp) a x).trans
  calc
    _ ≤ ∫ t, intervalDensity a' (l/2) (by linarith) n t + intervalDensity a l hl n t := by
      apply integral_mono (hc.sub hp).abs (hc.add hp)
      intro t
      change |intervalDensity a' (l/2) _ n t - intervalDensity a l hl n t| ≤
        intervalDensity a' (l/2) _ n t + intervalDensity a l hl n t
      apply abs_le.mpr
      have hc := intervalDensity_nonneg a' (l/2) (by linarith) n t
      have hp := intervalDensity_nonneg a l hl n t
      constructor <;> linarith
    _ = 2 := by
      rw [integral_add hc hp, intervalDensity_integral, intervalDensity_integral]
      norm_num

lemma intervalTransport_integrable (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    Integrable (intervalTransport a l hl a' n) :=
  (intervalTransport_contDiff ..).continuous.integrable_of_hasCompactSupport (μ := volume)
    (intervalTransport_compact a l hl a' ha ha' n)

lemma intervalTransport_integral_abs_le (a l : ℝ) (hl : 0 < l) (a' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l) (n : ℕ) :
    ∫ x, |intervalTransport a l hl a' n x| ≤ 2*l := by
  have hs : ∀ x, x ∉ Icc a (a+l) → |intervalTransport a l hl a' n x| = 0 := by
    intro x hx
    have he : intervalTransport a l hl a' n x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      have hh' := intervalTransport_support_interior a l hl a' ha ha' n hh
      exact hx ⟨hh'.1.le,hh'.2.le⟩
    rw [he, abs_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs]
  calc
    _ ≤ ∫ x in Icc a (a+l), (2:ℝ) := by
      apply integral_mono_ae
        ((intervalTransport_integrable a l hl a' ha ha' n).abs.restrict)
        (integrable_const 2)
      exact Eventually.of_forall fun x => intervalTransport_bound a l hl a' n x
    _ = 2*l := by
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc, add_sub_cancel_left, ENNReal.toReal_ofReal hl.le, smul_eq_mul]
      ring

lemma complexTensor_contDiff {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (complexTensor f g) :=
  (hf.comp Complex.reCLM.contDiff).mul (hg.comp Complex.imCLM.contDiff)

lemma complexTensor_support (f g : ℝ → ℝ) :
    tsupport (complexTensor f g) ⊆
      Complex.equivRealProdCLM ⁻¹' (tsupport f ×ˢ tsupport g) := by
  apply closure_minimal _
    (((isClosed_tsupport f).prod (isClosed_tsupport g)).preimage
      Complex.equivRealProdCLM.continuous)
  intro z hz
  have hh : f z.re * g z.im ≠ 0 := hz
  exact ⟨subset_closure (mul_ne_zero_iff.mp hh).1,
    subset_closure (mul_ne_zero_iff.mp hh).2⟩

lemma complexTensor_compact {f g : ℝ → ℝ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (complexTensor f g) :=
  (Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr
    (hf.prod hg)).of_isClosed_subset (isClosed_tsupport _) (complexTensor_support f g)

lemma complexTensor_integral (f g : ℝ → ℝ) :
    (∫ z, complexTensor f g z) = (∫ x, f x) * (∫ y, g y) := by
  have he := Complex.volume_preserving_equiv_real_prod.integral_comp
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => f p.1 * g p.2)
  simp only [Complex.measurableEquivRealProd_apply] at he
  unfold complexTensor
  rw [he, Measure.volume_eq_prod]
  exact integral_prod_mul f g

lemma complexTensor_integral_abs (f g : ℝ → ℝ) :
    (∫ z, |complexTensor f g z|) = (∫ x, |f x|) * (∫ y, |g y|) := by
  simpa only [complexTensor, abs_mul] using
    complexTensor_integral (fun x => |f x|) (fun y => |g y|)

lemma complexTensor_deriv_re {f g : ℝ → ℝ} {f' g' : ℝ} {z : ℂ}
    (hf : HasDerivAt f f' z.re) (hg : HasDerivAt g g' z.im) :
    (fderiv ℝ (complexTensor f g) z) (1 : ℂ) = f' * g z.im := by
  have hh := (hf.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt).mul
    (hg.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt)
  change fderiv ℝ ((f ∘ Complex.re) * (g ∘ Complex.im)) z 1 = _
  rw [hh.fderiv]
  simp [mul_comm]

lemma complexTensor_deriv_im {f g : ℝ → ℝ} {f' g' : ℝ} {z : ℂ}
    (hf : HasDerivAt f f' z.re) (hg : HasDerivAt g g' z.im) :
    (fderiv ℝ (complexTensor f g) z) Complex.I = f z.re * g' := by
  have hh := (hf.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt).mul
    (hg.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt)
  change fderiv ℝ ((f ∘ Complex.re) * (g ∘ Complex.im)) z Complex.I = _
  rw [hh.fderiv]
  simp

lemma rectangleTransportX_contDiff (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (rectangleTransportX a b lx ly hx hy a' b' n) :=
  complexTensor_contDiff (intervalTransport_contDiff ..) (intervalDensity_smooth ..)

lemma rectangleTransportY_contDiff (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (rectangleTransportY a b lx ly hx hy a' b' n) :=
  complexTensor_contDiff (intervalDensity_smooth ..) (intervalTransport_contDiff ..)

lemma rectangleTransportX_compact (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (ha : a ≤ a') (ha' : a'+lx/2 ≤ a+lx) (n : ℕ) :
    HasCompactSupport (rectangleTransportX a b lx ly hx hy a' b' n) :=
  complexTensor_compact (intervalTransport_compact a lx hx a' ha ha' n)
    (intervalDensity_compact ..)

lemma rectangleTransportY_compact (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (hb : b ≤ b') (hb' : b'+ly/2 ≤ b+ly) (n : ℕ) :
    HasCompactSupport (rectangleTransportY a b lx ly hx hy a' b' n) :=
  complexTensor_compact (intervalDensity_compact ..)
    (intervalTransport_compact b ly hy b' hb hb' n)

lemma rectangleTransportX_support (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (ha : a ≤ a') (ha' : a'+lx/2 ≤ a+lx)
    (hb : b ≤ b') (hb' : b'+ly/2 ≤ b+ly) (n : ℕ) :
    tsupport (rectangleTransportX a b lx ly hx hy a' b' n) ⊆
      {z | a < z.re ∧ z.re < a+lx ∧ b < z.im ∧ z.im < b+ly} := by
  intro z hz
  have hh := complexTensor_support _ _ hz
  have hr := intervalTransport_support_interior a lx hx a' ha ha' n hh.1
  have hi := intervalDensity_support b' (ly/2) (by linarith) n hh.2
  exact ⟨hr.1, hr.2, hb.trans_lt hi.1, hi.2.trans_le hb'⟩

lemma rectangleTransportY_support (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (hb : b ≤ b') (hb' : b'+ly/2 ≤ b+ly) (n : ℕ) :
    tsupport (rectangleTransportY a b lx ly hx hy a' b' n) ⊆
      {z | a < z.re ∧ z.re < a+lx ∧ b < z.im ∧ z.im < b+ly} := by
  intro z hz
  have hh := complexTensor_support _ _ hz
  have hr := intervalDensity_support a lx hx n hh.1
  have hi := intervalTransport_support_interior b ly hy b' hb hb' n hh.2
  exact ⟨hr.1, hr.2, hi.1, hi.2⟩

lemma rectangleTransport_divergence (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) (z : ℂ) :
    (fderiv ℝ (rectangleTransportX a b lx ly hx hy a' b' n) z) 1 +
      (fderiv ℝ (rectangleTransportY a b lx ly hx hy a' b' n) z) Complex.I =
      rectangleDensity a' b' (lx/2) (ly/2) (by linarith) (by linarith) n z -
        rectangleDensity a b lx ly hx hy n z := by
  unfold rectangleTransportX rectangleTransportY
  rw [complexTensor_deriv_re (intervalTransport_hasDerivAt ..)
    (((intervalDensity_smooth ..).differentiable (by simp)) _).hasDerivAt]
  rw [complexTensor_deriv_im
    (((intervalDensity_smooth ..).differentiable (by simp)) _).hasDerivAt
    (intervalTransport_hasDerivAt ..)]
  dsimp [rectangleDensity, complexTensor]
  ring

lemma rectangleTransportX_bound (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) (z : ℂ) :
    |rectangleTransportX a b lx ly hx hy a' b' n z| ≤ 8/ly := by
  unfold rectangleTransportX complexTensor
  rw [abs_mul, abs_of_nonneg (intervalDensity_nonneg ..)]
  calc
    _ ≤ 2 * (2/(ly/2)) := mul_le_mul (intervalTransport_bound ..)
      (intervalDensity_bound ..) (intervalDensity_nonneg ..) (by norm_num)
    _ = _ := by field_simp; ring

lemma rectangleTransportY_bound (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (n : ℕ) (z : ℂ) :
    |rectangleTransportY a b lx ly hx hy a' b' n z| ≤ 4/lx := by
  unfold rectangleTransportY complexTensor
  rw [abs_mul, abs_of_nonneg (intervalDensity_nonneg ..)]
  calc
    _ ≤ (2/lx) * 2 := mul_le_mul (intervalDensity_bound ..)
      (intervalTransport_bound ..) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma intervalDensity_integral_abs (a l : ℝ) (hl : 0 < l) (n : ℕ) :
    (∫ x, |intervalDensity a l hl n x|) = 1 := by
  simp_rw [abs_of_nonneg (intervalDensity_nonneg a l hl n _)]
  exact intervalDensity_integral ..

lemma rectangleTransportX_integral_abs (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (ha : a ≤ a') (ha' : a'+lx/2 ≤ a+lx) (n : ℕ) :
    ∫ z, |rectangleTransportX a b lx ly hx hy a' b' n z| ≤ 2*lx := by
  rw [rectangleTransportX, complexTensor_integral_abs, intervalDensity_integral_abs, mul_one]
  exact intervalTransport_integral_abs_le a lx hx a' ha ha' n

lemma rectangleTransportY_integral_abs (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (a' b' : ℝ) (hb : b ≤ b') (hb' : b'+ly/2 ≤ b+ly) (n : ℕ) :
    ∫ z, |rectangleTransportY a b lx ly hx hy a' b' n z| ≤ 2*ly := by
  rw [rectangleTransportY, complexTensor_integral_abs, intervalDensity_integral_abs, one_mul]
  exact intervalTransport_integral_abs_le b ly hy b' hb hb' n

lemma scaleLength_le_one (j : ℕ) : scaleLength j ≤ 1 := by
  unfold scaleLength
  exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
lemma scaleLength_zero : scaleLength 0 = 1 := by simp [scaleLength]
lemma scaleLength_succ (j : ℕ) : scaleLength (j+1) = scaleLength j/2 := by
  simp [scaleLength, pow_succ, div_mul_eq_div_div]
lemma scaleOrigin_zero (t : ℝ) : scaleOrigin t 0 = 0 := by simp [scaleOrigin, scaleLength]
lemma scaleOrigin_nonneg {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : 0 ≤ scaleOrigin t j :=
  mul_nonneg ht (sub_nonneg.mpr (scaleLength_le_one j))
lemma scaleOrigin_add_le_one {t : ℝ} (ht : t ≤ 1) (j : ℕ) :
    scaleOrigin t j + scaleLength j ≤ 1 := by
  have hh := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr (scaleLength_le_one j))
  dsimp [scaleOrigin]
  linarith
lemma scaleOrigin_step {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    scaleOrigin t j ≤ scaleOrigin t (j+1) := by
  simp only [scaleOrigin, scaleLength_succ]
  have := mul_nonneg ht (scaleLength_pos j).le
  nlinarith
lemma scaleOrigin_right_step {t : ℝ} (ht : t ≤ 1) (j : ℕ) :
    scaleOrigin t (j+1) + scaleLength j/2 ≤ scaleOrigin t j + scaleLength j := by
  simp only [scaleOrigin, scaleLength_succ]
  have := mul_le_mul_of_nonneg_right ht (scaleLength_pos j).le
  nlinarith

lemma dyadic_position_param (k : ℕ) (hk : k ≠ 0) (i : Fin (2^k)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ scaleOrigin t k = (i:ℝ)/(2:ℝ)^k := by
  have hp : (1:ℝ) < 2^k := one_lt_pow₀ (by norm_num) hk
  have hi : (i:ℝ) + 1 ≤ (2:ℝ)^k := by
    exact_mod_cast i.isLt
  refine ⟨(i:ℝ)/((2:ℝ)^k-1), by positivity, ?_, ?_⟩
  · apply (div_le_one (by linarith)).2
    linarith
  · unfold scaleOrigin scaleLength
    have hp0 : (2:ℝ)^k ≠ 0 := by positivity
    have hp1 : (2:ℝ)^k-1 ≠ 0 := by linarith
    field_simp

lemma dyadic_sum (n : ℕ) : ∑ j ∈ Finset.range n, (2 : ℝ)^j = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

 

lemma dyadic_sum_square (a : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A) (n : ℕ)
    (ha : ∀ j < n, 0 ≤ a j ∧ a j ≤ A * 2^j) :
    (∑ j ∈ Finset.range n, a j)^2 ≤
      3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * a j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ha n (Nat.lt_succ_self n)
    have ha' : ∀ j < n, 0 ≤ a j ∧ a j ≤ A * 2^j :=
      fun j hj => ha j (Nat.lt_trans hj (Nat.lt_succ_self n))
    have hs0 : 0 ≤ ∑ j ∈ Finset.range n, a j :=
      Finset.sum_nonneg fun j hj => (ha' j (Finset.mem_range.mp hj)).1
    have hs : (∑ j ∈ Finset.range n, a j) ≤ A * (2^n - 1) := by
      calc
        _ ≤ ∑ j ∈ Finset.range n, A * 2^j :=
          Finset.sum_le_sum fun j hj => (ha' j (Finset.mem_range.mp hj)).2
        _ = _ := by rw [← Finset.mul_sum, dyadic_sum]
    have hcross := mul_le_mul_of_nonneg_right hs hn.1
    have hsquare := mul_le_mul_of_nonneg_right hn.2 hn.1
    have hnonneg : 0 ≤ A * a n := mul_nonneg hA hn.1
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hi := ih ha'
    nlinarith

 

theorem integral_sum_kernel_sq_le
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (K : ℕ → X → E) (A B : ℝ) (n : ℕ)
    (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hK : ∀ j < n, Integrable (K j) μ)
    (hbound : ∀ j < n, ∀ x, ‖K j x‖ ≤ A * 2^j)
    (h₁ : ∀ j < n, ∫ x, ‖K j x‖ ∂μ ≤ B / 2^j) :
    (∫ x, ‖∑ j ∈ Finset.range n, K j x‖^2 ∂μ) ≤ 3 * A * B * n := by
  have hb (x : X) : ‖∑ j ∈ Finset.range n, K j x‖^2 ≤
      3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * ‖K j x‖ := by
    have hz : 0 ≤ ∑ j ∈ Finset.range n, ‖K j x‖ := by positivity
    have hn := norm_sum_le (Finset.range n) (fun j => K j x)
    exact (sq_le_sq₀ (norm_nonneg _) hz).mpr hn |>.trans
      (dyadic_sum_square (fun j => ‖K j x‖) A hA n
        (fun j hj => ⟨norm_nonneg _, hbound j hj x⟩))
  have hi : Integrable
      (fun x => 3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * ‖K j x‖) μ := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ fun j hj =>
      ((hK j (Finset.mem_range.mp hj)).norm).const_mul _
  have hs : AEStronglyMeasurable (fun x => ∑ j ∈ Finset.range n, K j x) μ := by
    convert Finset.aestronglyMeasurable_sum (Finset.range n) (fun j hj =>
        (hK j (Finset.mem_range.mp hj)).aestronglyMeasurable) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact (Finset.sum_apply x _ _).symm
  have hi' : Integrable (fun x => ‖∑ j ∈ Finset.range n, K j x‖^2) μ := by
    apply hi.mono' (hs.norm.pow 2)
    exact Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x
  calc
    _ ≤ ∫ x, 3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * ‖K j x‖ ∂μ :=
      integral_mono hi' hi hb
    _ = 3 * A * ∑ j ∈ Finset.range n, (2 : ℝ)^j * ∫ x, ‖K j x‖ ∂μ := by
      rw [integral_const_mul, integral_finsetSum]
      · simp_rw [integral_const_mul]
      · intro j hj
        exact ((hK j (Finset.mem_range.mp hj)).norm).const_mul _
    _ ≤ 3 * A * ∑ j ∈ Finset.range n, B := by
      gcongr with j hj
      have hp : 0 < (2 : ℝ)^j := by positivity
      have hh := mul_le_mul_of_nonneg_left (h₁ j (Finset.mem_range.mp hj)) hp.le
      simpa [mul_div_cancel₀ B (ne_of_gt hp)] using hh
    _ = _ := by simp; ring

lemma openUnitStrip_isOpen : IsOpen openUnitStrip := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

lemma openUnitStrip_measure_lt_top : volume openUnitStrip < ⊤ := by
  have hs : openUnitStrip ⊆ Metric.closedBall (0:ℂ) (1+Real.pi) := by
    intro z hz
    change 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < Real.pi at hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have hn := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hz.1,abs_of_pos hz.2.2.1] at hn
    linarith [hz.2.1,hz.2.2.2]
  exact (measure_mono hs).trans_lt (isCompact_closedBall (0:ℂ) (1+Real.pi)).measure_lt_top

instance finite_openUnitStrip : IsFiniteMeasure (volume.restrict openUnitStrip) :=
  isFiniteMeasure_restrict.mpr openUnitStrip_measure_lt_top.ne

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StripKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strip Kernels for chordal SLE. -/

section
section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge
lemma integrable_mul_compact_test {μ : Measure ℂ} {f g : ℂ → ℝ}
    (hf : Integrable f μ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun z => f z * g z) μ := by
  obtain ⟨C, hC⟩ := (hgc.isCompact_range hg).isBounded.exists_norm_le
  exact hf.mul_bdd hg.aestronglyMeasurable
    (Eventually.of_forall fun z => hC _ ⟨z,rfl⟩)

lemma weak_gradient_pairing {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) {X Y : ℂ → ℝ}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (hcX : HasCompactSupport X) (hcY : HasCompactSupport Y)
    (hsX : tsupport X ⊆ openUnitStrip) (hsY : tsupport Y ⊆ openUnitStrip) :
    (∫ z in openUnitStrip, u z * ((fderiv ℝ X z) 1 + (fderiv ℝ Y z) Complex.I)) =
      -(∫ z in openUnitStrip, (D z).re * X z + (D z).im * Y z) := by
  have hui := hu.1.integrable (by norm_num)
  have hDi := hu.2.1.integrable (by norm_num)
  have hx := integrable_mul_compact_test hui
    ((hX.continuous_fderiv (by simp)).clm_apply continuous_const) (hcX.fderiv_apply ℝ 1)
  have hy := integrable_mul_compact_test hui
    ((hY.continuous_fderiv (by simp)).clm_apply continuous_const) (hcY.fderiv_apply ℝ Complex.I)
  have hdx := integrable_mul_compact_test (Complex.reCLM.integrable_comp hDi) hX.continuous hcX
  have hdy := integrable_mul_compact_test (Complex.imCLM.integrable_comp hDi) hY.continuous hcY
  change Integrable (fun z => (D z).re * X z) _ at hdx
  change Integrable (fun z => (D z).im * Y z) _ at hdy
  simp_rw [mul_add]
  rw [integral_add hx hy, (hu.2.2 X hX hcX hsX).1, (hu.2.2 Y hY hcY hsY).2,
    integral_add hdx hdy]
  ring

lemma complex_pairing_abs_le (D : ℂ) (X Y : ℝ) :
    |D.re * X + D.im * Y| ≤ ‖D‖ * (|X|+|Y|) := by
  calc
    _ ≤ |D.re * X| + |D.im * Y| := abs_add_le _ _
    _ ≤ ‖D‖ * |X| + ‖D‖ * |Y| := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm D) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm D) (abs_nonneg _))
    _ = _ := by ring

lemma integral_nonneg_cauchy {μ : Measure ℂ} {f g : ℂ → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) :
    (∫ z, f z * g z ∂μ) ≤
      Real.sqrt (∫ z, (f z)^2 ∂μ) * Real.sqrt (∫ z, (g z)^2 ∂μ) := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hf0) (Eventually.of_forall hg0)
    (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hh

lemma integral_pairing_le {D : ℂ → ℂ}
    (hD : MemLp D 2 (volume.restrict openUnitStrip)) {X Y : ℂ → ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (hcX : HasCompactSupport X) (hcY : HasCompactSupport Y) :
    |∫ z in openUnitStrip, (D z).re * X z + (D z).im * Y z| ≤
      Real.sqrt (stripDirichletEnergy D) *
        Real.sqrt (∫ z in openUnitStrip, (|X z|+|Y z|)^2) := by
  have hDi := hD.integrable (by norm_num)
  have hdx := integrable_mul_compact_test (Complex.reCLM.integrable_comp hDi) hX hcX
  have hdy := integrable_mul_compact_test (Complex.imCLM.integrable_comp hDi) hY hcY
  have hK : MemLp (fun z => |X z|+|Y z|) 2 (volume.restrict openUnitStrip) :=
    (hX.abs.add hY.abs).memLp_of_hasCompactSupport (hcX.abs.add hcY.abs)
  calc
    _ ≤ ∫ z in openUnitStrip, |(D z).re * X z + (D z).im * Y z| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => (D z).re * X z + (D z).im * Y z)
    _ ≤ ∫ z in openUnitStrip, ‖D z‖ * (|X z|+|Y z|) :=
      integral_mono (hdx.add hdy).abs (hD.norm.integrable_mul hK)
        (fun z => complex_pairing_abs_le ..)
    _ ≤ _ := integral_nonneg_cauchy hD.norm hK (fun _ => norm_nonneg _)
      (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

lemma chainX_smooth (t s : ℝ) (j n : ℕ) : ContDiff ℝ ∞ (chainX t s j n) :=
  rectangleTransportX_contDiff ..
lemma chainY_smooth (t s : ℝ) (j n : ℕ) : ContDiff ℝ ∞ (chainY t s j n) :=
  rectangleTransportY_contDiff ..
lemma chainX_compact {t : ℝ} (s : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (j n : ℕ) :
    HasCompactSupport (chainX t s j n) :=
  rectangleTransportX_compact _ _ _ _ _ _ _ _
    (scaleOrigin_step ht j) (scaleOrigin_right_step ht1 j) n
lemma chainY_compact (t : ℝ) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    HasCompactSupport (chainY t s j n) := by
  apply rectangleTransportY_compact
  · exact mul_le_mul_of_nonneg_left (scaleOrigin_step hs j) Real.pi_pos.le
  · have hh := mul_le_mul_of_nonneg_left (scaleOrigin_right_step hs1 j) Real.pi_pos.le
    nlinarith

lemma chainX_support {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    tsupport (chainX t s j n) ⊆ openUnitStrip := by
  have hh := rectangleTransportX_support (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1))
    (scaleOrigin_step ht j) (scaleOrigin_right_step ht1 j)
    (mul_le_mul_of_nonneg_left (scaleOrigin_step hs j) Real.pi_pos.le)
    (by have := mul_le_mul_of_nonneg_left (scaleOrigin_right_step hs1 j) Real.pi_pos.le
        nlinarith) n
  intro z hz
  obtain ⟨h1,h2,h3,h4⟩ := hh hz
  have h5 := scaleOrigin_nonneg ht j
  have h6 := scaleOrigin_add_le_one ht1 j
  have h7 := mul_nonneg Real.pi_pos.le (scaleOrigin_nonneg hs j)
  have h8 := mul_le_mul_of_nonneg_left (scaleOrigin_add_le_one hs1 j) Real.pi_pos.le
  exact ⟨by linarith, by linarith, by linarith, by nlinarith⟩

lemma chainY_support {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    tsupport (chainY t s j n) ⊆ openUnitStrip := by
  have hh := rectangleTransportY_support (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1))
    (mul_le_mul_of_nonneg_left (scaleOrigin_step hs j) Real.pi_pos.le)
    (by have := mul_le_mul_of_nonneg_left (scaleOrigin_right_step hs1 j) Real.pi_pos.le
        nlinarith) n
  intro z hz
  obtain ⟨h1,h2,h3,h4⟩ := hh hz
  have h5 := scaleOrigin_nonneg ht j
  have h6 := scaleOrigin_add_le_one ht1 j
  have h7 := mul_nonneg Real.pi_pos.le (scaleOrigin_nonneg hs j)
  have h8 := mul_le_mul_of_nonneg_left (scaleOrigin_add_le_one hs1 j) Real.pi_pos.le
  exact ⟨by linarith, by linarith, by linarith, by nlinarith⟩

lemma chain_divergence (t s : ℝ) (j n : ℕ) (z : ℂ) :
    (fderiv ℝ (chainX t s j n) z) 1 + (fderiv ℝ (chainY t s j n) z) Complex.I =
      chainDensity t s (j+1) n z - chainDensity t s j n z := by
  unfold chainX chainY chainDensity
  rw [rectangleTransport_divergence]
  simp only [scaleLength_succ, mul_div_assoc]

lemma chainKernel_continuous (t s : ℝ) (j n : ℕ) : Continuous (chainKernel t s j n) :=
  (chainX_smooth t s j n).continuous.abs.add (chainY_smooth t s j n).continuous.abs
lemma chainKernel_compact {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    HasCompactSupport (chainKernel t s j n) :=
  (chainX_compact s ht ht1 j n).abs.add (chainY_compact t hs hs1 j n).abs
lemma chainKernel_nonneg (t s : ℝ) (j n : ℕ) (z : ℂ) : 0 ≤ chainKernel t s j n z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma chainKernel_bound (t s : ℝ) (j n : ℕ) (z : ℂ) :
    ‖chainKernel t s j n z‖ ≤ 12 * (2:ℝ)^j := by
  rw [Real.norm_of_nonneg (chainKernel_nonneg ..)]
  have hx := rectangleTransportX_bound (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1)) n z
  have hy := rectangleTransportY_bound (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1)) n z
  have hp : scaleLength j ≤ Real.pi*scaleLength j := by
    nlinarith [scaleLength_pos j, Real.pi_gt_three]
  have hx' := hx.trans (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8)
    (scaleLength_pos j) hp)
  change |chainX t s j n z| + |chainY t s j n z| ≤ _
  calc
    _ ≤ 8/scaleLength j + 4/scaleLength j := add_le_add hx' hy
    _ = _ := by unfold scaleLength; field_simp; ring

lemma chainKernel_integral_bound {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (j n : ℕ) :
    (∫ z, ‖chainKernel t s j n z‖) ≤ 10 / (2:ℝ)^j := by
  have hx := rectangleTransportX_integral_abs (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1))
    (scaleOrigin_step ht j) (scaleOrigin_right_step ht1 j) n
  have hy := rectangleTransportY_integral_abs (scaleOrigin t j) (Real.pi*scaleOrigin s j)
    (scaleLength j) (Real.pi*scaleLength j) (scaleLength_pos j)
    (mul_pos Real.pi_pos (scaleLength_pos j))
    (scaleOrigin t (j+1)) (Real.pi*scaleOrigin s (j+1))
    (mul_le_mul_of_nonneg_left (scaleOrigin_step hs j) Real.pi_pos.le)
    (by have := mul_le_mul_of_nonneg_left (scaleOrigin_right_step hs1 j) Real.pi_pos.le
        nlinarith) n
  have hiX := (chainX_smooth t s j n).continuous.integrable_of_hasCompactSupport (μ := volume)
    (chainX_compact s ht ht1 j n)
  have hiY := (chainY_smooth t s j n).continuous.integrable_of_hasCompactSupport (μ := volume)
    (chainY_compact t hs hs1 j n)
  simp_rw [Real.norm_of_nonneg (chainKernel_nonneg ..)]
  change (∫ z, |chainX t s j n z| + |chainY t s j n z|) ≤ _
  rw [integral_add hiX.abs hiY.abs]
  change (∫ z, |chainX t s j n z|) ≤ _ at hx
  change (∫ z, |chainY t s j n z|) ≤ _ at hy
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (scaleLength_pos j).le
  have hh : 10*scaleLength j = 10/(2:ℝ)^j := by simp [scaleLength, div_eq_mul_inv]
  nlinarith

lemma compact_sum_range {f : ℕ → ℂ → ℝ} (hf : ∀ j, HasCompactSupport (f j)) (k : ℕ) :
    HasCompactSupport (fun z => ∑ j ∈ Finset.range k, f j z) := by
  induction k with
  | zero => simp [HasCompactSupport]
  | succ k ih =>
    simp only [Finset.sum_range_succ]
    exact (ih.union (hf k)).of_isClosed_subset (isClosed_tsupport _) (tsupport_add _ _)

lemma support_sum_range {f : ℕ → ℂ → ℝ} {S : Set ℂ}
    (hf : ∀ j, tsupport (f j) ⊆ S) (k : ℕ) :
    tsupport (fun z => ∑ j ∈ Finset.range k, f j z) ⊆ S := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Finset.sum_range_succ]
    exact (tsupport_add _ _).trans (union_subset ih (hf k))

lemma aggregateX_smooth (t s : ℝ) (k n : ℕ) : ContDiff ℝ ∞ (aggregateX t s k n) :=
  ContDiff.sum (fun j _ => chainX_smooth t s j n)
lemma aggregateY_smooth (t s : ℝ) (k n : ℕ) : ContDiff ℝ ∞ (aggregateY t s k n) :=
  ContDiff.sum (fun j _ => chainY_smooth t s j n)
lemma aggregateX_compact {t : ℝ} (s : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (k n : ℕ) :
    HasCompactSupport (aggregateX t s k n) :=
  compact_sum_range (fun j => chainX_compact s ht ht1 j n) k
lemma aggregateY_compact (t : ℝ) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    HasCompactSupport (aggregateY t s k n) :=
  compact_sum_range (fun j => chainY_compact t hs hs1 j n) k
lemma aggregateX_support {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    tsupport (aggregateX t s k n) ⊆ openUnitStrip :=
  support_sum_range (fun j => chainX_support ht ht1 hs hs1 j n) k
lemma aggregateY_support {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    tsupport (aggregateY t s k n) ⊆ openUnitStrip :=
  support_sum_range (fun j => chainY_support ht ht1 hs hs1 j n) k

lemma aggregate_divergence (t s : ℝ) (k n : ℕ) (z : ℂ) :
    (fderiv ℝ (aggregateX t s k n) z) 1 + (fderiv ℝ (aggregateY t s k n) z) Complex.I =
      chainDensity t s k n z - chainDensity t s 0 n z := by
  unfold aggregateX aggregateY
  rw [fderiv_fun_sum (fun j _ => ((chainX_smooth t s j n).differentiable (by simp)) z),
    fderiv_fun_sum (fun j _ => ((chainY_smooth t s j n).differentiable (by simp)) z)]
  simp only [sum_apply, ← Finset.sum_add_distrib]
  simp_rw [chain_divergence]
  exact Finset.sum_range_sub (fun j => chainDensity t s j n z) k

lemma aggregate_kernel_bound {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    (∫ z in openUnitStrip, (|aggregateX t s k n z|+|aggregateY t s k n z|)^2) ≤ 360*k := by
  have hsum : (∫ z in openUnitStrip, ‖∑ j ∈ Finset.range k, chainKernel t s j n z‖^2) ≤
      3*12*10*k := by
    apply integral_sum_kernel_sq_le (fun j => chainKernel t s j n) 12 10 k
      (by norm_num) (by norm_num)
    · intro j _
      exact ((chainKernel_continuous t s j n).integrable_of_hasCompactSupport
        (chainKernel_compact ht ht1 hs hs1 j n)).integrableOn
    · intro j _ z
      exact chainKernel_bound t s j n z
    · intro j _
      refine (setIntegral_le_integral ?_ (Eventually.of_forall (fun _ => norm_nonneg _))).trans
        (chainKernel_integral_bound ht ht1 hs hs1 j n)
      exact ((chainKernel_continuous t s j n).integrable_of_hasCompactSupport
        (chainKernel_compact ht ht1 hs hs1 j n)).norm
  have hI : Integrable (fun z => (|aggregateX t s k n z|+|aggregateY t s k n z|)^2)
      (volume.restrict openUnitStrip) := by
    apply MemLp.integrable_sq
    exact ((aggregateX_smooth t s k n).continuous.abs.add
      (aggregateY_smooth t s k n).continuous.abs).memLp_of_hasCompactSupport
      ((aggregateX_compact s ht ht1 k n).abs.add (aggregateY_compact t hs hs1 k n).abs)
  have hJ : Integrable (fun z => ‖∑ j ∈ Finset.range k, chainKernel t s j n z‖^2)
      (volume.restrict openUnitStrip) := by
    have hc := continuous_finsetSum (Finset.range k) (fun j _ => chainKernel_continuous t s j n)
    exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).1
      (hc.memLp_of_hasCompactSupport
        (compact_sum_range (fun j => chainKernel_compact ht ht1 hs hs1 j n) k))
  refine (integral_mono hI hJ ?_).trans (by linarith)
  intro z
  have hh : |aggregateX t s k n z|+|aggregateY t s k n z| ≤
      ∑ j ∈ Finset.range k, chainKernel t s j n z := by
    unfold aggregateX aggregateY chainKernel
    rw [Finset.sum_add_distrib]
    exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).2
  exact hh.trans (le_abs_self _)

lemma chainDensity_continuous (t s : ℝ) (j n : ℕ) : Continuous (chainDensity t s j n) :=
  (complexTensor_contDiff (intervalDensity_smooth ..) (intervalDensity_smooth ..)).continuous
lemma chainDensity_compact (t s : ℝ) (j n : ℕ) : HasCompactSupport (chainDensity t s j n) :=
  complexTensor_compact (intervalDensity_compact ..) (intervalDensity_compact ..)

lemma smoothed_means_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k n : ℕ) :
    |(∫ z in openUnitStrip, u z * chainDensity t s k n z) -
      (∫ z in openUnitStrip, u z * chainDensity t s 0 n z)| ≤
      20 * Real.sqrt (((k:ℝ)+1)*stripDirichletEnergy D) := by
  have he := weak_gradient_pairing hu (aggregateX_smooth t s k n) (aggregateY_smooth t s k n)
    (aggregateX_compact s ht ht1 k n) (aggregateY_compact t hs hs1 k n)
    (aggregateX_support ht ht1 hs hs1 k n) (aggregateY_support ht ht1 hs hs1 k n)
  simp_rw [aggregate_divergence] at he
  have hi₁ := integrable_mul_compact_test (hu.1.integrable (by norm_num))
    (chainDensity_continuous t s k n) (chainDensity_compact t s k n)
  have hi₀ := integrable_mul_compact_test (hu.1.integrable (by norm_num))
    (chainDensity_continuous t s 0 n) (chainDensity_compact t s 0 n)
  simp_rw [mul_sub] at he
  rw [integral_sub hi₁ hi₀] at he
  rw [he, abs_neg]
  refine (integral_pairing_le hu.2.1 (aggregateX_smooth t s k n).continuous
    (aggregateY_smooth t s k n).continuous (aggregateX_compact s ht ht1 k n)
    (aggregateY_compact t hs hs1 k n)).trans ?_
  have hE : 0 ≤ stripDirichletEnergy D := integral_nonneg (fun _ => sq_nonneg _)
  have hA : 0 ≤ ∫ z in openUnitStrip, (|aggregateX t s k n z|+|aggregateY t s k n z|)^2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hb := aggregate_kernel_bound ht ht1 hs hs1 k n
  have hR : 0 ≤ ((k:ℝ)+1)*stripDirichletEnergy D := by positivity
  have hSqE := Real.sq_sqrt hE
  have hSqA := Real.sq_sqrt hA
  have hSqR := Real.sq_sqrt hR
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, hSqE, hSqA, mul_pow, hSqR]
  nlinarith [mul_le_mul_of_nonneg_left hb hE]

lemma stripRectangle_eq_preimage (a b l : ℝ) :
    stripRectangle a b l = Complex.measurableEquivRealProd ⁻¹'
      (Icc a (a+l) ×ˢ Icc b (b+Real.pi*l)) := by
  ext z
  simp only [stripRectangle, mem_ofPred_eq, mem_preimage, mem_prod, mem_Icc,
    Complex.measurableEquivRealProd_apply]
  tauto

lemma stripRectangle_volume (a b l : ℝ) :
    volume (stripRectangle a b l) = ENNReal.ofReal l * ENNReal.ofReal (Real.pi*l) := by
  rw [stripRectangle_eq_preimage,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp only [Real.volume_Icc, add_sub_cancel_left]

lemma openStripRectangle_eq_preimage (a b l : ℝ) :
    openStripRectangle a b l = Complex.measurableEquivRealProd ⁻¹'
      (Ioo a (a+l) ×ˢ Ioo b (b+Real.pi*l)) := by
  ext z
  simp only [openStripRectangle, mem_ofPred_eq, mem_preimage, mem_prod, mem_Ioo,
    Complex.measurableEquivRealProd_apply]
  tauto

lemma openStripRectangle_measurable (a b l : ℝ) : MeasurableSet (openStripRectangle a b l) := by
  rw [openStripRectangle_eq_preimage]
  exact (measurableSet_Ioo.prod measurableSet_Ioo).preimage
    Complex.measurableEquivRealProd.measurable

lemma openStripRectangle_ae_eq (a b l : ℝ) :
    openStripRectangle a b l =ᵐ[volume] stripRectangle a b l := by
  rw [openStripRectangle_eq_preimage, stripRectangle_eq_preimage]
  apply Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.preimage_ae_eq
  rw [Measure.volume_eq_prod]
  exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc

lemma rectangleDensity_nonneg (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (n : ℕ) (z : ℂ) : 0 ≤ rectangleDensity a b lx ly hx hy n z :=
  mul_nonneg (intervalDensity_nonneg ..) (intervalDensity_nonneg ..)
lemma rectangleDensity_bound (a b lx ly : ℝ) (hx : 0 < lx) (hy : 0 < ly)
    (n : ℕ) (z : ℂ) : rectangleDensity a b lx ly hx hy n z ≤ 4/(lx*ly) := by
  calc
    _ ≤ (2/lx)*(2/ly) := mul_le_mul (intervalDensity_bound ..) (intervalDensity_bound ..)
      (intervalDensity_nonneg ..) (by positivity)
    _ = _ := by ring

lemma rectangleDensity_tendsto (a b l : ℝ) (hl : 0 < l) (z : ℂ) :
    Tendsto (fun n => rectangleDensity a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) n z)
      atTop (𝓝 ((openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z)) := by
  have hh := (intervalDensity_tendsto a l hl z.re).mul
    (intervalDensity_tendsto b (Real.pi*l) (mul_pos Real.pi_pos hl) z.im)
  have heq : (openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z =
      (Ioo a (a+l)).indicator (fun _ => 1/l) z.re *
        (Ioo b (b+Real.pi*l)).indicator (fun _ => 1/(Real.pi*l)) z.im := by
    by_cases hx : z.re ∈ Ioo a (a+l) <;> by_cases hy : z.im ∈ Ioo b (b+Real.pi*l)
    · have hz : z ∈ openStripRectangle a b l := ⟨hx.1,hx.2,hy.1,hy.2⟩
      simp [hz,hx,hy,one_div]
      ring
    · have hz : z ∉ openStripRectangle a b l := fun hz => hy ⟨hz.2.2.1,hz.2.2.2⟩
      simp [hz,hx,hy]
    · have hz : z ∉ openStripRectangle a b l := fun hz => hx ⟨hz.1,hz.2.1⟩
      simp [hz,hx,hy]
    · have hz : z ∉ openStripRectangle a b l := fun hz => hx ⟨hz.1,hz.2.1⟩
      simp [hz,hx,hy]
  simpa only [rectangleDensity, complexTensor, heq] using hh

lemma rectangle_smoothed_mean_tendsto {u : ℂ → ℝ}
    (hu : MemLp u 2 (volume.restrict openUnitStrip)) (a b l : ℝ) (hl : 0 < l)
    (ha : 0 ≤ a) (ha1 : a+l ≤ 1) (hb : 0 ≤ b) (hb1 : b+Real.pi*l ≤ Real.pi) :
    Tendsto (fun n => ∫ z in openUnitStrip,
      u z * rectangleDensity a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) n z)
      atTop (𝓝 (spatialAverage u (stripRectangle a b l))) := by
  have hsub : openStripRectangle a b l ⊆ openUnitStrip := by
    intro z hz
    exact ⟨ha.trans_lt hz.1, hz.2.1.trans_le ha1, hb.trans_lt hz.2.2.1, hz.2.2.2.trans_le hb1⟩
  have hint := hu.integrable (by norm_num)
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict openUnitStrip)
    (F := fun n z => u z * rectangleDensity a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) n z)
    (f := fun z => u z * (openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z)
    (fun z => |u z| * (4/(l*(Real.pi*l))))
    (fun n => hu.aestronglyMeasurable.mul
      ((complexTensor_contDiff (intervalDensity_smooth ..) (intervalDensity_smooth ..)).continuous.aestronglyMeasurable))
    (hint.abs.mul_const _) (fun n => Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rectangleDensity_nonneg ..)]
      exact mul_le_mul_of_nonneg_left (rectangleDensity_bound ..) (abs_nonneg _))
    (Eventually.of_forall fun z => (rectangleDensity_tendsto a b l hl z).const_mul (u z))
  have heq : (∫ z in openUnitStrip,
      u z * (openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z) =
      spatialAverage u (stripRectangle a b l) := by
    have hfun : (fun z => u z * (openStripRectangle a b l).indicator (fun _ => 1/(l*(Real.pi*l))) z) =
        (openStripRectangle a b l).indicator (fun z => u z * (1/(l*(Real.pi*l)))) := by
      funext z
      by_cases hz : z ∈ openStripRectangle a b l <;> simp [hz]
    rw [hfun, integral_indicator (openStripRectangle_measurable a b l),
      Measure.restrict_restrict (openStripRectangle_measurable a b l), inter_eq_left.mpr hsub,
      integral_mul_const, setIntegral_congr_set (openStripRectangle_ae_eq a b l)]
    unfold spatialAverage
    rw [stripRectangle_volume, ENNReal.toReal_mul, ENNReal.toReal_ofReal hl.le,
      ENNReal.toReal_ofReal (mul_pos Real.pi_pos hl).le]
    ring
  rwa [heq] at hlim

lemma chain_means_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) {t s : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (k : ℕ) :
    |spatialAverage u (stripRectangle (scaleOrigin t k) (Real.pi*scaleOrigin s k) (scaleLength k)) -
      spatialAverage u (stripRectangle 0 0 1)| ≤
      20 * Real.sqrt (((k:ℝ)+1)*stripDirichletEnergy D) := by
  have hlim (j : ℕ) : Tendsto (fun n => ∫ z in openUnitStrip, u z * chainDensity t s j n z)
      atTop (𝓝 (spatialAverage u (stripRectangle (scaleOrigin t j)
        (Real.pi*scaleOrigin s j) (scaleLength j)))) := by
    apply rectangle_smoothed_mean_tendsto hu.1 _ _ _ (scaleLength_pos j)
      (scaleOrigin_nonneg ht j) (scaleOrigin_add_le_one ht1 j)
      (mul_nonneg Real.pi_pos.le (scaleOrigin_nonneg hs j))
    have hh := mul_le_mul_of_nonneg_left (scaleOrigin_add_le_one hs1 j) Real.pi_pos.le
    nlinarith
  have hzero := hlim 0
  simp only [scaleOrigin_zero, scaleLength_zero, mul_zero] at hzero
  exact le_of_tendsto ((hlim k).sub hzero).abs
    (Eventually.of_forall (fun n => smoothed_means_le hu ht ht1 hs hs1 k n))

lemma integral_pairing_local_le {D : ℂ → ℂ}
    (hD : MemLp D 2 (volume.restrict openUnitStrip)) {V : Set ℂ}
    (hV : V ⊆ openUnitStrip) {X Y : ℂ → ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (hcX : HasCompactSupport X) (hcY : HasCompactSupport Y)
    (hsX : tsupport X ⊆ V) (hsY : tsupport Y ⊆ V) :
    |∫ z in openUnitStrip, (D z).re * X z + (D z).im * Y z| ≤
      Real.sqrt (∫ z in V, ‖D z‖^2) *
        Real.sqrt (∫ z in V, (|X z|+|Y z|)^2) := by
  have hm : volume.restrict V ≤ volume.restrict openUnitStrip :=
    Measure.restrict_mono hV le_rfl
  have hDl := hD.mono_measure hm
  have hDi := (hD.integrable (by norm_num)).mono_measure hm
  have hdx := integrable_mul_compact_test (Complex.reCLM.integrable_comp hDi) hX hcX
  have hdy := integrable_mul_compact_test (Complex.imCLM.integrable_comp hDi) hY hcY
  have hK : MemLp (fun z => |X z|+|Y z|) 2 (volume.restrict V) :=
    (hX.abs.add hY.abs).memLp_of_hasCompactSupport (hcX.abs.add hcY.abs)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero openUnitStrip_isOpen.measurableSet hV
    (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz.2 (hsX h)),
        image_eq_zero_of_notMem_tsupport (fun h => hz.2 (hsY h))]
      ring)]
  calc
    _ ≤ ∫ z in V, |(D z).re * X z + (D z).im * Y z| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z => (D z).re * X z + (D z).im * Y z)
    _ ≤ ∫ z in V, ‖D z‖ * (|X z|+|Y z|) :=
      integral_mono (hdx.add hdy).abs (hDl.norm.integrable_mul hK)
        (fun z => complex_pairing_abs_le ..)
    _ ≤ _ := integral_nonneg_cauchy hDl.norm hK (fun _ => norm_nonneg _)
      (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

lemma rectangle_transport_L2_bound (a b l : ℝ) (hl : 0 < l) (a' b' : ℝ)
    (ha : a ≤ a') (ha' : a'+l/2 ≤ a+l)
    (hb : b ≤ b') (hb' : b'+(Real.pi*l)/2 ≤ b+Real.pi*l) (n : ℕ) (V : Set ℂ) :
    (∫ z in V, (|rectangleTransportX a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n z| +
      |rectangleTransportY a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n z|)^2) ≤ 120 := by
  let X := rectangleTransportX a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n
  let Y := rectangleTransportY a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n
  have hx := (rectangleTransportX_contDiff a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n).continuous
  have hy := (rectangleTransportY_contDiff a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n).continuous
  have hcx := rectangleTransportX_compact a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' ha ha' n
  have hcy := rectangleTransportY_compact a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' hb hb' n
  have hK : Continuous (fun z => |X z|+|Y z|) := hx.abs.add hy.abs
  have hcK : HasCompactSupport (fun z => |X z|+|Y z|) := hcx.abs.add hcy.abs
  have hKi := hK.integrable_of_hasCompactSupport (μ := volume) hcK
  have hKsq : Integrable (fun z => (|X z|+|Y z|)^2) volume :=
    (hK.memLp_of_hasCompactSupport (p := 2) hcK).integrable_sq
  have hK0 (z : ℂ) : 0 ≤ |X z|+|Y z| := by positivity
  have hKb (z : ℂ) : |X z|+|Y z| ≤ 12/l := by
    have hx' := rectangleTransportX_bound a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n z
    have hy' := rectangleTransportY_bound a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n z
    have hp : l ≤ Real.pi*l := by nlinarith [Real.pi_gt_three]
    have hx'' := hx'.trans (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 8) hl hp)
    change |X z| ≤ _ at hx''
    change |Y z| ≤ _ at hy'
    calc
      _ ≤ 8/l+4/l := add_le_add hx'' hy'
      _ = 12/l := by ring
  have hKI : (∫ z, |X z|+|Y z|) ≤ 10*l := by
    rw [integral_add (hx.integrable_of_hasCompactSupport hcx).abs
      (hy.integrable_of_hasCompactSupport hcy).abs]
    have hx' := rectangleTransportX_integral_abs a b l (Real.pi*l) hl
      (mul_pos Real.pi_pos hl) a' b' ha ha' n
    have hy' := rectangleTransportY_integral_abs a b l (Real.pi*l) hl
      (mul_pos Real.pi_pos hl) a' b' hb hb' n
    change (∫ z, |X z|) ≤ _ at hx'
    change (∫ z, |Y z|) ≤ _ at hy'
    nlinarith [Real.pi_lt_four]
  change (∫ z in V, (|X z|+|Y z|)^2) ≤ _
  calc
    _ ≤ ∫ z, (|X z|+|Y z|)^2 :=
      setIntegral_le_integral hKsq (Eventually.of_forall (fun _ => sq_nonneg _))
    _ ≤ ∫ z, (12/l)*(|X z|+|Y z|) := integral_mono hKsq (hKi.const_mul _) (fun z => by
      nlinarith [mul_le_mul_of_nonneg_right (hKb z) (hK0 z)])
    _ = (12/l)*∫ z, |X z|+|Y z| := integral_const_mul ..
    _ ≤ (12/l)*(10*l) := mul_le_mul_of_nonneg_left hKI (by positivity)
    _ = 120 := by field_simp; ring

lemma openStripRectangle_subset_unit {a b l : ℝ}
    (ha : 0 ≤ a) (ha1 : a+l ≤ 1) (hb : 0 ≤ b) (hb1 : b+Real.pi*l ≤ Real.pi) :
    openStripRectangle a b l ⊆ openUnitStrip := by
  intro z hz
  exact ⟨ha.trans_lt hz.1, hz.2.1.trans_le ha1,
    hb.trans_lt hz.2.2.1, hz.2.2.2.trans_le hb1⟩

lemma local_means_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) (a b l : ℝ) (hl : 0 < l)
    (ha : 0 ≤ a) (ha1 : a+l ≤ 1) (hb : 0 ≤ b) (hb1 : b+Real.pi*l ≤ Real.pi)
    (a' b' : ℝ) (haa : a ≤ a') (haa' : a'+l/2 ≤ a+l)
    (hbb : b ≤ b') (hbb' : b'+(Real.pi*l)/2 ≤ b+Real.pi*l) :
    |spatialAverage u (stripRectangle a' b' (l/2)) -
      spatialAverage u (stripRectangle a b l)| ≤
      12 * Real.sqrt (∫ z in openStripRectangle a b l, ‖D z‖^2) := by
  have hsub := openStripRectangle_subset_unit ha ha1 hb hb1
  have hsmooth (n : ℕ) :
      |(∫ z in openUnitStrip, u z * rectangleDensity a' b' (l/2) (Real.pi*(l/2))
          (by positivity) (by positivity) n z) -
        (∫ z in openUnitStrip, u z * rectangleDensity a b l (Real.pi*l)
          hl (mul_pos Real.pi_pos hl) n z)| ≤
      12 * Real.sqrt (∫ z in openStripRectangle a b l, ‖D z‖^2) := by
    let X := rectangleTransportX a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n
    let Y := rectangleTransportY a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n
    have hx : ContDiff ℝ ∞ X := rectangleTransportX_contDiff ..
    have hy : ContDiff ℝ ∞ Y := rectangleTransportY_contDiff ..
    have hcx : HasCompactSupport X := rectangleTransportX_compact _ _ _ _ _ _ _ _ haa haa' n
    have hcy : HasCompactSupport Y := rectangleTransportY_compact _ _ _ _ _ _ _ _ hbb hbb' n
    have hsx : tsupport X ⊆ openStripRectangle a b l :=
      rectangleTransportX_support _ _ _ _ _ _ _ _ haa haa' hbb hbb' n
    have hsy : tsupport Y ⊆ openStripRectangle a b l :=
      rectangleTransportY_support _ _ _ _ _ _ _ _ hbb hbb' n
    have he := weak_gradient_pairing hu hx hy hcx hcy (hsx.trans hsub) (hsy.trans hsub)
    change (∫ z in openUnitStrip, u z *
      ((fderiv ℝ (rectangleTransportX a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n) z) 1 +
       (fderiv ℝ (rectangleTransportY a b l (Real.pi*l) hl (mul_pos Real.pi_pos hl) a' b' n) z) Complex.I)) = _ at he
    simp_rw [rectangleTransport_divergence, show Real.pi*l/2 = Real.pi*(l/2) by ring, mul_sub] at he
    have hi₁ := integrable_mul_compact_test (hu.1.integrable (by norm_num))
      (complexTensor_contDiff (intervalDensity_smooth a' (l/2) (by positivity) n)
        (intervalDensity_smooth b' (Real.pi*(l/2)) (by positivity) n)).continuous
      (complexTensor_compact (intervalDensity_compact ..) (intervalDensity_compact ..))
    have hi₀ := integrable_mul_compact_test (hu.1.integrable (by norm_num))
      (complexTensor_contDiff (intervalDensity_smooth a l hl n)
        (intervalDensity_smooth b (Real.pi*l) (mul_pos Real.pi_pos hl) n)).continuous
      (complexTensor_compact (intervalDensity_compact ..) (intervalDensity_compact ..))
    dsimp only [rectangleDensity] at he ⊢
    rw [integral_sub hi₁ hi₀] at he
    rw [he, abs_neg]
    refine (integral_pairing_local_le hu.2.1 hsub hx.continuous hy.continuous hcx hcy hsx hsy).trans ?_
    have hbnd := rectangle_transport_L2_bound a b l hl a' b' haa haa' hbb hbb' n
      (openStripRectangle a b l)
    change (∫ z in openStripRectangle a b l, (|X z|+|Y z|)^2) ≤ 120 at hbnd
    have hE : 0 ≤ ∫ z in openStripRectangle a b l, ‖D z‖^2 := integral_nonneg (fun _ => sq_nonneg _)
    have hA : 0 ≤ ∫ z in openStripRectangle a b l, (|X z|+|Y z|)^2 := integral_nonneg (fun _ => sq_nonneg _)
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hA, mul_pow, Real.sq_sqrt hE]
    nlinarith [mul_le_mul_of_nonneg_left hbnd hE]
  have hlim₀ := rectangle_smoothed_mean_tendsto hu.1 a b l hl ha ha1 hb hb1
  have hlim₁ := rectangle_smoothed_mean_tendsto hu.1 a' b' (l/2) (by positivity)
    (ha.trans haa) (haa'.trans ha1) (hb.trans hbb) (by nlinarith)
  exact le_of_tendsto (hlim₁.sub hlim₀).abs (Eventually.of_forall hsmooth)

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_RectangleMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangle Means for chordal SLE. -/

section
section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge

lemma dyadicCell_eq (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    dyadicCell k p = dyadicStripRectangle 0 k p.1 p.2 := by
  simp [dyadicCell, dyadicStripRectangle, cellOrigin, scaleLength, div_eq_mul_inv]
lemma cellOrigin_nonneg (k : ℕ) (i : Fin (2^k)) : 0 ≤ cellOrigin k i := by
  exact mul_nonneg (Nat.cast_nonneg _) (scaleLength_pos k).le
lemma cellOrigin_right (k : ℕ) (i : Fin (2^k)) : cellOrigin k i + scaleLength k ≤ 1 := by
  have hh : (i:ℝ)+1 ≤ (2:ℝ)^k := by exact_mod_cast i.isLt
  dsimp [cellOrigin, scaleLength]
  calc
    _ = ((i:ℝ)+1)/(2:ℝ)^k := by ring
    _ ≤ 1 := (div_le_one (by positivity)).2 hh
lemma dyadicInterior_subset_unit (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    dyadicInterior k p ⊆ openUnitStrip := by
  intro z hz
  have hr := cellOrigin_right k p.1
  have hi := mul_le_mul_of_nonneg_left (cellOrigin_right k p.2) Real.pi_pos.le
  have h0 := cellOrigin_nonneg k p.1
  have h0' := mul_nonneg Real.pi_pos.le (cellOrigin_nonneg k p.2)
  change _ < z.re ∧ z.re < _ ∧ _ < z.im ∧ z.im < _ at hz
  exact ⟨h0.trans_lt hz.1, hz.2.1.trans_le hr,
    h0'.trans_lt hz.2.2.1, by nlinarith [hz.2.2.2]⟩
lemma dyadicCell_subset_root (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    dyadicCell k p ⊆ stripRectangle 0 0 1 := by
  intro z hz
  have hr := cellOrigin_right k p.1
  have hi := mul_le_mul_of_nonneg_left (cellOrigin_right k p.2) Real.pi_pos.le
  have h0 := cellOrigin_nonneg k p.1
  have h0' := mul_nonneg Real.pi_pos.le (cellOrigin_nonneg k p.2)
  change _ ≤ z.re ∧ z.re ≤ _ ∧ _ ≤ z.im ∧ z.im ≤ _ at hz
  change 0 ≤ z.re ∧ z.re ≤ 0+1 ∧ 0 ≤ z.im ∧ z.im ≤ 0+Real.pi*1
  exact ⟨h0.trans hz.1, by linarith [hz.2.1],
    h0'.trans hz.2.2.1, by nlinarith [hz.2.2.2]⟩

lemma cellOrigin_separated {k : ℕ} {i j : Fin (2^k)} (hij : i < j) :
    cellOrigin k i + scaleLength k ≤ cellOrigin k j := by
  have hh : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hij
  have hm := mul_le_mul_of_nonneg_right hh (scaleLength_pos k).le
  dsimp [cellOrigin]
  nlinarith

lemma dyadicInterior_disjoint (k : ℕ) : Pairwise (fun p q => Disjoint (dyadicInterior k p) (dyadicInterior k q)) := by
  intro p q hpq
  rw [Set.disjoint_left]
  intro z hz hz'
  change _ < z.re ∧ z.re < _ ∧ _ < z.im ∧ z.im < _ at hz hz'
  by_cases h : p.1 = q.1
  · have hne : p.2 ≠ q.2 := by intro h'; exact hpq (Prod.ext h h')
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hh := mul_le_mul_of_nonneg_left (cellOrigin_separated hlt) Real.pi_pos.le
      nlinarith [hz.2.2.2, hz'.2.2.1]
    · have hh := mul_le_mul_of_nonneg_left (cellOrigin_separated hlt) Real.pi_pos.le
      nlinarith [hz'.2.2.2, hz.2.2.1]
  · rcases lt_or_gt_of_ne h with hlt | hlt
    · have hh := cellOrigin_separated hlt
      linarith [hz.2.1, hz'.1]
    · have hh := cellOrigin_separated hlt
      linarith [hz'.2.1, hz.1]

lemma cellOrigin_leftChild (k : ℕ) (i : Fin (2^k)) :
    cellOrigin (k+1) (leftChild k i) = cellOrigin k i := by
  simp only [cellOrigin, leftChild, Fin.val_mk, Nat.cast_mul, Nat.cast_ofNat, scaleLength_succ]
  ring
lemma cellOrigin_rightChild (k : ℕ) (i : Fin (2^k)) :
    cellOrigin (k+1) (rightChild k i) = cellOrigin k i + scaleLength k/2 := by
  simp only [cellOrigin, rightChild, Fin.val_mk, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, scaleLength_succ]
  ring

lemma branchIndex_step (x : ℝ) (k : ℕ) :
    cellOrigin k (branchIndex x k) ≤ cellOrigin (k+1) (branchIndex x (k+1)) ∧
    cellOrigin (k+1) (branchIndex x (k+1))+scaleLength k/2 ≤
      cellOrigin k (branchIndex x k)+scaleLength k := by
  rw [branchIndex]
  split
  · rw [cellOrigin_leftChild]
    constructor
    · rfl
    · linarith [scaleLength_pos k]
  · rw [cellOrigin_rightChild]
    constructor <;> linarith [scaleLength_pos k]

lemma branchIndex_contains {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    cellOrigin k (branchIndex x k) ≤ x ∧
    x ≤ cellOrigin k (branchIndex x k)+scaleLength k := by
  induction k with
  | zero => simpa [branchIndex, cellOrigin, scaleLength] using And.intro hx hx1
  | succ k ih =>
    rw [branchIndex]
    split_ifs with h
    · rw [cellOrigin_leftChild, scaleLength_succ]
      exact ⟨ih.1,h⟩
    · rw [cellOrigin_rightChild, scaleLength_succ]
      exact ⟨(not_le.mp h).le, by linarith [ih.2]⟩

lemma pointBranch_contains {z : ℂ} (hz : z ∈ stripRectangle 0 0 1) (k : ℕ) :
    z ∈ dyadicCell k (pointBranch z k) := by
  have hzr : 0 ≤ z.re ∧ z.re ≤ 1 := by simpa [stripRectangle] using And.intro hz.1 hz.2.1
  have hzi : 0 ≤ z.im/Real.pi ∧ z.im/Real.pi ≤ 1 := by
    refine ⟨div_nonneg hz.2.2.1 Real.pi_pos.le, (div_le_one Real.pi_pos).2 ?_⟩
    simpa using hz.2.2.2
  have hr := branchIndex_contains hzr.1 hzr.2 k
  have hi := branchIndex_contains hzi.1 hzi.2 k
  have hi₁ := mul_le_mul_of_nonneg_left hi.1 Real.pi_pos.le
  have hi₂ := mul_le_mul_of_nonneg_left hi.2 Real.pi_pos.le
  rw [mul_div_cancel₀ _ Real.pi_ne_zero] at hi₁ hi₂
  change _ ≤ z.re ∧ z.re ≤ _ ∧ Real.pi*cellOrigin k (branchIndex (z.im/Real.pi) k) ≤ z.im ∧
    z.im ≤ Real.pi*cellOrigin k (branchIndex (z.im/Real.pi) k)+Real.pi*scaleLength k
  exact ⟨hr.1, hr.2, hi₁, by nlinarith⟩

lemma stripRectangle_convex (a b l : ℝ) : Convex ℝ (stripRectangle a b l) := by
  have he : stripRectangle a b l =
      Complex.reCLM ⁻¹' Icc a (a+l) ∩ Complex.imCLM ⁻¹' Icc b (b+Real.pi*l) := by
    ext z
    simp only [stripRectangle, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Icc, Complex.reCLM_apply, Complex.imCLM_apply]
    tauto
  rw [he]
  exact ((convex_Icc a (a+l)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Icc b (b+Real.pi*l)).linear_preimage Complex.imCLM.toLinearMap)

lemma stripRectangle_compact (a b l : ℝ) : IsCompact (stripRectangle a b l) := by
  rw [stripRectangle_eq_preimage]
  change IsCompact (Complex.equivRealProdCLM.toHomeomorph ⁻¹' _)
  exact Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr
    (isCompact_Icc.prod isCompact_Icc)

lemma stripRectangle_nonempty (a b l : ℝ) (hl : 0 ≤ l) : (stripRectangle a b l).Nonempty := by
  refine ⟨⟨a,b⟩, ?_⟩
  change a ≤ a ∧ a ≤ a+l ∧ b ≤ b ∧ b ≤ b+Real.pi*l
  exact ⟨le_rfl,le_add_of_nonneg_right hl,le_rfl,
    le_add_of_nonneg_right (mul_nonneg Real.pi_pos.le hl)⟩

lemma spatialAverage_eq_setAverage (u : ℂ → ℝ) (Q : Set ℂ) :
    spatialAverage u Q = ⨍ z in Q, u z := by
  rw [spatialAverage, setAverage_eq, Measure.real]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

lemma stripRectangle_average_attained {u : ℂ → ℝ} {a b l : ℝ}
    (hu : ContinuousOn u (stripRectangle a b l)) (hl : 0 < l) :
    ∃ z ∈ stripRectangle a b l, u z = spatialAverage u (stripRectangle a b l) := by
  rw [spatialAverage_eq_setAverage]
  apply exists_eq_setAverage ((stripRectangle_convex a b l).isConnected
    (stripRectangle_nonempty a b l hl.le)) hu
    (hu.integrableOn_compact (stripRectangle_compact a b l))
    (stripRectangle_compact a b l).measure_lt_top.ne
  rw [stripRectangle_volume]
  exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hl)
    (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos Real.pi_pos hl))

lemma dyadicCell_dist_le {k : ℕ} {p : Fin (2^k) × Fin (2^k)} {z w : ℂ}
    (hz : z ∈ dyadicCell k p) (hw : w ∈ dyadicCell k p) :
    dist z w ≤ 5*scaleLength k := by
  change _ ≤ z.re ∧ z.re ≤ _ ∧ _ ≤ z.im ∧ z.im ≤ _ at hz
  change _ ≤ w.re ∧ w.re ≤ _ ∧ _ ≤ w.im ∧ w.im ≤ _ at hw
  have hre : |z.re-w.re| ≤ scaleLength k := by rw [abs_le]; constructor <;> linarith
  have him : |z.im-w.im| ≤ Real.pi*scaleLength k := by rw [abs_le]; constructor <;> linarith
  rw [dist_eq_norm]
  have hn := Complex.norm_le_abs_re_add_abs_im (z-w)
  simp only [Complex.sub_re, Complex.sub_im] at hn
  nlinarith [scaleLength_pos k, Real.pi_lt_four]

lemma scaleLength_tendsto : Tendsto scaleLength atTop (𝓝 0) := by
  have hh := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 < 1)
  change Tendsto (fun n => 1/(2:ℝ)^n) atTop (𝓝 0)
  simpa only [div_pow, one_pow] using hh

lemma branch_means_tendsto {u : ℂ → ℝ} (hu : ContinuousOn u (stripRectangle 0 0 1))
    {z : ℂ} (hz : z ∈ stripRectangle 0 0 1) :
    Tendsto (fun k => spatialAverage u (dyadicCell k (pointBranch z k))) atTop (𝓝 (u z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, huδ⟩ := (Metric.continuousWithinAt_iff.1 (hu z hz)) ε hε
  have hs : ∀ᶠ k in atTop, 5*scaleLength k < δ :=
    ((scaleLength_tendsto.const_mul 5).eventually (eventually_lt_nhds (by simpa using hδ)))
  obtain ⟨N,hN⟩ := eventually_atTop.1 hs
  refine ⟨N,fun k hk => ?_⟩
  obtain ⟨w,hw,hew⟩ := stripRectangle_average_attained
    (hu.mono (dyadicCell_subset_root k (pointBranch z k))) (scaleLength_pos k)
  change u w = spatialAverage u (dyadicCell k (pointBranch z k)) at hew
  rw [← hew]
  apply huδ (dyadicCell_subset_root k (pointBranch z k) hw)
  exact (dyadicCell_dist_le hw (pointBranch_contains hz k)).trans_lt (hN k hk)

lemma cellEnergy_nonneg (D : ℂ → ℂ) (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    0 ≤ cellEnergy D k p := integral_nonneg (fun _ => sq_nonneg _)

lemma branch_mean_step_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) (z : ℂ) (k : ℕ) :
    |spatialAverage u (dyadicCell (k+1) (pointBranch z (k+1))) -
      spatialAverage u (dyadicCell k (pointBranch z k))| ≤
      12*Real.sqrt (cellEnergy D k (pointBranch z k)) := by
  have hs₁ := branchIndex_step z.re k
  have hs₂ := branchIndex_step (z.im/Real.pi) k
  have hh := local_means_le hu
    (cellOrigin k (branchIndex z.re k)) (Real.pi*cellOrigin k (branchIndex (z.im/Real.pi) k))
    (scaleLength k) (scaleLength_pos k)
    (cellOrigin_nonneg ..) (cellOrigin_right ..)
    (mul_nonneg Real.pi_pos.le (cellOrigin_nonneg ..))
    (by nlinarith [cellOrigin_right k (branchIndex (z.im/Real.pi) k), Real.pi_pos])
    (cellOrigin (k+1) (branchIndex z.re (k+1)))
    (Real.pi*cellOrigin (k+1) (branchIndex (z.im/Real.pi) (k+1)))
    hs₁.1 hs₁.2 (mul_le_mul_of_nonneg_left hs₂.1 Real.pi_pos.le)
    (by have := mul_le_mul_of_nonneg_left hs₂.2 Real.pi_pos.le; nlinarith)
  simpa only [dyadicCell, pointBranch, cellEnergy, dyadicInterior, scaleLength_succ] using hh

lemma sum_cellEnergy_le {D : ℂ → ℂ} (hD : MemLp D 2 (volume.restrict openUnitStrip)) (k : ℕ) :
    ∑ p : Fin (2^k) × Fin (2^k), cellEnergy D k p ≤ stripDirichletEnergy D := by
  have hs : (⋃ p : Fin (2^k) × Fin (2^k), dyadicInterior k p) ⊆ openUnitStrip :=
    iUnion_subset (fun p => dyadicInterior_subset_unit k p)
  have hi : IntegrableOn (fun z => ‖D z‖^2) openUnitStrip volume := hD.norm.integrable_sq
  have he := integral_iUnion
    (fun p : Fin (2^k) × Fin (2^k) => openStripRectangle_measurable _ _ _)
    (dyadicInterior_disjoint k) (hi.mono_set hs)
  rw [tsum_fintype] at he
  change (∫ z in ⋃ p : Fin (2^k) × Fin (2^k), dyadicInterior k p, ‖D z‖^2) =
    ∑ p : Fin (2^k) × Fin (2^k), ∫ z in dyadicInterior k p, ‖D z‖^2 at he
  change (∑ p : Fin (2^k) × Fin (2^k), ∫ z in dyadicInterior k p, ‖D z‖^2) ≤ _
  rw [← he]
  exact setIntegral_mono_set hi (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (fun z hz => hs hz))

lemma exists_large_increment {a : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (ha : Tendsto a atTop (𝓝 H)) (ha0 : a 0 ≤ 3*H/4) :
    ∃ j : ℕ, H/(8*((j:ℝ)+1)*((j:ℝ)+2)) < |a (j+1)-a j| := by
  by_contra! hn
  have hpartial (n : ℕ) : a n ≤ a 0 + H/8*(1-1/((n:ℝ)+1)) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hstep := (le_abs_self (a (n+1)-a n)).trans (hn n)
      have htel : H/8*(1-1/((n:ℝ)+1)) + H/(8*((n:ℝ)+1)*((n:ℝ)+2)) =
          H/8*(1-1/(((n+1:ℕ):ℝ)+1)) := by
        push_cast
        field_simp
        ring
      linarith
  have hb (n : ℕ) : a n ≤ a 0+H/8 := by
    have hp : 0 ≤ H/8*(1/((n:ℝ)+1)) := by positivity
    have hh := hpartial n
    nlinarith
  have hh := le_of_tendsto ha (Eventually.of_forall hb)
  linarith

lemma large_increment_energy {H e : ℝ} (hH : 0 < H) (he : 0 ≤ e) (j : ℕ)
    (h : H/(8*((j:ℝ)+1)*((j:ℝ)+2)) ≤ 12*Real.sqrt e) :
    H^2/(9216*((j:ℝ)+2)^4) ≤ e := by
  have hd : 0 < 8*((j:ℝ)+1)*((j:ℝ)+2) := by positivity
  have hh := (div_le_iff₀ hd).1 h
  have hj : ((j:ℝ)+1)*((j:ℝ)+2) ≤ ((j:ℝ)+2)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hm := mul_le_mul_of_nonneg_right hj (show 0 ≤ 96*Real.sqrt e by positivity)
  have hlinear : H ≤ 96*((j:ℝ)+2)^2*Real.sqrt e := by nlinarith
  have hsq := (sq_le_sq₀ hH.le (by positivity)).2 hlinear
  rw [mul_pow, mul_pow, Real.sq_sqrt he] at hsq
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [show (((j:ℝ)+2)^2)^2 = ((j:ℝ)+2)^4 by ring]

lemma mem_exceptionalParents (D : ℂ → ℂ) (H : ℝ) (N j : ℕ)
    (p : Fin (2^(N+j)) × Fin (2^(N+j))) :
    p ∈ exceptionalParents D H N j ↔ H^2/(9216*((j:ℝ)+2)^4) ≤ cellEnergy D (N+j) p := by
  classical
  simp [exceptionalParents]

lemma exceptional_cover {u : ℂ → ℝ} {D : ℂ → ℂ} {H : ℝ} (hH : 0 < H)
    (hu : SourceIsStripWeakGradient u D) (hc : ContinuousOn u (stripRectangle 0 0 1))
    (N : ℕ) (hN : ∀ p, spatialAverage u (dyadicCell N p) ≤ 3*H/4) :
    {z | z ∈ stripRectangle 0 0 1 ∧ u z = H} ⊆
      ⋃ j : ℕ, ⋃ p ∈ exceptionalParents D H N j, dyadicCell (N+j) p := by
  intro z hz
  have ht : Tendsto (fun j => spatialAverage u (dyadicCell (N+j) (pointBranch z (N+j))))
      atTop (𝓝 H) := by
    simpa only [Function.comp_def, Nat.add_comm, hz.2] using
      (branch_means_tendsto hc hz.1).comp (tendsto_add_atTop_nat N)
  obtain ⟨j,hj⟩ := exists_large_increment hH ht (by simpa using hN (pointBranch z N))
  have hstep := branch_mean_step_le hu z (N+j)
  have he : H^2/(9216*((j:ℝ)+2)^4) ≤ cellEnergy D (N+j) (pointBranch z (N+j)) := by
    apply large_increment_energy hH (cellEnergy_nonneg ..) j
    have hnj : N+(j+1) = N+j+1 := by omega
    rw [hnj] at hj
    exact hj.le.trans hstep
  exact mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨pointBranch z (N+j), mem_iUnion.2
    ⟨(mem_exceptionalParents ..).2 he, pointBranch_contains hz.1 (N+j)⟩⟩⟩

lemma exceptional_count {D : ℂ → ℂ} (hD : MemLp D 2 (volume.restrict openUnitStrip))
    {H : ℝ} (hH : 0 < H) (N j : ℕ) :
    ((exceptionalParents D H N j).card : ℝ) ≤
      9216*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4 := by
  classical
  have hl := Finset.card_nsmul_le_sum (exceptionalParents D H N j)
    (cellEnergy D (N+j)) (H^2/(9216*((j:ℝ)+2)^4))
    (fun p hp => (mem_exceptionalParents ..).1 hp)
  simp only [nsmul_eq_mul] at hl
  have hs : ∑ p ∈ exceptionalParents D H N j, cellEnergy D (N+j) p ≤
      stripDirichletEnergy D := by
    apply le_trans _ (sum_cellEnergy_le hD (N+j))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun p _ _ => cellEnergy_nonneg ..)
  have hd : 0 < 9216*((j:ℝ)+2)^4 := by positivity
  have hh : ((exceptionalParents D H N j).card : ℝ)*H^2 ≤
      stripDirichletEnergy D*(9216*((j:ℝ)+2)^4) := by
    apply (div_le_iff₀ hd).1
    simpa only [mul_div_assoc] using hl.trans hs
  calc
    ((exceptionalParents D H N j).card : ℝ) ≤
        (stripDirichletEnergy D*(9216*((j:ℝ)+2)^4))/H^2 :=
      (le_div_iff₀ (sq_pos_of_pos hH)).2 hh
    _ = 9216*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4 := by ring

lemma summable_polyGeometric {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Summable (fun j : ℕ => ((j:ℝ)+2)^4*q^j) := by
  have hs₀ : Summable (fun n : ℕ => (n:ℝ)^4*q^n) :=
    summable_pow_mul_geometric_of_norm_lt_one 4 (by simpa [Real.norm_eq_abs, abs_of_pos hq] using hq1)
  have hs : Summable (fun n : ℕ => ((n+2:ℕ):ℝ)^4*q^(n+2)) :=
    (summable_nat_add_iff 2).2 hs₀
  apply (hs.mul_right (q^2)⁻¹).congr
  intro j
  push_cast
  rw [pow_add]
  field_simp

lemma polyGeometricSum_pos {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : 0 < polyGeometricSum q := by
  have hh := (summable_polyGeometric hq hq1).le_tsum 0
    (fun j _ => by positivity : ∀ j : ℕ, j ≠ 0 → 0 ≤ ((j:ℝ)+2)^4*q^j)
  norm_num at hh
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 16) hh

lemma decay_factor (α : ℝ) (N j : ℕ) :
    (2:ℝ)^(-α*((N+j:ℕ):ℝ)) = ((2:ℝ)^(-α))^N * ((2:ℝ)^(-α))^j := by
  push_cast
  rw [mul_add, Real.rpow_add (by norm_num), Real.rpow_mul_natCast (by norm_num),
    Real.rpow_mul_natCast (by norm_num)]

lemma summable_weighted_decay (α : ℝ) (hα : 0 < α) (N : ℕ) (A : ℝ) :
    Summable (fun j : ℕ => A*((j:ℝ)+2)^4*(2:ℝ)^(-α*((N+j:ℕ):ℝ))) := by
  have hq : 0 < (2:ℝ)^(-α) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (2:ℝ)^(-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  apply ((summable_polyGeometric hq hq1).mul_left (A*((2:ℝ)^(-α))^N)).congr
  intro j
  rw [decay_factor]
  ring

lemma tsum_weighted_decay (α : ℝ) (_hα : 0 < α) (N : ℕ) (A : ℝ) :
    (∑' j : ℕ, A*((j:ℝ)+2)^4*(2:ℝ)^(-α*((N+j:ℕ):ℝ))) =
      A*polyGeometricSum ((2:ℝ)^(-α))*((2:ℝ)^(-α))^N := by
  simp_rw [decay_factor]
  have he : (fun j : ℕ => A*((j:ℝ)+2)^4*(((2:ℝ)^(-α))^N*((2:ℝ)^(-α))^j)) =
      (fun j : ℕ => (A*((2:ℝ)^(-α))^N)*(((j:ℝ)+2)^4*((2:ℝ)^(-α))^j)) := by
    ext j
    ring
  rw [he, tsum_mul_left]
  dsimp [polyGeometricSum]
  ring

lemma finite_union_hit_bound {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : I → Set ℂ) (X : Ω → Set ℂ) (S : Finset I) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ p ∈ S, P {ξ | (X ξ ∩ Q p).Nonempty} ≤ ENNReal.ofReal B) :
    P (⋃ p ∈ S, {ξ | (X ξ ∩ Q p).Nonempty}) ≤ ENNReal.ofReal ((S.card:ℝ)*B) := by
  calc
    _ ≤ ∑ p ∈ S, P {ξ | (X ξ ∩ Q p).Nonempty} := measure_biUnion_finset_le S _
    _ ≤ ∑ p ∈ S, ENNReal.ofReal B := Finset.sum_le_sum h
    _ = ENNReal.ofReal ((S.card:ℝ)*B) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hB)]
      simp

lemma rectangle_bound_at_depth {u : ℂ → ℝ} {D : ℂ → ℂ} {H C0 α : ℝ}
    (hH : 0 < H) (hC0 : 0 < C0) (hα : 0 < α)
    (hu : SourceIsStripWeakGradient u D) (hc : ContinuousOn u (stripRectangle 0 0 1))
    (N : ℕ) (hN : ∀ p, spatialAverage u (dyadicCell N p) ≤ 3*H/4)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Set ℂ)
    (hhit : ∀ (k : ℕ) (p : Fin (2^k) × Fin (2^k)),
      P {ξ | (X ξ ∩ dyadicCell k p).Nonempty} ≤ ENNReal.ofReal (C0*(2:ℝ)^(-α*(k:ℝ)))) :
    P {ξ | (X ξ ∩ {z | z ∈ stripRectangle 0 0 1 ∧ u z = H}).Nonempty} ≤
      ENNReal.ofReal (9216*C0*(stripDirichletEnergy D/H^2)*
        polyGeometricSum ((2:ℝ)^(-α))*((2:ℝ)^(-α))^N) := by
  have hE : 0 ≤ stripDirichletEnergy D := integral_nonneg (fun _ => sq_nonneg _)
  have hsub : {ξ | (X ξ ∩ {z | z ∈ stripRectangle 0 0 1 ∧ u z = H}).Nonempty} ⊆
      ⋃ j : ℕ, ⋃ p ∈ exceptionalParents D H N j, {ξ | (X ξ ∩ dyadicCell (N+j) p).Nonempty} := by
    intro ξ hξ
    obtain ⟨z, hzX, hz⟩ := hξ
    have hz' := exceptional_cover hH hu hc N hN hz
    simp only [mem_iUnion] at hz' ⊢
    obtain ⟨j,p,hp,hzp⟩ := hz'
    exact ⟨j,p,hp, z,hzX,hzp⟩
  have hlevel (j : ℕ) :
      P (⋃ p ∈ exceptionalParents D H N j, {ξ | (X ξ ∩ dyadicCell (N+j) p).Nonempty}) ≤
      ENNReal.ofReal (9216*C0*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4*
        (2:ℝ)^(-α*((N+j:ℕ):ℝ))) := by
    apply (finite_union_hit_bound P (dyadicCell (N+j)) X (exceptionalParents D H N j)
      (by positivity) (fun p _ => hhit (N+j) p)).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_right (exceptional_count hu.2.1 hH N j)
      (show 0 ≤ C0*(2:ℝ)^(-α*((N+j:ℕ):ℝ)) by positivity)
    calc
      _ ≤ (9216*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4)*
          (C0*(2:ℝ)^(-α*((N+j:ℕ):ℝ))) := hh
      _ = _ := by ring
  calc
    _ ≤ P (⋃ j : ℕ, ⋃ p ∈ exceptionalParents D H N j,
        {ξ | (X ξ ∩ dyadicCell (N+j) p).Nonempty}) := measure_mono hsub
    _ ≤ ∑' j : ℕ, P (⋃ p ∈ exceptionalParents D H N j,
        {ξ | (X ξ ∩ dyadicCell (N+j) p).Nonempty}) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (9216*C0*(stripDirichletEnergy D/H^2)*((j:ℝ)+2)^4*
        (2:ℝ)^(-α*((N+j:ℕ):ℝ))) := ENNReal.tsum_le_tsum hlevel
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
        (summable_weighted_decay α hα N (9216*C0*(stripDirichletEnergy D/H^2))),
        tsum_weighted_decay α hα N]

lemma energyDepth_mean_bound {H E : ℝ} (hH : 0 < H) (hE : 0 < E)
    (hsmall : E ≤ H^2/51200) :
    20*Real.sqrt ((((energyDepth H E:ℕ):ℝ)+1)*E) ≤ H/4 := by
  have hf : ((energyDepth H E:ℕ):ℝ) ≤ H^2/(25600*E) := Nat.floor_le (by positivity)
  have hm := (le_div_iff₀ (show 0 < 25600*E by positivity)).1 hf
  have hn : 0 ≤ (((energyDepth H E:ℕ):ℝ)+1)*E := by positivity
  change 20*Real.sqrt ((((energyDepth H E:ℕ):ℝ)+1)*E) ≤ H/4
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, Real.sq_sqrt hn, div_pow]
  norm_num
  nlinarith [sq_nonneg H]

lemma energyDepth_lower {H E : ℝ} (_hH : 0 < H) (hE : 0 < E)
    (hsmall : E ≤ H^2/51200) :
    H^2/(51200*E) ≤ ((energyDepth H E:ℕ):ℝ) := by
  have hf : H^2/(25600*E) < ((energyDepth H E:ℕ):ℝ)+1 := Nat.lt_floor_add_one _
  have hx : 2 ≤ H^2/(25600*E) := by
    apply (le_div_iff₀ (by positivity)).2
    linarith
  have he : H^2/(51200*E) = (H^2/(25600*E))/2 := by ring
  rw [he]
  linarith

lemma energyDepth_decay {H E α : ℝ} (hH : 0 < H) (hE : 0 < E) (hα : 0 < α)
    (hsmall : E ≤ H^2/51200) :
    ((2:ℝ)^(-α))^(energyDepth H E) ≤ Real.exp (-(α*Real.log 2/51200)*H^2/E) := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2), Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  have hn := energyDepth_lower hH hE hsmall
  have hh := mul_le_mul_of_nonneg_left hn (show 0 ≤ α*Real.log 2 by positivity)
  calc
    Real.log 2 * (-α*((energyDepth H E:ℕ):ℝ)) = -(α*Real.log 2*((energyDepth H E:ℕ):ℝ)) := by ring
    _ ≤ -(α*Real.log 2*(H^2/(51200*E))) := neg_le_neg hh
    _ = _ := by ring

universe u



lemma critical_cell_means_le {u : ℂ → ℝ} {D : ℂ → ℂ}
    (hu : SourceIsStripWeakGradient u D) (k : ℕ) (p : Fin (2^k) × Fin (2^k)) :
    |spatialAverage u (dyadicCell k p) - spatialAverage u (stripRectangle 0 0 1)| ≤
      20*Real.sqrt (((k:ℝ)+1)*stripDirichletEnergy D) := by
  rw [dyadicCell_eq]
  by_cases hk : k = 0
  · subst k
    have hi : p.1 = 0 := by apply Fin.ext; have := p.1.isLt; norm_num at this ⊢
    have hm : p.2 = 0 := by apply Fin.ext; have := p.2.isLt; norm_num at this ⊢
    simp [hi, hm, dyadicStripRectangle]
  · obtain ⟨t, ht, ht1, hit⟩ := dyadic_position_param k hk p.1
    obtain ⟨s, hs, hs1, hms⟩ := dyadic_position_param k hk p.2
    have hh := chain_means_le hu ht ht1 hs hs1 k
    simpa only [dyadicStripRectangle, Int.cast_zero, zero_add, hit, hms, scaleLength] using hh

lemma high_set_empty_of_energy_zero {u : ℂ → ℝ} {D : ℂ → ℂ} {H : ℝ}
    (hH : 0 < H) (hu : SourceIsStripWeakGradient u D)
    (hc : ContinuousOn u (stripRectangle 0 0 1))
    (hmean : spatialAverage u (stripRectangle 0 0 1) ≤ H/2)
    (hzero : stripDirichletEnergy D = 0) :
    {z | z ∈ stripRectangle 0 0 1 ∧ u z = H} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hb (k : ℕ) : spatialAverage u (dyadicCell k (pointBranch z k)) ≤ H/2 := by
    have hh := critical_cell_means_le hu k (pointBranch z k)
    rw [hzero, mul_zero, Real.sqrt_zero, mul_zero] at hh
    have hh' := (le_abs_self _).trans hh
    linarith
  have hh := le_of_tendsto (branch_means_tendsto hc hz.1) (Eventually.of_forall hb)
  rw [hz.2] at hh
  linarith

theorem sourceStripRectangleEnergy : SourceStripRectangleEnergyTarget := by
  intro C0 α hC0 hα
  have hq : 0 < (2:ℝ)^(-α) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (2:ℝ)^(-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨9216*C0*polyGeometricSum ((2:ℝ)^(-α)), α*Real.log 2/51200, 1/51200,
    by positivity [polyGeometricSum_pos hq hq1], by positivity, by norm_num, ?_⟩
  intro H hH u D hu hc _hrange hmean Ω mΩ P _hP X hhit hsmall
  have hE : 0 ≤ stripDirichletEnergy D := integral_nonneg (fun _ => sq_nonneg _)
  have hsmall' : stripDirichletEnergy D ≤ H^2/51200 := by linarith
  by_cases hz : stripDirichletEnergy D = 0
  · rw [high_set_empty_of_energy_zero hH hu hc hmean hz]
    simp [hz]
  · have hEpos : 0 < stripDirichletEnergy D := lt_of_le_of_ne hE (Ne.symm hz)
    let N := energyDepth H (stripDirichletEnergy D)
    have hN : ∀ p, spatialAverage u (dyadicCell N p) ≤ 3*H/4 := by
      intro p
      have hh := critical_cell_means_le hu N p
      have hs := energyDepth_mean_bound hH hEpos hsmall'
      change 20*Real.sqrt (((N:ℝ)+1)*stripDirichletEnergy D) ≤ H/4 at hs
      have hh' := (le_abs_self _).trans (hh.trans hs)
      linarith
    have hh := rectangle_bound_at_depth hH hC0 hα hu hc N hN P X
      (fun k p => by simpa only [dyadicCell_eq] using hhit k p.1 p.2)
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    have hl := mul_le_mul_of_nonneg_left (energyDepth_decay hH hEpos hα hsmall')
      (show 0 ≤ 9216*C0*(stripDirichletEnergy D/H^2)*polyGeometricSum ((2:ℝ)^(-α)) by
        exact mul_nonneg (by positivity) (polyGeometricSum_pos hq hq1).le)
    calc
      _ ≤ (9216*C0*(stripDirichletEnergy D/H^2)*polyGeometricSum ((2:ℝ)^(-α)))*
          Real.exp (-(α*Real.log 2/51200)*H^2/stripDirichletEnergy D) := hl
      _ = _ := by ring

lemma source_local_lipschitz_weak_derivative {D : Set ℂ} (hD : IsOpen D) {u : ℂ → ℝ}
    (hlocal : ∀ x ∈ D, ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ x ∈ U ∧ LipschitzOnWith K u U)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ D) (v : ℂ) :
    (∫ z in D, u z * (fderiv ℝ φ z) v) =
      -(∫ z in D, (fderiv ℝ u z) v * φ z) := by
  obtain ⟨S,hSc,hφS,hSD⟩ := exists_compact_between hcφ hD hsφ
  have huS : LocallyLipschitzOn S u := by
    intro x hx
    obtain ⟨K,U,hUo,hxU,hU⟩ := hlocal x (hSD hx)
    exact ⟨K,U,mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hxU),hU⟩
  obtain ⟨K,hK⟩ := huS.exists_lipschitzOnWith_of_compact hSc
  obtain ⟨g,hglip,hug⟩ := hK.extend_real
  obtain ⟨C,hφlip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ hφ (by simp)
  have hφdiff : ∀ z, DifferentiableAt ℝ φ z := fun z => (hφ.differentiable (by simp)).differentiableAt
  have ht (z : ℂ) (hz : z ∈ tsupport φ) : u =ᶠ[𝓝 z] g := by
    filter_upwards [mem_interior_iff_mem_nhds.mp (hφS hz)] with w hw
    exact hug hw
  have hid := hglip.integral_lineDeriv_mul_eq (μ := volume) hφlip hcφ v
  have hfull : (∫ z, (fderiv ℝ g z) v * φ z) = -(∫ z, g z * (fderiv ℝ φ z) v) := by
    calc
      _ = ∫ z, lineDeriv ℝ g z v * φ z := by
        apply integral_congr_ae
        filter_upwards [hglip.ae_differentiableAt (μ := volume)] with z hz
        rw [hz.lineDeriv_eq_fderiv]
      _ = ∫ z, lineDeriv ℝ φ z (-v) * g z := hid
      _ = _ := by
        simp_rw [(hφdiff _).lineDeriv_eq_fderiv,map_neg,neg_mul,mul_comm _ (g _)]
        rw [integral_neg]
  have he1 : (fun z => u z * (fderiv ℝ φ z) v) = (fun z => g z * (fderiv ℝ φ z) v) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [hug (interior_subset (hφS hz))]
    · simp [fderiv_of_notMem_tsupport ℝ hz]
  have he2 : (fun z => (fderiv ℝ u z) v * φ z) = (fun z => (fderiv ℝ g z) v * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [(ht z hz).fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hs1 : (∫ z in D, u z * (fderiv ℝ φ z) v) = ∫ z, u z * (fderiv ℝ φ z) v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport φ := fun h => hz (hsφ h)
    simp [fderiv_of_notMem_tsupport ℝ hn]
  have hs2 : (∫ z in D, (fderiv ℝ u z) v * φ z) = ∫ z, (fderiv ℝ u z) v * φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport φ := fun h => hz (hsφ h)
    simp [image_eq_zero_of_notMem_tsupport hn]
  rw [hs1,hs2,he1,he2,hfull]
  simp

lemma real_gradient_re (u : ℂ → ℝ) (z : ℂ) : (gradient u z).re = (fderiv ℝ u z) (1:ℂ) := by
  have hh := inner_gradient_left (f := u) (x := z) (y := (1:ℂ))
  rw [Complex.inner] at hh
  simpa using hh

lemma real_gradient_im (u : ℂ → ℝ) (z : ℂ) : (gradient u z).im = (fderiv ℝ u z) Complex.I := by
  have hh := inner_gradient_left (f := u) (x := z) (y := Complex.I)
  rw [Complex.inner] at hh
  simpa using hh

lemma locallyLipschitz_source_weakGradient {u : ℂ → ℝ}
    (hl : LocallyLipschitzOn openUnitStrip u)
    (hu : MemLp u 2 (volume.restrict openUnitStrip))
    (hg : MemLp (gradient u) 2 (volume.restrict openUnitStrip)) :
    SourceIsStripWeakGradient u (gradient u) := by
  refine ⟨hu,hg,?_⟩
  have hlocal (z : ℂ) (hz : z ∈ openUnitStrip) :
      ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ z ∈ U ∧ LipschitzOnWith K u U := by
    obtain ⟨K,t,ht,htl⟩ := hl hz
    rw [nhdsWithin_eq_nhds.mpr (openUnitStrip_isOpen.mem_nhds hz)] at ht
    obtain ⟨U,hUt,hUo,hzU⟩ := _root_.mem_nhds_iff.mp ht
    exact ⟨K,U,hUo,hzU,htl.mono hUt⟩
  intro φ hφ hc hs
  constructor
  · simpa only [real_gradient_re] using
      source_local_lipschitz_weak_derivative openUnitStrip_isOpen hlocal φ hφ hc hs 1
  · simpa only [real_gradient_im] using
      source_local_lipschitz_weak_derivative openUnitStrip_isOpen hlocal φ hφ hc hs Complex.I

 

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

lemma spatialSmallnessConstant_gt_one : 1 < spatialSmallnessConstant := by
  dsimp [spatialSmallnessConstant]
  have := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 128) Real.pi_pos) (Real.exp_pos 1)
  linarith

lemma spatial_smallness (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hy : spatialSmallnessConstant * r < z.im) :
    0 < z.im ∧ r ≤ z.im ∧ 1 ≤ Real.log ((2 * z.im) / ((128 * Real.pi) * r)) := by
  have hA : 1 ≤ spatialSmallnessConstant := spatialSmallnessConstant_gt_one.le
  have hry : r < z.im := (le_mul_of_one_le_left hr.le hA).trans_lt hy
  refine ⟨hr.trans hry, hry.le, ?_⟩
  have hC : 0 < (128 * Real.pi) * r := mul_pos (mul_pos (by norm_num) Real.pi_pos) hr
  have hquot : 0 < (2 * z.im) / ((128 * Real.pi) * r) :=
    div_pos (mul_pos (by norm_num) (hr.trans hry)) hC
  apply (Real.le_log_iff_exp_le hquot).mpr
  apply (le_div_iff₀ hC).mpr
  dsimp [spatialSmallnessConstant] at hy
  nlinarith [Real.exp_pos 1]

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

lemma spatialOnePointConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < spatialOnePointConstant κ :=
  mul_pos (uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num))
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) Real.pi_pos) _)

lemma sausagePointConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < sausagePointConstant κ :=
  (mul_pos (spatialOnePointConstant_pos κ hκ hκ8) (Real.rpow_pos_of_pos (by norm_num) _)).trans_le
    (le_max_left _ _)

lemma negative_power_scale (x r A p : ℝ) (hx : 0 < x) (hr : 0 < r)
    (hA : 0 < A) (hp : 0 ≤ p) (hxr : x ≤ A * r) :
    r ^ (-p) ≤ A ^ p * x ^ (-p) := by
  have hh := Real.rpow_le_rpow hx.le hxr hp
  rw [Real.mul_rpow hA.le hr.le] at hh
  rw [Real.rpow_neg hr.le, Real.rpow_neg hx.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hx p)).mpr
  exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hr p)).mpr (by simpa [mul_comm] using hh)

 

theorem normalized_visit_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z.im ≠ 0) (r : ℝ) (hr : 0 < r) :
    r ^ (-codimension κ) * (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      sausagePointConstant κ * |z.im| ^ (-codimension κ) := by
  have hp := codimension_pos κ hκ8
  have hA : 0 < spatialSmallnessConstant := zero_lt_one.trans spatialSmallnessConstant_gt_one
  have hscale (hy : |z.im| ≤ spatialSmallnessConstant * r) :
      r ^ (-codimension κ) * (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
        sausagePointConstant κ * |z.im| ^ (-codimension κ) := by
    calc
      _ ≤ r ^ (-codimension κ) * 1 := mul_le_mul_of_nonneg_left measureReal_le_one
        (Real.rpow_nonneg hr.le _)
      _ ≤ spatialSmallnessConstant ^ codimension κ * |z.im| ^ (-codimension κ) := by
        rw [mul_one]
        exact negative_power_scale _ _ _ _ (abs_pos.mpr hz) hr hA hp.le hy
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (abs_nonneg _) _)
  by_cases hsmall : spatialSmallnessConstant * r < z.im
  · obtain ⟨hy, hry, hlog⟩ := spatial_smallness z r hr hsmall
    have hh := euclidean_approach hB κ hκ hκ8 γ G F hw z hy r hr hry hlog
    have hS := (spatialOnePointConstant_pos κ hκ hκ8).le
    change (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      spatialOnePointConstant κ * initialGreen κ z * r ^ codimension κ at hh
    have hcancel : r ^ (-codimension κ) * r ^ codimension κ = 1 := by
      rw [← Real.rpow_add hr]; simp
    calc
      _ ≤ r ^ (-codimension κ) * (spatialOnePointConstant κ * initialGreen κ z * r ^ codimension κ) :=
        mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hr.le _)
      _ = spatialOnePointConstant κ * initialGreen κ z := by
        calc
          _ = (spatialOnePointConstant κ * initialGreen κ z) *
              (r ^ (-codimension κ) * r ^ codimension κ) := by ring
          _ = _ := by rw [hcancel, mul_one]
      _ ≤ spatialOnePointConstant κ * ((2 : ℝ) ^ (-codimension κ) * z.im ^ (-codimension κ)) :=
        mul_le_mul_of_nonneg_left (initialGreen_le_height κ hκ hκ8 z hy) hS
      _ ≤ _ := by
        rw [abs_of_pos hy, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.le _)
  · by_cases hy : 0 ≤ z.im
    · apply hscale
      rw [abs_of_nonneg hy]
      exact le_of_not_gt hsmall
    · by_cases hzr : -r < z.im
      · apply hscale
        rw [abs_of_neg (lt_of_not_ge hy)]
        exact (by linarith : -z.im ≤ r).trans (le_mul_of_one_le_left hr.le spatialSmallnessConstant_gt_one.le)
      · have hzero : P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r} = 0 := by
          have hn : ∀ᵐ ω ∂P, ¬ (∃ t : ℝ≥0, dist (γ ω t) z < r) := by
            filter_upwards [hw] with ω hω
            rintro ⟨t, ht⟩
            have hi := Complex.im_le_norm (γ ω t - z)
            rw [Complex.sub_im, ← dist_eq_norm] at hi
            have hnon := hω.2.2.1 t
            linarith [le_of_not_gt hzr]
          simpa only [not_not, ofPred_mem_eq] using ae_iff.mp hn
        rw [hzero, ENNReal.toReal_zero, mul_zero]
        exact mul_nonneg (sausagePointConstant_pos κ hκ hκ8).le (Real.rpow_nonneg (abs_nonneg _) _)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsOrdinaryChordalSLE.exists_charts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (hSLE : IsOrdinaryChordalSLE κ γ P) :
    ∃ (B : ℝ≥0 → Ω → ℝ) (G F : Ω → ℝ≥0 → ℂ → ℂ),
      IsBrownianReal B P ∧ ∀ᵐ ω ∂P, IsCapacityTwoWitness
        (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω) := by
  classical
  obtain ⟨B,hB,htrace⟩ := hSLE.2
  have hchoice (ω : Ω) : ∃ G F : ℝ≥0 → ℂ → ℂ,
      IsCapacityTwoTrace (fun t => Real.sqrt κ*B t ω) (γ ω) →
        IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) G F := by
    by_cases h : IsCapacityTwoTrace (fun t => Real.sqrt κ*B t ω) (γ ω)
    · obtain ⟨G,F,hw⟩ := h
      exact ⟨G,F,fun _ => hw⟩
    · exact ⟨fun _ _ => 0,fun _ _ => 0,fun hh => False.elim (h hh)⟩
  choose G F hw using hchoice
  exact ⟨B,G,F,hB,htrace.mono fun ω hω => hw ω hω⟩



end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma annularApproachPower_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < annularApproachPower κ := by
  have hp := codimension_pos κ hκ8
  unfold annularApproachPower boundaryApproachPower
  exact lt_min (by positivity) (by positivity)

lemma annularApproachConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < annularApproachConstant κ := by
  have hh := sausagePointConstant_pos κ hκ hκ8
  unfold annularApproachConstant
  exact add_pos (Real.rpow_pos_of_pos (by positivity) _) hh



end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma sle_high_center_approach_scaled
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (z : ℂ) (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hy : R*Real.sqrt r ≤ z.im) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < R*r}).toReal ≤
      sausagePointConstant κ * r^(codimension κ/2) := by
  obtain ⟨B,G,F,hB,hw⟩ := hSLE.exists_charts
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hp := codimension_pos κ hκ8
  have hs := Real.sqrt_pos.mpr hr
  have hz : 0 < z.im := (mul_pos hR hs).trans_le hy
  have hb := normalized_visit_bound hB κ hκ hκ8 γ G F hw z hz.ne' (R*r) (mul_pos hR hr)
  have hb' := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (mul_nonneg hR.le hr.le) (codimension κ))
  rw [← mul_assoc,← Real.rpow_add (mul_pos hR hr),add_neg_cancel,Real.rpow_zero,one_mul,abs_of_pos hz] at hb'
  have hpow : z.im^(-codimension κ) ≤ (R*Real.sqrt r)^(-codimension κ) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hR hs) hy (neg_nonpos.mpr hp.le)
  have hid : (R*r)^codimension κ * (R*Real.sqrt r)^(-codimension κ) = r^(codimension κ/2) := by
    rw [Real.mul_rpow hR.le hr.le,Real.mul_rpow hR.le hs.le]
    calc
      _ = (R^codimension κ*R^(-codimension κ)) *
          (r^codimension κ*(Real.sqrt r)^(-codimension κ)) := by ring
      _ = r^(codimension κ/2) := by
        rw [← Real.rpow_add hR,add_neg_cancel,Real.rpow_zero,one_mul,
          Real.sqrt_eq_rpow,← Real.rpow_mul hr.le,← Real.rpow_add hr]
        congr 1
        ring
  calc
    _ ≤ (R*r)^codimension κ * (sausagePointConstant κ * (R*Real.sqrt r)^(-codimension κ)) :=
      hb'.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (sausagePointConstant_pos κ hκ hκ8).le)
        (Real.rpow_nonneg (mul_nonneg hR.le hr.le) _))
    _ = _ := by rw [← mul_assoc,mul_comm ((R*r)^codimension κ),mul_assoc,hid]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma sle_low_center_approach_scaled
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hz : 0 ≤ z.im) (hn : R/2 ≤ ‖z‖)
    (r : ℝ) (hr : 0 < r) (hr16 : r < 1/16) (hy : z.im ≤ R*Real.sqrt r) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < R*r}).toReal ≤
      (8/((8-κ)/32))^boundaryApproachPower κ * r^(boundaryApproachPower κ/2) := by
  obtain ⟨B,hB,_⟩ := hSLE.2
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hδ : 0 < (8-κ)/32 := by positivity
  have hβ : 0 < boundaryApproachPower κ := by unfold boundaryApproachPower; positivity
  have hs := Real.sqrt_pos.mpr hr
  have hsq := Real.sq_sqrt hr.le
  have hs4 : Real.sqrt r < 1/4 := by nlinarith [Real.sqrt_nonneg r]
  have hrs : r ≤ Real.sqrt r := by nlinarith [Real.sqrt_nonneg r]
  have hx : R/4 ≤ |z.re| := by
    have hn' := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg hz] at hn'
    nlinarith [mul_pos hR (sub_pos.mpr hs4)]
  have hx0 : z.re ≠ 0 := by
    intro he
    rw [he,abs_zero] at hx
    linarith
  have hd : dist z (z.re:ℂ) = z.im := by
    rw [dist_eq_norm]
    have he : z-(z.re:ℂ) = (z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
  have hb := sle_real_center_approach κ hκ hκ8 γ hSLE z.re (2*R*Real.sqrt r) hx0 (by positivity)
  have he : P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < R*r} ≤
      P {ω | ∃ t : ℝ≥0, dist (γ ω t) (z.re:ℂ) < 2*R*Real.sqrt r} := by
    apply measure_mono
    rintro ω ⟨t,ht⟩
    refine ⟨t,?_⟩
    have hh := dist_triangle (γ ω t) z (z.re:ℂ)
    rw [hd] at hh
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hrs)]
  have hb' := ENNReal.toReal_mono ENNReal.ofReal_ne_top (he.trans hb)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)] at hb'
  have hq : (2*R*Real.sqrt r)/(((8-κ)/32)*|z.re|) ≤ (8/((8-κ)/32))*Real.sqrt r := by
    calc
      _ ≤ (2*R*Real.sqrt r)/(((8-κ)/32)*(R/4)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left (show R/4 ≤ |z.re| from hx) hδ.le)
      _ = _ := by field_simp; ring
  have hsβ : (Real.sqrt r)^boundaryApproachPower κ = r^(boundaryApproachPower κ/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hr.le]
    congr 1
    ring
  calc
    _ ≤ ((8/((8-κ)/32))*Real.sqrt r)^boundaryApproachPower κ :=
      hb'.trans (Real.rpow_le_rpow (by positivity) hq hβ.le)
    _ = _ := by rw [Real.mul_rpow (by positivity) hs.le,hsβ]

 

theorem sle_annular_small_target_scaled
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hz : 0 ≤ z.im)
    (hn : R/2 ≤ ‖z‖) (_hn2 : ‖z‖ ≤ 2*R)
    (r : ℝ) (hr : 0 < r) (hr16 : r < 1/16) :
    P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < R*r} ≤
      ENNReal.ofReal (annularApproachConstant κ * r^annularApproachPower κ) := by
  obtain ⟨B,hB,_⟩ := hSLE.2
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hC := annularApproachConstant_pos κ hκ hκ8
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  have hr1 : r ≤ 1 := by linarith
  by_cases hy : z.im ≤ R*Real.sqrt r
  · have hb := sle_low_center_approach_scaled κ hκ hκ8 γ hSLE z R hR hz hn r hr hr16 hy
    have hp := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_left
      (boundaryApproachPower κ/2) (codimension κ/2))
    have hcoeff : (8/((8-κ)/32))^boundaryApproachPower κ ≤ annularApproachConstant κ := by
      exact le_add_of_nonneg_right (sausagePointConstant_pos κ hκ hκ8).le
    exact hb.trans (mul_le_mul hcoeff hp (Real.rpow_nonneg hr.le _) hC.le)
  · have hb := sle_high_center_approach_scaled κ hκ hκ8 γ hSLE z R r hR hr (le_of_not_ge hy)
    have hp := Real.rpow_le_rpow_of_exponent_ge hr hr1 (min_le_right
      (boundaryApproachPower κ/2) (codimension κ/2))
    have hcoeff : sausagePointConstant κ ≤ annularApproachConstant κ := by
      exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
    exact hb.trans (mul_le_mul hcoeff hp (Real.rpow_nonneg hr.le _) hC.le)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 
lemma stripRectangle_norm_sub_le (a b l : ℝ) (w : ℂ)
    (hw : w ∈ stripRectangle a b l) :
    ‖w-((a:ℂ)+(b:ℂ)*Complex.I)‖ ≤ (1+Real.pi)*l := by
  rcases hw with ⟨hwr,hwr',hwi,hwi'⟩
  have hr : 0 ≤ (w-((a:ℂ)+(b:ℂ)*Complex.I)).re := by simpa using sub_nonneg.mpr hwr
  have hi : 0 ≤ (w-((a:ℂ)+(b:ℂ)*Complex.I)).im := by simpa using sub_nonneg.mpr hwi
  have hh := Complex.norm_le_abs_re_add_abs_im (w-((a:ℂ)+(b:ℂ)*Complex.I))
  rw [abs_of_nonneg hr,abs_of_nonneg hi] at hh
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im, mul_zero, mul_one,
    sub_self,add_zero,Complex.sub_im,Complex.add_im,Complex.mul_im,
    zero_add] at hh
  nlinarith

lemma stripRectangle_exp_distance (a b l : ℝ) (hl : 0 < l)
    (hs : (1+Real.pi)*l ≤ 1) (w : ℂ) (hw : w ∈ stripRectangle a b l) :
    dist (Complex.exp w) (Complex.exp ((a:ℂ)+(b:ℂ)*Complex.I)) <
      Real.exp a * (3*(1+Real.pi)*l) := by
  let c : ℂ := (a:ℂ)+(b:ℂ)*Complex.I
  have hn := stripRectangle_norm_sub_le a b l w hw
  have he : Complex.exp w - Complex.exp c =
      Complex.exp c * (Complex.exp (w-c)-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    ring
  have hc : ‖Complex.exp c‖ = Real.exp a := by simp [c,Complex.norm_exp]
  rw [dist_eq_norm,show ((a:ℂ)+(b:ℂ)*Complex.I) = c from rfl,he,norm_mul,hc]
  calc
    _ ≤ Real.exp a * (2*‖w-c‖) := mul_le_mul_of_nonneg_left
      (Complex.norm_exp_sub_one_le (hn.trans hs)) (Real.exp_pos a).le
    _ ≤ Real.exp a * (2*((1+Real.pi)*l)) := by gcongr
    _ < _ := by
      apply mul_lt_mul_of_pos_left _ (Real.exp_pos a)
      have hh : 0 < (1+Real.pi)*l := mul_pos (by linarith [Real.pi_pos]) hl
      nlinarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma stripHittingConstant_pos (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < stripHittingConstant κ := by
  have hC := annularApproachConstant_pos κ hκ hκ8
  have hp := Real.pi_pos
  unfold stripHittingConstant
  positivity

 

theorem sle_exp_strip_rectangle_hit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (a b l : ℝ) (hb0 : 0 ≤ b) (hbpi : b ≤ Real.pi) (hl : 0 < l) :
    P {ω | ∃ t : ℝ≥0, γ ω t ∈ Complex.exp '' stripRectangle a b l} ≤
      ENNReal.ofReal (stripHittingConstant κ * l^annularApproachPower κ) := by
  obtain ⟨B,hB,_⟩ := hSLE.2
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hC := annularApproachConstant_pos κ hκ hκ8
  have hα := annularApproachPower_pos κ hκ hκ8
  have hD : 0 < 1+Real.pi := by have hp := Real.pi_pos; linarith
  have h64 : 0 < 64*(1+Real.pi) := by positivity
  by_cases hs : l < 1/(64*(1+Real.pi))
  · have hs' : 64*(1+Real.pi)*l < 1 := by
      have hh := (lt_div_iff₀ h64).mp hs
      nlinarith
    let c : ℂ := Complex.exp ((a:ℂ)+(b:ℂ)*Complex.I)
    have hc : ‖c‖ = Real.exp a := by simp [c,Complex.norm_exp]
    have hci : 0 ≤ c.im := by
      simp only [c,Complex.exp_im,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
        sub_self,add_zero,Complex.add_im,Complex.mul_im,zero_add]
      exact mul_nonneg (Real.exp_pos a).le (Real.sin_nonneg_of_mem_Icc ⟨hb0,hbpi⟩)
    have hb := sle_annular_small_target_scaled κ hκ hκ8 γ hSLE c (Real.exp a)
      (Real.exp_pos a) hci (by rw [hc]; linarith [Real.exp_pos a])
      (by rw [hc]; linarith [Real.exp_pos a]) (3*(1+Real.pi)*l)
      (by positivity) (by nlinarith)
    have hsub : P {ω | ∃ t : ℝ≥0, γ ω t ∈ Complex.exp '' stripRectangle a b l} ≤
        P {ω | ∃ t : ℝ≥0, dist (γ ω t) c < Real.exp a * (3*(1+Real.pi)*l)} := by
      apply measure_mono
      rintro ω ⟨t,w,hw,he⟩
      refine ⟨t,?_⟩
      rw [← he]
      exact stripRectangle_exp_distance a b l hl (by nlinarith) w hw
    refine (hsub.trans hb).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.mul_rpow (by positivity : 0 ≤ 3*(1+Real.pi)) hl.le]
    unfold stripHittingConstant
    have hp : (3*(1+Real.pi))^annularApproachPower κ ≤
        (64*(1+Real.pi))^annularApproachPower κ := by
      apply Real.rpow_le_rpow (by positivity) (by nlinarith) hα.le
    have hcoeff : annularApproachConstant κ * (3*(1+Real.pi))^annularApproachPower κ ≤
        (annularApproachConstant κ+1) * (64*(1+Real.pi))^annularApproachPower κ :=
      mul_le_mul (by linarith) hp (Real.rpow_nonneg (by positivity) _) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hl.le (annularApproachPower κ))]
  · have hs' : 1 ≤ 64*(1+Real.pi)*l := by
      have hh := (div_le_iff₀ h64).mp (le_of_not_gt hs)
      nlinarith
    have hp : 1 ≤ (64*(1+Real.pi)*l)^annularApproachPower κ :=
      Real.one_le_rpow hs' hα.le
    rw [Real.mul_rpow h64.le hl.le] at hp
    have hc : 1 ≤ stripHittingConstant κ * l^annularApproachPower κ := by
      unfold stripHittingConstant
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hp)]
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hc

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_DyadicStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic Strips for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma inv_pow_rpow_two (k : ℕ) (α : ℝ) :
    (1/(2:ℝ)^k)^α = (2:ℝ)^(-α*(k:ℝ)) := by
  rw [one_div,Real.inv_rpow (by positivity)]
  rw [← Real.rpow_natCast (2:ℝ) k,← Real.rpow_mul (by norm_num : 0 ≤ (2:ℝ)),
    ← Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ))]
  congr 1
  ring

 

theorem sle_dyadic_strip_rectangle_hit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (j : ℤ) (k : ℕ) (i m : Fin (2^k)) :
    P {ω | ∃ t : ℝ≥0, γ ω t ∈ Complex.exp '' dyadicStripRectangle j k i m} ≤
      ENNReal.ofReal (stripHittingConstant κ *
        (2:ℝ)^(-annularApproachPower κ*(k:ℝ))) := by
  have hk : 0 < (2:ℝ)^k := by positivity
  have hm : (m:ℝ) ≤ (2:ℝ)^k := by
    exact_mod_cast m.isLt.le
  have hz : 0 ≤ Real.pi*((m:ℝ)/(2:ℝ)^k) := by positivity
  have hp : Real.pi*((m:ℝ)/(2:ℝ)^k) ≤ Real.pi := by
    exact mul_le_of_le_one_right Real.pi_pos.le ((div_le_one hk).mpr hm)
  have hh := sle_exp_strip_rectangle_hit κ hκ hκ8 γ hSLE
    ((j:ℝ)+(i:ℝ)/(2:ℝ)^k) (Real.pi*((m:ℝ)/(2:ℝ)^k))
    (1/(2:ℝ)^k) hz hp (by positivity)
  simpa only [dyadicStripRectangle,inv_pow_rpow_two] using hh

 

theorem ordinary_sle_strip_hitting_constants
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
        ∀ (j : ℤ) (k : ℕ) (i m : Fin (2^k)),
        P {ω | ∃ t : ℝ≥0, γ ω t ∈ Complex.exp '' dyadicStripRectangle j k i m} ≤
          ENNReal.ofReal (C*(2:ℝ)^(-α*(k:ℝ))) := by
  refine ⟨stripHittingConstant κ,annularApproachPower κ,
    stripHittingConstant_pos κ hκ hκ8,annularApproachPower_pos κ hκ hκ8,?_⟩
  intro Ω _ P γ hγ j k i m
  exact sle_dyadic_strip_rectangle_hit κ hκ hκ8 γ hγ j k i m

end SLEExactGauge
end

section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge


lemma lintegral_inv_Ioo (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    (∫⁻ x in Ioo r R, ENNReal.ofReal x⁻¹) = ENNReal.ofReal (Real.log (R/r)) := by
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Icc r R) :=
    continuousOn_id.inv₀ (fun x hx => ne_of_gt (hr.trans_le hx.1))
  have hi : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo r R) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · congr 1
    change (∫ x, x⁻¹ ∂volume.restrict (Ioo r R)) = _
    rw [restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le hrR.le]
    apply integral_inv
    rw [uIcc_of_le hrR.le]
    intro h
    exact not_le_of_gt hr h.1
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact inv_nonneg.mpr (hr.trans hx.1).le

lemma annulusKernel_polar (r R : ℝ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    ENNReal.ofReal p.1 * annulusKernel 0 r R (Complex.polarCoord.symm p) =
      (Ioo r R).indicator (fun x : ℝ => ENNReal.ofReal x⁻¹) p.1 := by
  simp only [annulusKernel,sub_zero,Complex.norm_polarCoord_symm,abs_of_pos hp]
  by_cases h : r < p.1 ∧ p.1 < R
  · simp only [Set.indicator,Set.mem_Ioo,ite_eq_left h]
    rw [← ENNReal.ofReal_mul hp.le]
    congr 1
    field_simp
  · simp only [Set.indicator,Set.mem_Ioo,ite_eq_right h,mul_zero]

 

theorem annulusKernel_integral (q : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) :
    (∫⁻ w, annulusKernel q r R w) = ENNReal.ofReal (2*Real.pi*Real.log (R/r)) := by
  have hcenter : (∫⁻ w, annulusKernel q r R w) = ∫⁻ w, annulusKernel 0 r R w := by
    simpa only [annulusKernel,sub_zero] using
      (lintegral_sub_right_eq_self (μ := (volume : Measure ℂ)) (annulusKernel 0 r R) q)
  rw [hcenter,← Complex.lintegral_comp_polarCoord_symm]
  let f : ℝ → ℝ≥0∞ := (Ioo r R).indicator (fun x : ℝ => ENNReal.ofReal x⁻¹)
  have hf : Measurable f := (ENNReal.measurable_ofReal.comp measurable_inv).indicator measurableSet_Ioo
  have he : (∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
      annulusKernel 0 r R (Complex.polarCoord.symm p)) =
      ∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, f p.1 := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    exact annulusKernel_polar r R p hp.1
  rw [he]
  change (∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, f p.1 ∂volume.prod volume) = _
  rw [setLIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun p : ℝ × ℝ => f p.1) ((hf.comp measurable_fst).aemeasurable)]
  simp only [setLIntegral_const,Real.volume_Ioo,sub_neg_eq_add]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hsub : Ioo r R ⊆ Ioi (0:ℝ) := fun x hx => hr.trans hx.1
  have hfint : (∫⁻ x in Ioi (0:ℝ), f x) = ENNReal.ofReal (Real.log (R/r)) := by
    dsimp [f]
    rw [setLIntegral_indicator measurableSet_Ioo,inter_eq_left.mpr hsub,
      lintegral_inv_Ioo r R hr hrR]
  rw [hfint,← ENNReal.ofReal_mul]
  · congr 1
    ring
  · exact Real.log_nonneg ((one_le_div hr).mpr hrR.le)

lemma complex_deriv_real_det (d : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ d).restrictScalars ℝ).det = ‖d‖^2 := by
  simp [ContinuousLinearMap.det,LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq,Complex.normSq_eq_norm_sq]



lemma lipschitz_clip (H : ℝ) : LipschitzWith 1 (fun x : ℝ => min H (max 0 x)) := by
  have hmax : LipschitzWith 1 (fun x : ℝ => max 0 x) := by
    simpa [Function.comp_def] using lipschitzWith_max.comp ((LipschitzWith.const (0:ℝ)).prodMk LipschitzWith.id)
  simpa [Function.comp_def] using lipschitzWith_min.comp ((LipschitzWith.const H).prodMk hmax)

lemma norm_fderiv_clip_le {v : ℂ → ℝ} {z : ℂ} (hv : ContDiffAt ℝ 1 v z) (H : ℝ) :
    ‖fderiv ℝ (fun w => min H (max 0 (v w))) z‖ ≤ ‖fderiv ℝ v z‖ := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro K hK
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK.le
  obtain ⟨s,hs,hvs⟩ := hv.exists_lipschitzOnWith_of_nnnorm_lt ⟨K,hK0⟩ hK
  have hc := (lipschitz_clip H).comp_lipschitzOnWith hvs
  have he : (1 : ℝ≥0)*⟨K,hK0⟩ = ⟨K,hK0⟩ := one_mul _
  rw [he] at hc
  exact norm_fderiv_le_of_lipschitzOn ℝ hs hc

lemma norm_fderiv_log_norm_div_le {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (q : ℂ) {r : ℝ} (hr : 0 < r)
    (h0 : F z-q ≠ 0) :
    ‖fderiv ℝ (fun w => Real.log (‖F w-q‖/r)) z‖ ≤ ‖deriv F z‖ / ‖F z-q‖ := by
  let A : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ
  have hA : HasFDerivAt (fun w => F w-q) A z :=
    ((hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).sub_const q)
  have hn := (differentiableAt_id.norm ℝ h0).hasFDerivAt
  have hnorm : ‖fderiv ℝ (fun w : ℂ => ‖w‖) (F z-q)‖ = 1 :=
    norm_fderiv_norm (differentiableAt_id.norm ℝ h0)
  have hn0 : 0 < ‖F z-q‖ := norm_pos_iff.mpr h0
  have hl := ((hn.comp z hA).log (norm_ne_zero_iff.mpr h0)).sub_const (Real.log r)
  have he : (fun w => Real.log (‖F w-q‖/r)) =ᶠ[𝓝 z]
      (fun w => Real.log ‖F w-q‖ - Real.log r) := by
    filter_upwards [(hA.continuousAt.norm).eventually (Ioi_mem_nhds hn0)] with w hw
    exact Real.log_div (ne_of_gt hw) hr.ne'
  have hd := hl.congr_of_eventuallyEq he
  rw [hd.fderiv,norm_smul,Real.norm_eq_abs]
  simp only [Function.comp_apply,id_eq] at *
  rw [abs_of_pos (inv_pos.mpr hn0)]
  have hAnorm : ‖A‖ = ‖deriv F z‖ := by
    simp [A]
  have hb := (fderiv ℝ (fun w : ℂ => ‖w‖) (F z-q)).opNorm_comp_le A
  rw [hnorm,one_mul,hAnorm] at hb
  simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hn0.le)

lemma truncatedConformalLog_eq_zero {F : ℂ → ℂ} {q z : ℂ} {r H : ℝ}
    (hr : 0 < r) (hH : 0 ≤ H) (hl : ‖F z-q‖ ≤ r) :
    truncatedConformalLog F q r H z = 0 := by
  have hb : Real.log (‖F z-q‖/r) ≤ 0 := Real.log_nonpos
    (div_nonneg (norm_nonneg _) hr.le) ((div_le_one hr).mpr hl)
  simp [truncatedConformalLog,max_eq_left hb,min_eq_right hH]

lemma truncatedConformalLog_eq_height {F : ℂ → ℂ} {q z : ℂ} {r H : ℝ}
    (hr : 0 < r) (hu : Real.exp H*r ≤ ‖F z-q‖) :
    truncatedConformalLog F q r H z = H := by
  have hn : 0 < ‖F z-q‖ := (mul_pos (Real.exp_pos _) hr).trans_le hu
  have hb : H ≤ Real.log (‖F z-q‖/r) :=
    (Real.le_log_iff_exp_le (div_pos hn hr)).mpr ((le_div_iff₀ hr).mpr hu)
  exact min_eq_left (hb.trans (le_max_right _ _))

lemma fderiv_truncated_eq_zero_of_low {F : ℂ → ℂ} {q z : ℂ} {r H : ℝ}
    (hF : ContinuousAt F z) (hr : 0 < r) (hH : 0 ≤ H) (hl : ‖F z-q‖ < r) :
    fderiv ℝ (truncatedConformalLog F q r H) z = 0 := by
  have he : truncatedConformalLog F q r H =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    filter_upwards [((hF.sub_const q).norm).eventually (Iio_mem_nhds hl)] with w hw
    exact truncatedConformalLog_eq_zero hr hH hw.le
  exact ((hasFDerivAt_const (0:ℝ) z).congr_of_eventuallyEq he).fderiv

lemma fderiv_truncated_eq_zero_of_high {F : ℂ → ℂ} {q z : ℂ} {r H : ℝ}
    (hF : ContinuousAt F z) (hr : 0 < r) (hu : Real.exp H*r < ‖F z-q‖) :
    fderiv ℝ (truncatedConformalLog F q r H) z = 0 := by
  have he : truncatedConformalLog F q r H =ᶠ[𝓝 z] (fun _ => H) := by
    filter_upwards [((hF.sub_const q).norm).eventually (Ioi_mem_nhds hu)] with w hw
    exact truncatedConformalLog_eq_height hr hw.le
  exact ((hasFDerivAt_const H z).congr_of_eventuallyEq he).fderiv

lemma norm_fderiv_truncated_le {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) {z : ℂ} (hz : z ∈ D) (q : ℂ) {r H : ℝ}
    (hr : 0 < r) (h0 : F z-q ≠ 0) :
    ‖fderiv ℝ (truncatedConformalLog F q r H) z‖ ≤ ‖deriv F z‖ / ‖F z-q‖ := by
  have hcF : ContDiffAt ℝ 1 F z := ((hF.analyticAt (hD.mem_nhds hz)).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hv : ContDiffAt ℝ 1 (fun w => Real.log (‖F w-q‖/r)) z :=
    (((hcF.sub contDiffAt_const).norm ℝ h0).div_const r).log
      (div_ne_zero (norm_ne_zero_iff.mpr h0) hr.ne')
  exact (norm_fderiv_clip_le hv H).trans
    (norm_fderiv_log_norm_div_le (hF.differentiableAt (hD.mem_nhds hz)) q hr h0)

 

lemma truncated_log_energy_pointwise {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) {z : ℂ} (hz : z ∈ D) (q : ℂ)
    {r H a b : ℝ} (hr : 0 < r) (hH : 0 < H) (ha : 0 < a) (har : a < r)
    (hRb : Real.exp H*r < b) :
    ENNReal.ofReal (‖fderiv ℝ (truncatedConformalLog F q r H) z‖^2) ≤
      ENNReal.ofReal (‖deriv F z‖^2) * annulusKernel q a b (F z) := by
  have hc := (hF.differentiableAt (hD.mem_nhds hz)).continuousAt
  by_cases hband : a < ‖F z-q‖ ∧ ‖F z-q‖ < b
  · have hn : 0 < ‖F z-q‖ := ha.trans hband.1
    have hb := norm_fderiv_truncated_le hD hF hz q hr (norm_ne_zero_iff.mp hn.ne') (H := H)
    have hs : ‖fderiv ℝ (truncatedConformalLog F q r H) z‖^2 ≤
        ‖deriv F z‖^2 * (‖F z-q‖^2)⁻¹ := by
      calc
        _ ≤ (‖deriv F z‖/‖F z-q‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = _ := by rw [div_pow,div_eq_mul_inv]
    simpa only [annulusKernel,ite_eq_left hband,← ENNReal.ofReal_mul (sq_nonneg _)] using
      ENNReal.ofReal_le_ofReal hs
  · have he : fderiv ℝ (truncatedConformalLog F q r H) z = 0 := by
      rcases not_and_or.mp hband with hl | hu
      · exact fderiv_truncated_eq_zero_of_low hc hr hH.le ((le_of_not_gt hl).trans_lt har)
      · exact fderiv_truncated_eq_zero_of_high hc hr (hRb.trans_le (le_of_not_gt hu))
    simp [he]

lemma truncated_log_lipschitz_near {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) {z : ℂ} (hz : z ∈ D) (q : ℂ) {r H : ℝ}
    (hr : 0 < r) (hH : 0 < H) :
    ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ z ∈ U ∧
      LipschitzOnWith K (truncatedConformalLog F q r H) U := by
  by_cases h0 : F z-q = 0
  · have hn : ‖F z-q‖ < r := by simpa [h0] using hr
    have he := (((hF.differentiableAt (hD.mem_nhds hz)).continuousAt.sub_const q).norm).eventually
      (Iio_mem_nhds hn)
    obtain ⟨U,hU,hUo,hzU⟩ := mem_nhds_iff.mp he
    refine ⟨0,U,hUo,hzU,?_⟩
    intro x hx y hy
    rw [truncatedConformalLog_eq_zero hr hH.le (hU hx).le,
      truncatedConformalLog_eq_zero hr hH.le (hU hy).le]
    simp
  · have hcF : ContDiffAt ℝ 1 F z :=
      ((hF.analyticAt (hD.mem_nhds hz)).restrictScalars (𝕜 := ℝ)).contDiffAt
    have hv : ContDiffAt ℝ 1 (fun w => Real.log (‖F w-q‖/r)) z :=
      (((hcF.sub contDiffAt_const).norm ℝ h0).div_const r).log
        (div_ne_zero (norm_ne_zero_iff.mpr h0) hr.ne')
    let K : ℝ≥0 := ‖fderiv ℝ (fun w => Real.log (‖F w-q‖/r)) z‖₊ + 1
    have hK : ‖fderiv ℝ (fun w => Real.log (‖F w-q‖/r)) z‖₊ < K := by
      dsimp [K]; simp
    obtain ⟨U,hU,hLip⟩ := hv.exists_lipschitzOnWith_of_nnnorm_lt K hK
    refine ⟨1*K,interior U,isOpen_interior,mem_interior_iff_mem_nhds.mpr hU,?_⟩
    exact ((lipschitz_clip H).comp_lipschitzOnWith hLip).mono interior_subset


lemma local_lipschitz_weak_derivative {D : Set ℂ} (hD : IsOpen D) {u : ℂ → ℝ}
    (hlocal : ∀ x ∈ D, ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ x ∈ U ∧ LipschitzOnWith K u U)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ⊤ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ D) (v : ℂ) :
    (∫ z in D, u z * (fderiv ℝ φ z) v) =
      -(∫ z in D, (fderiv ℝ u z) v * φ z) := by
  obtain ⟨S,hSc,hφS,hSD⟩ := exists_compact_between hcφ hD hsφ
  have huS : LocallyLipschitzOn S u := by
    intro x hx
    obtain ⟨K,U,hUo,hxU,hU⟩ := hlocal x (hSD hx)
    exact ⟨K,U,mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hxU),hU⟩
  obtain ⟨K,hK⟩ := huS.exists_lipschitzOnWith_of_compact hSc
  obtain ⟨g,hglip,hug⟩ := hK.extend_real
  obtain ⟨C,hφlip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ hφ (by simp)
  have hφdiff : ∀ z, DifferentiableAt ℝ φ z := fun z => (hφ.differentiable (by simp)).differentiableAt
  have ht (z : ℂ) (hz : z ∈ tsupport φ) : u =ᶠ[𝓝 z] g := by
    filter_upwards [mem_interior_iff_mem_nhds.mp (hφS hz)] with w hw
    exact hug hw
  have hid := hglip.integral_lineDeriv_mul_eq (μ := volume) hφlip hcφ v
  have hfull : (∫ z, (fderiv ℝ g z) v * φ z) = -(∫ z, g z * (fderiv ℝ φ z) v) := by
    calc
      _ = ∫ z, lineDeriv ℝ g z v * φ z := by
        apply integral_congr_ae
        filter_upwards [hglip.ae_differentiableAt (μ := volume)] with z hz
        rw [hz.lineDeriv_eq_fderiv]
      _ = ∫ z, lineDeriv ℝ φ z (-v) * g z := hid
      _ = _ := by
        simp_rw [(hφdiff _).lineDeriv_eq_fderiv,map_neg,neg_mul,mul_comm _ (g _)]
        rw [integral_neg]
  have he1 : (fun z => u z * (fderiv ℝ φ z) v) = (fun z => g z * (fderiv ℝ φ z) v) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [hug (interior_subset (hφS hz))]
    · simp [fderiv_of_notMem_tsupport ℝ hz]
  have he2 : (fun z => (fderiv ℝ u z) v * φ z) = (fun z => (fderiv ℝ g z) v * φ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · rw [(ht z hz).fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hs1 : (∫ z in D, u z * (fderiv ℝ φ z) v) = ∫ z, u z * (fderiv ℝ φ z) v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport φ := fun h => hz (hsφ h)
    simp [fderiv_of_notMem_tsupport ℝ hn]
  have hs2 : (∫ z in D, (fderiv ℝ u z) v * φ z) = ∫ z, (fderiv ℝ u z) v * φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport φ := fun h => hz (hsφ h)
    simp [image_eq_zero_of_notMem_tsupport hn]
  rw [hs1,hs2,he1,he2,hfull]
  simp

theorem truncated_log_weak_derivative {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ⊤ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ D) (v : ℂ) :
    (∫ z in D, truncatedConformalLog F q r H z * (fderiv ℝ φ z) v) =
      -(∫ z in D, (fderiv ℝ (truncatedConformalLog F q r H) z) v * φ z) :=
  local_lipschitz_weak_derivative hD (fun _ hx => truncated_log_lipschitz_near hD hF hx q hr hH)
    φ hφ hcφ hsφ v

lemma open_univalent_weighted_area {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (hi : InjOn F D) (q : ℂ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    (∫⁻ z in D, ENNReal.ofReal (‖deriv F z‖^2)*annulusKernel q a b (F z)) ≤
      ENNReal.ofReal (2*Real.pi*Real.log (b/a)) := by
  let B : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ
  have hB : ∀ z ∈ D, HasFDerivWithinAt F (B z) D z := by
    intro z hz
    exact ((hF.differentiableAt (hD.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD.measurableSet hB hi (annulusKernel q a b)
  have hdet (z : ℂ) : |(B z).det| = ‖deriv F z‖^2 := by
    rw [show B z = (ContinuousLinearMap.toSpanSingleton ℂ (deriv F z)).restrictScalars ℝ from rfl,
      complex_deriv_real_det,abs_of_nonneg (sq_nonneg _)]
  simp only [hdet] at he
  rw [← he]
  exact (setLIntegral_le_lintegral _ _).trans_eq (annulusKernel_integral q a b ha hab)

 

theorem truncated_log_dirichlet_bound {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (hi : InjOn F D)
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ (truncatedConformalLog F q r H) z‖^2)) ≤
      ENNReal.ofReal (2*Real.pi*H) := by
  have hbound (ε : ℝ) (hε : 0 < ε) :
      (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ (truncatedConformalLog F q r H) z‖^2)) ≤
        ENNReal.ofReal (2*Real.pi*(H+2*ε)) := by
    let a := r * Real.exp (-ε)
    let b := Real.exp (H+ε)*r
    have ha : 0 < a := mul_pos hr (Real.exp_pos _)
    have har : a < r := by
      dsimp [a]
      exact (mul_lt_mul_of_pos_left (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hε)) hr).trans_eq (mul_one r)
    have hrR : r < Real.exp H*r := by
      simpa using mul_lt_mul_of_pos_right (Real.one_lt_exp_iff.mpr hH) hr
    have hRb : Real.exp H*r < b := by
      exact mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr (lt_add_of_pos_right _ hε)) hr
    have hab : a < b := har.trans (hrR.trans hRb)
    have hlog : Real.log (b/a) = H+2*ε := by
      have hid : b/a = Real.exp (H+2*ε) := by
        dsimp [a,b]
        rw [show H+2*ε = (H+ε)+ε by ring,Real.exp_add (H+ε) ε,Real.exp_neg]
        field_simp
      rw [hid,Real.log_exp]
    calc
      _ ≤ ∫⁻ z in D, ENNReal.ofReal (‖deriv F z‖^2)*annulusKernel q a b (F z) := by
        apply setLIntegral_mono' hD.measurableSet
        intro z hz
        exact truncated_log_energy_pointwise hD hF hz q hr hH ha har hRb
      _ ≤ ENNReal.ofReal (2*Real.pi*Real.log (b/a)) := open_univalent_weighted_area hD hF hi q a b ha hab
      _ = _ := by rw [hlog]
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (2*Real.pi*(H+2*ε))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (2*Real.pi*H))) := by
    have hc : Continuous (fun ε : ℝ => ENNReal.ofReal (2*Real.pi*(H+2*ε))) := ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with ε hε using hbound ε hε)

lemma measurable_real_gradient (u : ℂ → ℝ) : Measurable (gradient u) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp (measurable_fderiv ℝ u)

lemma norm_real_gradient (u : ℂ → ℝ) (z : ℂ) : ‖gradient u z‖ = ‖fderiv ℝ u z‖ := by
  simp [gradient]

theorem truncated_log_sobolev_energy {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (hi : InjOn F D)
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    MemLp (gradient (truncatedConformalLog F q r H)) 2 (volume.restrict D) ∧
    (∫ z in D, ‖gradient (truncatedConformalLog F q r H) z‖^2) ≤ 2*Real.pi*H ∧
    ∀ (φ : ℂ → ℝ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → tsupport φ ⊆ D →
      ((∫ z in D, truncatedConformalLog F q r H z * (fderiv ℝ φ z) (1:ℂ)) =
        -(∫ z in D, (gradient (truncatedConformalLog F q r H) z).re * φ z)) ∧
      ((∫ z in D, truncatedConformalLog F q r H z * (fderiv ℝ φ z) Complex.I) =
        -(∫ z in D, (gradient (truncatedConformalLog F q r H) z).im * φ z)) := by
  let u := truncatedConformalLog F q r H
  have hgm : AEStronglyMeasurable (gradient u) (volume.restrict D) :=
    (measurable_real_gradient u).aestronglyMeasurable
  have hsq : AEStronglyMeasurable (fun z => ‖gradient u z‖^2) (volume.restrict D) := hgm.norm.pow 2
  have hb : (∫⁻ z in D, ENNReal.ofReal (‖gradient u z‖^2)) ≤ ENNReal.ofReal (2*Real.pi*H) := by
    simpa only [norm_real_gradient] using truncated_log_dirichlet_bound hD hF hi q r H hr hH
  have hint : Integrable (fun z => ‖gradient u z‖^2) (volume.restrict D) :=
    (lintegral_ofReal_ne_top_iff_integrable hsq (ae_of_all _ fun z => sq_nonneg _)).mp
      (ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top))
  have henergy : (∫ z in D, ‖gradient u z‖^2) ≤ 2*Real.pi*H := by
    have he := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _)
    rw [← he] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*Real.pi*H)).mp hb
  refine ⟨(memLp_two_iff_integrable_sq_norm hgm).mpr hint,henergy,?_⟩
  intro φ hφ hcφ hsφ
  constructor
  · simpa only [real_gradient_re] using truncated_log_weak_derivative hD hF q r H hr hH φ hφ hcφ hsφ (1:ℂ)
  · simpa only [real_gradient_im] using truncated_log_weak_derivative hD hF q r H hr hH φ hφ hcφ hsφ Complex.I

lemma exp_strip_halfplane : MapsTo Complex.exp {z : ℂ | 0 < z.im ∧ z.im < Real.pi}
    {z : ℂ | 0 < z.im} := by
  intro z hz
  change 0 < (Complex.exp z).im
  rw [Complex.exp_im]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2)

lemma exp_injective_strip : InjOn Complex.exp {z : ℂ | 0 < z.im ∧ z.im < Real.pi} := by
  intro x hx y hy hxy
  exact Complex.exp_inj_of_neg_pi_lt_of_le_pi
    ((neg_neg_of_pos Real.pi_pos).trans hx.1) hx.2.le
    ((neg_neg_of_pos Real.pi_pos).trans hy.1) hy.2.le hxy

 
theorem conformal_strip_total_energy {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hi : InjOn F {z | 0 < z.im})
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    MemLp (gradient (conformalStripLog F q r H)) 2
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < Real.pi}) ∧
    (∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
      ‖gradient (conformalStripLog F q r H) z‖^2) ≤ 2*Real.pi*H ∧
    ∀ (φ : ℂ → ℝ), ContDiff ℝ ⊤ φ → HasCompactSupport φ →
      tsupport φ ⊆ {z : ℂ | 0 < z.im ∧ z.im < Real.pi} →
      ((∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
          conformalStripLog F q r H z * (fderiv ℝ φ z) (1:ℂ)) =
        -(∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
          (gradient (conformalStripLog F q r H) z).re * φ z)) ∧
      ((∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
          conformalStripLog F q r H z * (fderiv ℝ φ z) Complex.I) =
        -(∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi},
          (gradient (conformalStripLog F q r H) z).im * φ z)) := by
  have hS : IsOpen {z : ℂ | 0 < z.im ∧ z.im < Real.pi} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hcomp : DifferentiableOn ℂ (F ∘ Complex.exp) {z : ℂ | 0 < z.im ∧ z.im < Real.pi} :=
    hF.comp Complex.differentiable_exp.differentiableOn exp_strip_halfplane
  have hicomp : InjOn (F ∘ Complex.exp) {z : ℂ | 0 < z.im ∧ z.im < Real.pi} :=
    hi.comp exp_injective_strip exp_strip_halfplane
  exact truncated_log_sobolev_energy hS hcomp hicomp q r H hr hH

lemma truncated_log_continuousOn {D : Set ℂ} (hD : IsOpen D) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F D) (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    ContinuousOn (truncatedConformalLog F q r H) D := by
  apply LocallyLipschitzOn.continuousOn
  intro z hz
  obtain ⟨K,U,hU,hzU,hlip⟩ := truncated_log_lipschitz_near hD hF hz q hr hH
  exact ⟨K,U,mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hzU),hlip⟩

lemma truncated_log_bounds (F : ℂ → ℂ) (q : ℂ) (r H : ℝ) (hH : 0 ≤ H) (z : ℂ) :
    0 ≤ truncatedConformalLog F q r H z ∧ truncatedConformalLog F q r H z ≤ H := by
  exact ⟨le_min hH (le_max_left _ _),min_le_left _ _⟩

theorem conformal_unit_strip_weak_gradient {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hi : InjOn F {z | 0 < z.im})
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    IsStripWeakGradient (conformalStripLog F q r H)
      (gradient (conformalStripLog F q r H)) ∧
    (∫ z in openUnitStrip, ‖gradient (conformalStripLog F q r H) z‖^2) ≤
      2*Real.pi*H := by
  have hsub : openUnitStrip ⊆ {z : ℂ | 0 < z.im ∧ z.im < Real.pi} := fun z hz => hz.2.2
  have hcm : DifferentiableOn ℂ (F ∘ Complex.exp) openUnitStrip :=
    (hF.comp Complex.differentiable_exp.differentiableOn exp_strip_halfplane).mono hsub
  have hicm : InjOn (F ∘ Complex.exp) openUnitStrip :=
    (hi.comp exp_injective_strip exp_strip_halfplane).mono hsub
  obtain ⟨hgrad,henergy,hweak⟩ :=
    truncated_log_sobolev_energy openUnitStrip_isOpen hcm hicm q r H hr hH
  have : IsFiniteMeasure (volume.restrict openUnitStrip) :=
    isFiniteMeasure_restrict.mpr openUnitStrip_measure_lt_top.ne
  have hu : MemLp (truncatedConformalLog (F ∘ Complex.exp) q r H) 2
      (volume.restrict openUnitStrip) :=
    memLp_of_bounded (ae_of_all _ fun z => truncated_log_bounds _ _ _ _ hH.le z)
      ((truncated_log_continuousOn openUnitStrip_isOpen hcm q r H hr hH).aestronglyMeasurable
        openUnitStrip_isOpen.measurableSet) 2
  exact ⟨⟨hu,hgrad,hweak⟩,henergy⟩


lemma sphericalTruncatedLog_continuous (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    Continuous (sphericalTruncatedLog q r H) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  induction x using OnePoint.rec with
  | infty =>
    apply OnePoint.continuousAt_infty.mpr
    intro S hS
    refine ⟨Metric.closedBall q (Real.exp H*r),Metric.isClosed_closedBall,isCompact_closedBall _ _,?_⟩
    intro z hz
    have hb : Real.exp H*r ≤ ‖z-q‖ := by
      rw [mem_compl_iff,Metric.mem_closedBall,dist_eq_norm] at hz
      exact (lt_of_not_ge hz).le
    have he : sphericalTruncatedLog q r H (z : OnePoint ℂ) = H := by
      rw [sphericalTruncatedLog_coe]
      exact truncatedConformalLog_eq_height (F := id) hr hb
    change sphericalTruncatedLog q r H (z : OnePoint ℂ) ∈ S
    rw [he]
    exact mem_of_mem_nhds hS
  | coe z =>
    rw [OnePoint.continuousAt_coe]
    change ContinuousAt (truncatedConformalLog id q r H) z
    have hc := truncated_log_continuousOn isOpen_univ
      (differentiable_id.differentiableOn : DifferentiableOn ℂ id Set.univ) q r H hr hH
    exact (continuousOn_univ.mp hc).continuousAt

 
theorem spherical_strip_log_continuous {Fbar : ℂ → OnePoint ℂ}
    (hFbar : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    ContinuousOn (fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z)))
      {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi} := by
  have hmap : MapsTo Complex.exp {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi}
      {z : ℂ | 0 ≤ z.im} := by
    intro z hz
    change 0 ≤ (Complex.exp z).im
    rw [Complex.exp_im]
    exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi hz.1 hz.2)
  exact (sphericalTruncatedLog_continuous q r H hr hH).continuousOn.comp
    (hFbar.comp Complex.continuous_exp.continuousOn hmap) (mapsTo_univ _ _)

 

theorem source_strip_log_regularity {F : ℂ → ℂ} {Fbar : ℂ → OnePoint ℂ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hi : InjOn F {z | 0 < z.im})
    (hbar : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    (hext : ∀ z : ℂ, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    let U := fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z))
    ContinuousOn U {z : ℂ | 0 ≤ z.im ∧ z.im ≤ Real.pi} ∧
    (∀ z, 0 ≤ U z ∧ U z ≤ H) ∧
    IsStripWeakGradient U (gradient U) ∧
    MemLp (gradient U) 2 (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < Real.pi}) ∧
    (∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi}, ‖gradient U z‖^2) ≤
      2*Real.pi*H := by
  let U := fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z))
  let V := conformalStripLog F q r H
  let S := {z : ℂ | 0 < z.im ∧ z.im < Real.pi}
  have hS : IsOpen S := (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)
  have heq : EqOn U V S := by
    intro z hz
    dsimp [U]
    rw [hext (Complex.exp z) (exp_strip_halfplane hz),sphericalTruncatedLog_coe]
    rfl
  have hgeq : EqOn (gradient U) (gradient V) S := by
    intro z hz
    have he : U =ᶠ[𝓝 z] V := by
      filter_upwards [hS.mem_nhds hz] with w hw
      exact heq hw
    simp only [gradient,he.fderiv_eq]
  have heae : U =ᵐ[volume.restrict S] V := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    exact heq hz
  have hgae : gradient U =ᵐ[volume.restrict S] gradient V := by
    filter_upwards [ae_restrict_mem hS.measurableSet] with z hz
    exact hgeq hz
  have hsub : openUnitStrip ⊆ S := fun z hz => hz.2.2
  have heu : U =ᵐ[volume.restrict openUnitStrip] V :=
    heae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hgu : gradient U =ᵐ[volume.restrict openUnitStrip] gradient V :=
    hgae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  obtain ⟨hV,-⟩ := conformal_unit_strip_weak_gradient hF hi q r H hr hH
  obtain ⟨hgrad,henergy,-⟩ := conformal_strip_total_energy hF hi q r H hr hH
  refine ⟨spherical_strip_log_continuous hbar q r H hr hH,?_,?_,(memLp_congr_ae hgae).mpr hgrad,?_⟩
  · intro z
    change 0 ≤ sphericalTruncatedLog q r H (Fbar (Complex.exp z)) ∧
      sphericalTruncatedLog q r H (Fbar (Complex.exp z)) ≤ H
    generalize Fbar (Complex.exp z) = x
    induction x using OnePoint.rec with
    | infty => simpa using And.intro hH.le (le_refl H)
    | coe w => exact truncated_log_bounds id q r H hH.le w
  · refine ⟨(memLp_congr_ae heu).mpr hV.1,(memLp_congr_ae hgu).mpr hV.2.1,?_⟩
    intro φ hφ hc hs
    obtain ⟨hrx,hix⟩ := hV.2.2 φ hφ hc hs
    have h1 : (∫ z in openUnitStrip, U z * (fderiv ℝ φ z) (1:ℂ)) =
        (∫ z in openUnitStrip, V z * (fderiv ℝ φ z) (1:ℂ)) :=
      integral_congr_ae (heu.mono fun z hz => by dsimp only; rw [hz])
    have h2 : (∫ z in openUnitStrip, U z * (fderiv ℝ φ z) Complex.I) =
        (∫ z in openUnitStrip, V z * (fderiv ℝ φ z) Complex.I) :=
      integral_congr_ae (heu.mono fun z hz => by dsimp only; rw [hz])
    have h3 : (∫ z in openUnitStrip, (gradient U z).re * φ z) =
        (∫ z in openUnitStrip, (gradient V z).re * φ z) :=
      integral_congr_ae (hgu.mono fun z hz => by dsimp only; rw [hz])
    have h4 : (∫ z in openUnitStrip, (gradient U z).im * φ z) =
        (∫ z in openUnitStrip, (gradient V z).im * φ z) :=
      integral_congr_ae (hgu.mono fun z hz => by dsimp only; rw [hz])
    exact ⟨h1.trans (hrx.trans (congrArg Neg.neg h3.symm)),
      h2.trans (hix.trans (congrArg Neg.neg h4.symm))⟩
  · calc
      _ = ∫ z in S, ‖gradient V z‖^2 :=
        integral_congr_ae (hgae.mono fun z hz => by dsimp only; rw [hz])
      _ ≤ _ := henergy

 

end SLEExactGauge
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_NestedMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Means for chordal SLE. -/

section
section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge
universe u
lemma slice_oscillation_le_integral {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hl : LocallyLipschitzOn (Ioo a b) f)
    (hg : IntegrableOn g (Icc a b)) (hgn : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo a b → ‖deriv f t‖ ≤ g t) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖f x-f y‖ ≤ ∫ t in Icc a b, g t := by
  have hint (x y : ℝ) (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) (hxy : x ≤ y) :
      ‖f y-f x‖ ≤ ∫ t in Icc a b, g t := by
    have hs : Icc x y ⊆ Ioo a b := by
      intro t ht
      exact ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
    obtain ⟨K,hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      isCompact_Icc (hl.mono hs)
    have hAC : AbsolutelyContinuousOnInterval f x y :=
      (by simpa [uIcc_of_le hxy] using hK : LipschitzOnWith K f (uIcc x y)).absolutelyContinuousOnInterval
    rw [← hAC.integral_deriv_eq_sub, intervalIntegral.integral_of_le hxy]
    have hdint : IntegrableOn (deriv f) (Ioc x y) :=
      hAC.intervalIntegrable_deriv.1
    have hgin : IntegrableOn g (Ioc x y) := hg.mono_set (by
      intro t ht; exact ⟨hx.1.le.trans ht.1.le,ht.2.trans hy.2.le⟩)
    calc
      ‖∫ t in Ioc x y, deriv f t‖ ≤ ∫ t in Ioc x y, ‖deriv f t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in Ioc x y, g t := integral_mono_ae hdint.norm hgin (by
        filter_upwards [ae_restrict_of_ae hd,ae_restrict_mem measurableSet_Ioc] with t ht htS
        exact ht (hs ⟨htS.1.le,htS.2⟩))
      _ ≤ ∫ t in Icc a b, g t := setIntegral_mono_set hg
        (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact hgn t ht)
        (Eventually.of_forall fun t ht => ⟨hx.1.le.trans ht.1.le,ht.2.trans hy.2.le⟩)
  have hi (x : ℝ) (hx : x ∈ Ioo a b) (y : ℝ) (hy : y ∈ Ioo a b) :
      ‖f x-f y‖ ≤ ∫ t in Icc a b, g t := by
    rcases le_total x y with h | h
    · simpa only [norm_sub_rev] using hint x y hx hy h
    · exact hint y x hy hx h
  have hc : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hyall (x : ℝ) (hx : x ∈ Ioo a b) :
      ∀ y ∈ Icc a b, ‖f x-f y‖ ≤ ∫ t in Icc a b, g t := by
    intro y hy
    apply le_on_closure (fun y hy => hi x hx y hy) _ continuousOn_const (hc.symm ▸ hy)
    rw [hc]
    exact (continuousOn_const.sub hf).norm
  intro x hx y hy
  apply le_on_closure (fun x hx => hyall x hx y hy) _ continuousOn_const (hc.symm ▸ hx)
  rw [hc]
  exact (hf.sub continuousOn_const).norm

lemma locallyLipschitz_ae_differentiable {D : Set ℂ} (hD : IsOpen D) {u : ℂ → ℝ}
    (hl : LocallyLipschitzOn D u) :
    ∀ᵐ z ∂volume, z ∈ D → DifferentiableAt ℝ u z := by
  classical
  have hloc (z : D) : ∃ (K : ℝ≥0) (U : Set ℂ), IsOpen U ∧ z.1 ∈ U ∧
      LipschitzOnWith K u U := by
    obtain ⟨K,t,ht,htl⟩ := hl z.2
    rw [nhdsWithin_eq_nhds.mpr (hD.mem_nhds z.2)] at ht
    obtain ⟨U,hUt,hUo,hzU⟩ := _root_.mem_nhds_iff.mp ht
    exact ⟨K,U,hUo,hzU,htl.mono hUt⟩
  choose K U hUo hxU hULip using hloc
  have hcov : D ⊆ ⋃ x : D, U x := fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hxU ⟨z,hz⟩⟩
  obtain ⟨t,ht,htcov⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover U hUo hcov
  have ha (x : D) : ∀ᵐ z ∂volume, z ∈ U x → DifferentiableAt ℝ u z := by
    filter_upwards [(hULip x).ae_differentiableWithinAt_of_mem (μ := volume)] with z hz hzU
    exact (hz hzU).differentiableAt ((hUo x).mem_nhds hzU)
  filter_upwards [(ae_ball_iff ht).mpr (fun x _ => ha x)] with z hz hzD
  obtain ⟨x,htx,hzx⟩ := mem_iUnion₂.mp (htcov hzD)
  exact hz x htx hzx

lemma complexCoordinates_eq (p : ℝ × ℝ) :
    complexCoordinates p = Complex.measurableEquivRealProd.symm p := by
  apply Complex.ext <;> simp [complexCoordinates]

lemma complexCoordinates_preserving : MeasurePreserving complexCoordinates volume volume := by
  simpa only [funext complexCoordinates_eq] using
    Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd

lemma complexCoordinates_continuous : Continuous complexCoordinates := by
  unfold complexCoordinates
  fun_prop

lemma vertical_isometry (x : ℝ) : Isometry (fun y : ℝ => complexCoordinates (x,y)) := by
  apply Isometry.of_dist_eq
  intro y z
  simp only [dist_eq_norm,complexCoordinates]
  have he : ((x:ℂ)+(y:ℂ)*Complex.I)-((x:ℂ)+(z:ℂ)*Complex.I) =
      ((y-z:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real]

lemma horizontal_isometry (y : ℝ) : Isometry (fun x : ℝ => complexCoordinates (x,y)) := by
  apply Isometry.of_dist_eq
  intro x z
  simp [dist_eq_norm,complexCoordinates, ← Complex.ofReal_sub]

lemma locallyLipschitz_comp_of_isometry {D : Set ℂ} (hD : IsOpen D) {u : ℂ → ℝ}
    (hu : LocallyLipschitzOn D u) {f : ℝ → ℂ} (hf : Isometry f) {s : Set ℝ}
    (hs : MapsTo f s D) : LocallyLipschitzOn s (u ∘ f) := by
  intro x hx
  obtain ⟨K,t,ht,hKt⟩ := hu (hs hx)
  rw [nhdsWithin_eq_nhds.mpr (hD.mem_nhds (hs hx))] at ht
  refine ⟨K*1,f ⁻¹' t,mem_nhdsWithin_of_mem_nhds (hf.continuous.continuousAt.preimage_mem_nhds ht),?_⟩
  exact hKt.comp hf.lipschitz.lipschitzOnWith (fun _ h => h)

lemma vertical_deriv_norm_le {u : ℂ → ℝ} {x y : ℝ}
    (hu : DifferentiableAt ℝ u (complexCoordinates (x,y))) :
    ‖deriv (fun t : ℝ => u (complexCoordinates (x,t))) y‖ ≤
      ‖gradient u (complexCoordinates (x,y))‖ := by
  have hi : HasDerivAt (fun t : ℝ => complexCoordinates (x,t)) Complex.I y := by
    simpa [complexCoordinates] using
      ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x:ℂ)
  have hh := hu.hasFDerivAt.comp_hasDerivAt y hi
  change ‖deriv (u ∘ (fun t : ℝ => complexCoordinates (x,t))) y‖ ≤ _
  rw [hh.deriv, ← inner_gradient_left]
  simpa using norm_inner_le_norm (𝕜 := ℝ) (gradient u (complexCoordinates (x,y))) Complex.I

lemma horizontal_deriv_norm_le {u : ℂ → ℝ} {x y : ℝ}
    (hu : DifferentiableAt ℝ u (complexCoordinates (x,y))) :
    ‖deriv (fun t : ℝ => u (complexCoordinates (t,y))) x‖ ≤
      ‖gradient u (complexCoordinates (x,y))‖ := by
  have hi : HasDerivAt (fun t : ℝ => complexCoordinates (t,y)) 1 x := by
    simpa [complexCoordinates] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y:ℂ)*Complex.I)
  have hh := hu.hasFDerivAt.comp_hasDerivAt x hi
  change ‖deriv (u ∘ (fun t : ℝ => complexCoordinates (t,y))) x‖ ≤ _
  rw [hh.deriv, ← inner_gradient_left]
  simpa using norm_inner_le_norm (𝕜 := ℝ) (gradient u (complexCoordinates (x,y))) 1

lemma cartesianRectangle_preimage (a b c d : ℝ) :
    cartesianRectangle a b c d = Complex.measurableEquivRealProd ⁻¹' (Icc a b ×ˢ Icc c d) := by
  ext z
  simp only [cartesianRectangle, mem_ofPred_eq,mem_preimage,mem_prod,mem_Icc,Complex.measurableEquivRealProd_apply]
  tauto

lemma cartesianRectangle_measurable (a b c d : ℝ) : MeasurableSet (cartesianRectangle a b c d) := by
  rw [cartesianRectangle_preimage]
  exact (measurableSet_Icc.prod measurableSet_Icc).preimage
    Complex.measurableEquivRealProd.measurable

lemma complexCoordinates_rect_preserving (a b c d : ℝ) :
    MeasurePreserving complexCoordinates
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))
      (volume.restrict (cartesianRectangle a b c d)) := by
  have h := complexCoordinates_preserving.restrict_preimage (cartesianRectangle_measurable a b c d)
  have he : complexCoordinates ⁻¹' cartesianRectangle a b c d = Icc a b ×ˢ Icc c d := by
    ext p
    simp only [mem_preimage,cartesianRectangle,mem_ofPred_eq,complexCoordinates,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,Complex.add_im,Complex.mul_im,mul_zero,sub_self,add_zero,mul_one,zero_add,mem_prod,mem_Icc]
    tauto
  rwa [he,Measure.volume_eq_prod, ← Measure.prod_restrict] at h

lemma cartesianRectangle_compact (a b c d : ℝ) : IsCompact (cartesianRectangle a b c d) := by
  have he : cartesianRectangle a b c d = complexCoordinates '' (Icc a b ×ˢ Icc c d) := by
    ext z; constructor
    · intro hz
      refine ⟨(z.re,z.im),?_,?_⟩
      · exact ⟨⟨hz.1,hz.2.1⟩,hz.2.2⟩
      · apply Complex.ext <;> simp [complexCoordinates]
    · rintro ⟨p,hp,rfl⟩
      rcases hp with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩
      simpa [cartesianRectangle,complexCoordinates] using And.intro ha (And.intro hb (And.intro hc hd))
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image complexCoordinates_continuous

lemma cartesianRectangle_integral {a b c d : ℝ} {u : ℂ → ℝ}
    (hu : IntegrableOn u (cartesianRectangle a b c d)) :
    (∫ z in cartesianRectangle a b c d, u z) =
      ∫ x in Icc a b, ∫ y in Icc c d, u (complexCoordinates (x,y)) := by
  have hp := complexCoordinates_rect_preserving a b c d
  have hemb : MeasurableEmbedding complexCoordinates := by
    simpa only [funext complexCoordinates_eq] using Complex.measurableEquivRealProd.symm.measurableEmbedding
  rw [← hp.integral_comp hemb]
  exact integral_prod _ ((hp.integrable_comp hu.aestronglyMeasurable).mpr hu)

lemma fullOpenStrip_isOpen : IsOpen fullOpenStrip :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

lemma cartesianRectangle_ae_strip (a b : ℝ) :
    cartesianRectangle a b 0 Real.pi ≤ᵐ[volume] fullOpenStrip := by
  have hf (c : ℝ) : volume {z : ℂ | z.im = c} = 0 := by
    have hh := Complex.volume_preserving_equiv_real_prod.measure_preimage
      (MeasurableSet.univ.prod (measurableSet_singleton c)).nullMeasurableSet
    simpa [Set.preimage,Measure.volume_eq_prod,Measure.prod_prod] using hh
  have h0 : ∀ᵐ z : ℂ ∂volume, z.im ≠ 0 := by
    simpa only [ae_iff,not_not] using hf 0
  have hp : ∀ᵐ z : ℂ ∂volume, z.im ≠ Real.pi := by
    simpa only [ae_iff,not_not] using hf Real.pi
  filter_upwards [h0,hp] with z hz0 hzp hzQ
  exact ⟨lt_of_le_of_ne hzQ.2.2.1 hz0.symm,lt_of_le_of_ne hzQ.2.2.2 hzp⟩

lemma cartesianRectangle_volume (a b c d : ℝ) :
    volume (cartesianRectangle a b c d) = ENNReal.ofReal (b-a)*ENNReal.ofReal (d-c) := by
  rw [cartesianRectangle_preimage,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet,
    Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]

lemma unitSlab_norm_integral_le {u : ℂ → ℝ} {a : ℝ}
    (hg : MemLp (gradient u) 2 (volume.restrict (cartesianRectangle a (a+1) 0 Real.pi))) :
    (∫ z in cartesianRectangle a (a+1) 0 Real.pi, ‖gradient u z‖) ≤
      Real.sqrt (Real.pi * ∫ z in cartesianRectangle a (a+1) 0 Real.pi, ‖gradient u z‖^2) := by
  let Q := cartesianRectangle a (a+1) 0 Real.pi
  have hv : volume Q = ENNReal.ofReal Real.pi := by
    simp [Q,cartesianRectangle_volume]
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by simp [hv]⟩
  have hconst : MemLp (fun _ : ℂ => (1:ℝ)) 2 (volume.restrict Q) := memLp_const 1
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := volume.restrict Q) (f := fun z => ‖gradient u z‖) (g := fun _ => (1:ℝ))
    (Eventually.of_forall fun z => norm_nonneg _) (Eventually.of_forall fun _ => zero_le_one)
    (by simpa using hg.norm) (by simpa using hconst)
  simp only [mul_one,Real.rpow_two,← Real.sqrt_eq_rpow,one_pow,integral_const,
    Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,hv,ENNReal.toReal_ofReal Real.pi_pos.le] at hh
  simpa only [Real.sqrt_mul Real.pi_pos.le,mul_comm] using hh

lemma vertical_derivative_bound_ae {u : ℂ → ℝ} (hu : LocallyLipschitzOn fullOpenStrip u) :
    ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume, y ∈ Ioo 0 Real.pi →
      ‖deriv (fun t : ℝ => u (complexCoordinates (x,t))) y‖ ≤
        ‖gradient u (complexCoordinates (x,y))‖ := by
  have hd := locallyLipschitz_ae_differentiable fullOpenStrip_isOpen hu
  have hp := complexCoordinates_preserving.quasiMeasurePreserving.tendsto_ae.eventually hd
  rw [Measure.volume_eq_prod] at hp
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with x hx
  filter_upwards [hx] with y hy hyI
  apply vertical_deriv_norm_le
  apply hy
  simpa [fullOpenStrip,complexCoordinates] using hyI

lemma negativeSlab_mean_le {u : ℂ → ℝ}
    (hu : ContinuousOn u fullClosedStrip) (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hz : ∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (complexCoordinates (x,y)) = 0)
    {a : ℝ} (ha : a+1 ≤ 0) :
    Real.pi⁻¹*(∫ z in cartesianRectangle a (a+1) 0 Real.pi, u z) ≤
      Real.sqrt (Real.pi * ∫ z in cartesianRectangle a (a+1) 0 Real.pi, ‖gradient u z‖^2) := by
  let Q := cartesianRectangle a (a+1) 0 Real.pi
  have hQ : Q ⊆ fullClosedStrip := fun _ h => h.2.2
  have hgQ : MemLp (gradient u) 2 (volume.restrict Q) :=
    hg.mono_measure (Measure.restrict_mono_ae (cartesianRectangle_ae_strip a (a+1)))
  have hv : volume Q < ⊤ := (cartesianRectangle_compact a (a+1) 0 Real.pi).measure_lt_top
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by simpa using hv⟩
  have hgI : IntegrableOn (fun z => ‖gradient u z‖) Q := (hgQ.integrable (by norm_num)).norm
  have huI : IntegrableOn u Q := (hu.mono hQ).integrableOn_compact (cartesianRectangle_compact _ _ _ _)
  have hp := complexCoordinates_rect_preserving a (a+1) 0 Real.pi
  have hgp := (hp.integrable_comp hgI.aestronglyMeasurable).mpr hgI
  have hup := (hp.integrable_comp huI.aestronglyMeasurable).mpr huI
  have hder := vertical_derivative_bound_ae hl
  have hslice : ∀ᵐ x ∂volume.restrict (Icc a (a+1)),
      (∫ y in Icc 0 Real.pi, u (complexCoordinates (x,y))) ≤
        Real.pi * ∫ y in Icc 0 Real.pi, ‖gradient u (complexCoordinates (x,y))‖ := by
    filter_upwards [ae_restrict_of_ae hder,hgp.prod_right_ae,ae_restrict_mem measurableSet_Icc] with x hdx hgx hx
    have hcont : ContinuousOn (fun y => u (complexCoordinates (x,y))) (Icc 0 Real.pi) :=
      hu.comp (vertical_isometry x).continuous.continuousOn (by
        intro y hy; simpa [fullClosedStrip,complexCoordinates] using hy)
    have hlip : LocallyLipschitzOn (Ioo 0 Real.pi) (fun y => u (complexCoordinates (x,y))) :=
      locallyLipschitz_comp_of_isometry fullOpenStrip_isOpen hl (vertical_isometry x) (by
        intro y hy; simpa [fullOpenStrip,complexCoordinates] using hy)
    obtain ⟨y0,hy0,huy0⟩ := hz x (hx.2.trans ha)
    have hosc := slice_oscillation_le_integral Real.pi_pos hcont hlip hgx
      (fun _ _ => norm_nonneg _) hdx
    have hpoint (y : ℝ) (hy : y ∈ Icc 0 Real.pi) :
        u (complexCoordinates (x,y)) ≤ ∫ t in Icc 0 Real.pi, ‖gradient u (complexCoordinates (x,t))‖ := by
      have hh := hosc y hy y0 hy0
      rw [huy0,sub_zero,Real.norm_eq_abs] at hh
      exact (le_abs_self _).trans hh
    have hci : IntegrableOn (fun _ : ℝ => ∫ t in Icc 0 Real.pi, ‖gradient u (complexCoordinates (x,t))‖) (Icc 0 Real.pi) := continuousOn_const.integrableOn_Icc
    have hh := setIntegral_mono_on hcont.integrableOn_Icc hci measurableSet_Icc hpoint
    simpa [integral_const,Real.volume_Icc,Real.pi_pos.le] using hh
  have htotal := integral_mono_ae hup.integral_prod_left
    (hgp.integral_prod_left.const_mul Real.pi) hslice
  rw [integral_const_mul] at htotal
  have huEq := cartesianRectangle_integral huI
  have hgEq := cartesianRectangle_integral hgI
  change (∫ z in Q,u z) = _ at huEq
  change (∫ z in Q,‖gradient u z‖) = _ at hgEq
  simp only [Function.comp_def] at htotal
  rw [← huEq,← hgEq] at htotal
  calc
    Real.pi⁻¹*(∫ z in Q,u z) ≤ ∫ z in Q,‖gradient u z‖ := by
      have hh := mul_le_mul_of_nonneg_left htotal (inv_nonneg.mpr Real.pi_pos.le)
      simpa [← mul_assoc,Real.pi_pos.ne'] using hh
    _ ≤ _ := unitSlab_norm_integral_le hgQ

lemma interval_unit_mean_comparison {f g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : ContinuousOn f (Icc (-1) (a+1)))
    (hl : LocallyLipschitzOn (Ioo (-1) (a+1)) f)
    (hg : IntegrableOn g (Icc (-1) (a+1))) (hgn : ∀ t ∈ Icc (-1) (a+1), 0 ≤ g t)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo (-1) (a+1) → ‖deriv f t‖ ≤ g t) :
    (∫ t in Icc a (a+1), f t) ≤ (∫ t in Icc (-1) 0, f t) + ∫ t in Icc (-1) (a+1), g t := by
  have hA : Icc a (a+1) ⊆ Icc (-1) (a+1) := by
    intro t ht; exact ⟨by linarith [ht.1],ht.2⟩
  have hB : Icc (-1:ℝ) 0 ⊆ Icc (-1) (a+1) := by
    intro t ht; exact ⟨ht.1,by linarith [ht.2]⟩
  have hffA := (hf.mono hA).integrableOn_Icc (μ := volume)
  have hffB := (hf.mono hB).integrableOn_Icc (μ := volume)
  have hosc := slice_oscillation_le_integral (by linarith : (-1:ℝ)<a+1) hf hl hg hgn hd
  let B := ∫ t in Icc (-1) (a+1),g t
  have hpt (x : ℝ) (hx : x ∈ Icc a (a+1)) (y : ℝ) (hy : y ∈ Icc (-1:ℝ) 0) : f x ≤ f y+B := by
    have hh := hosc x (hA hx) y (hB hy)
    have hh' := (le_abs_self (f x-f y)).trans (by simpa [Real.norm_eq_abs] using hh)
    dsimp [B]
    linarith
  have hxpt (x : ℝ) (hx : x ∈ Icc a (a+1)) : f x ≤ (∫ t in Icc (-1) 0,f t)+B := by
    have hc : IntegrableOn (fun _ : ℝ => f x) (Icc (-1) 0) := continuousOn_const.integrableOn_Icc
    have hh := setIntegral_mono_on hc (hffB.add (continuousOn_const.integrableOn_Icc))
      measurableSet_Icc (hpt x hx)
    simpa [integral_add hffB continuousOn_const.integrableOn_Icc,integral_const,Real.volume_Icc] using hh
  have hc : IntegrableOn (fun _ : ℝ => (∫ t in Icc (-1) 0,f t)+B) (Icc a (a+1)) :=
    continuousOn_const.integrableOn_Icc
  have hh := setIntegral_mono_on hffA hc measurableSet_Icc hxpt
  simpa [integral_const,Real.volume_Icc] using hh

lemma cartesianRectangle_integral_symm {a b c d : ℝ} {u : ℂ → ℝ}
    (hu : IntegrableOn u (cartesianRectangle a b c d)) :
    (∫ z in cartesianRectangle a b c d, u z) =
      ∫ y in Icc c d, ∫ x in Icc a b, u (complexCoordinates (x,y)) := by
  have hp := complexCoordinates_rect_preserving a b c d
  have hemb : MeasurableEmbedding complexCoordinates := by
    simpa only [funext complexCoordinates_eq] using Complex.measurableEquivRealProd.symm.measurableEmbedding
  rw [← hp.integral_comp hemb]
  exact integral_prod_symm _ ((hp.integrable_comp hu.aestronglyMeasurable).mpr hu)

lemma horizontal_derivative_bound_ae {u : ℂ → ℝ} (hu : LocallyLipschitzOn fullOpenStrip u) :
    ∀ᵐ y : ℝ ∂volume, y ∈ Ioo 0 Real.pi → ∀ᵐ x : ℝ ∂volume,
      ‖deriv (fun t : ℝ => u (complexCoordinates (t,y))) x‖ ≤
        ‖gradient u (complexCoordinates (x,y))‖ := by
  have hd := locallyLipschitz_ae_differentiable fullOpenStrip_isOpen hu
  have hp := complexCoordinates_preserving.quasiMeasurePreserving.tendsto_ae.eventually hd
  rw [Measure.volume_eq_prod] at hp
  have hs := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).quasiMeasurePreserving.tendsto_ae.eventually hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with y hy hyI
  filter_upwards [hy] with x hx
  apply horizontal_deriv_norm_le
  apply hx
  simpa [fullOpenStrip,complexCoordinates] using hyI

lemma slab_integral_comparison {u : ℂ → ℝ}
    (hu : ContinuousOn u fullClosedStrip) (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip)) {a : ℝ} (ha : 0 ≤ a) :
    (∫ z in cartesianRectangle a (a+1) 0 Real.pi,u z) ≤
      (∫ z in cartesianRectangle (-1) 0 0 Real.pi,u z) +
      ∫ z in cartesianRectangle (-1) (a+1) 0 Real.pi, ‖gradient u z‖ := by
  let R := cartesianRectangle (-1) (a+1) 0 Real.pi
  have hR : R ⊆ fullClosedStrip := fun _ h => h.2.2
  have huI : IntegrableOn u R := (hu.mono hR).integrableOn_compact (cartesianRectangle_compact _ _ _ _)
  have huA : IntegrableOn u (cartesianRectangle a (a+1) 0 Real.pi) :=
    (hu.mono (fun _ h => h.2.2)).integrableOn_compact (cartesianRectangle_compact _ _ _ _)
  have huB : IntegrableOn u (cartesianRectangle (-1) 0 0 Real.pi) :=
    (hu.mono (fun _ h => h.2.2)).integrableOn_compact (cartesianRectangle_compact _ _ _ _)
  have hgR : MemLp (gradient u) 2 (volume.restrict R) :=
    hg.mono_measure (Measure.restrict_mono_ae (cartesianRectangle_ae_strip (-1) (a+1)))
  let : IsFiniteMeasure (volume.restrict R) :=
    ⟨by simpa using (cartesianRectangle_compact (-1) (a+1) 0 Real.pi).measure_lt_top⟩
  have hgI : IntegrableOn (fun z => ‖gradient u z‖) R := (hgR.integrable (by norm_num)).norm
  have hpR := complexCoordinates_rect_preserving (-1) (a+1) 0 Real.pi
  have hpA := complexCoordinates_rect_preserving a (a+1) 0 Real.pi
  have hpB := complexCoordinates_rect_preserving (-1) 0 0 Real.pi
  have hgp := (hpR.integrable_comp hgI.aestronglyMeasurable).mpr hgI
  have hupA := (hpA.integrable_comp huA.aestronglyMeasurable).mpr huA
  have hupB := (hpB.integrable_comp huB.aestronglyMeasurable).mpr huB
  have hder := horizontal_derivative_bound_ae hl
  have hY : ∀ᵐ y : ℝ ∂volume.restrict (Icc 0 Real.pi), y ∈ Ioo 0 Real.pi := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (0:ℝ)),
      ae_restrict_of_ae (volume.ae_ne Real.pi)] with y hy hy0 hyp
    exact ⟨lt_of_le_of_ne hy.1 hy0.symm,lt_of_le_of_ne hy.2 hyp⟩
  have hslice : ∀ᵐ y ∂volume.restrict (Icc 0 Real.pi),
      (∫ x in Icc a (a+1), u (complexCoordinates (x,y))) ≤
        (∫ x in Icc (-1) 0, u (complexCoordinates (x,y)))+
          ∫ x in Icc (-1) (a+1), ‖gradient u (complexCoordinates (x,y))‖ := by
    filter_upwards [ae_restrict_of_ae hder,hgp.prod_left_ae,hY] with y hdy hgy hy
    have hcont : ContinuousOn (fun x => u (complexCoordinates (x,y))) (Icc (-1) (a+1)) :=
      hu.comp (horizontal_isometry y).continuous.continuousOn (by
        intro x _; simpa [fullClosedStrip,complexCoordinates] using And.intro hy.1.le hy.2.le)
    have hlip : LocallyLipschitzOn (Ioo (-1) (a+1)) (fun x => u (complexCoordinates (x,y))) :=
      locallyLipschitz_comp_of_isometry fullOpenStrip_isOpen hl (horizontal_isometry y) (by
        intro x _; simpa [fullOpenStrip,complexCoordinates] using hy)
    exact interval_unit_mean_comparison ha hcont hlip hgy (fun _ _ => norm_nonneg _)
      ((hdy hy).mono fun _ h _ => h)
  have hh := integral_mono_ae hupA.integral_prod_right
    (hupB.integral_prod_right.add hgp.integral_prod_right) hslice
  simp only [Pi.add_apply] at hh
  rw [integral_add hupB.integral_prod_right hgp.integral_prod_right] at hh
  simp only [Function.comp_def] at hh
  rwa [← cartesianRectangle_integral_symm huA,← cartesianRectangle_integral_symm huB,
    ← cartesianRectangle_integral_symm hgI] at hh

lemma rectangle_energy_le_total {u : ℂ → ℝ}
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip)) (a b : ℝ) :
    (∫ z in cartesianRectangle a b 0 Real.pi, ‖gradient u z‖^2) ≤
      ∫ z in fullOpenStrip, ‖gradient u z‖^2 := by
  exact integral_mono_measure
    (Measure.restrict_mono_ae (cartesianRectangle_ae_strip a b))
    (Eventually.of_forall fun _ => sq_nonneg _) hg.norm.integrable_sq

lemma rectangle_norm_integral_le {u : ℂ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : MemLp (gradient u) 2 (volume.restrict (cartesianRectangle a b 0 Real.pi))) :
    (∫ z in cartesianRectangle a b 0 Real.pi, ‖gradient u z‖) ≤
      Real.sqrt ((b-a)*Real.pi * ∫ z in cartesianRectangle a b 0 Real.pi, ‖gradient u z‖^2) := by
  let Q := cartesianRectangle a b 0 Real.pi
  have harea : 0 ≤ (b-a)*Real.pi := mul_nonneg (sub_nonneg.mpr hab) Real.pi_pos.le
  have hv : volume Q = ENNReal.ofReal ((b-a)*Real.pi) := by
    simp [Q,cartesianRectangle_volume,ENNReal.ofReal_mul (sub_nonneg.mpr hab)]
  let : IsFiniteMeasure (volume.restrict Q) := ⟨by simp [hv]⟩
  have hconst : MemLp (fun _ : ℂ => (1:ℝ)) 2 (volume.restrict Q) := memLp_const 1
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := volume.restrict Q) (f := fun z => ‖gradient u z‖) (g := fun _ => (1:ℝ))
    (Eventually.of_forall fun z => norm_nonneg _) (Eventually.of_forall fun _ => zero_le_one)
    (by simpa using hg.norm) (by simpa using hconst)
  simp only [mul_one,Real.rpow_two,← Real.sqrt_eq_rpow,one_pow,integral_const,
    Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,hv,ENNReal.toReal_ofReal harea] at hh
  rw [Real.sqrt_mul harea]
  simpa only [Q,mul_comm] using hh

lemma negativeSlab_mean_small {u : ℂ → ℝ} {H a : ℝ} (hH : 1024 ≤ H)
    (hu : ContinuousOn u fullClosedStrip) (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hE : (∫ z in fullOpenStrip, ‖gradient u z‖^2) ≤ 2*Real.pi*H)
    (hz : ∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (complexCoordinates (x,y)) = 0)
    (ha : a+1 ≤ 0) :
    Real.pi⁻¹*(∫ z in cartesianRectangle a (a+1) 0 Real.pi, u z) ≤ H/4 := by
  apply (negativeSlab_mean_le hu hl hg hz ha).trans
  have hEq := (rectangle_energy_le_total hg a (a+1)).trans hE
  apply (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hEq Real.pi_pos.le)).trans
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith
  · have hp := Real.pi_lt_four
    have hps : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos]
    have hHn : 0 ≤ H := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hps hHn, mul_nonneg hHn (show 0 ≤ H-512 by linarith)]

lemma positiveSlab_mean_small {u : ℂ → ℝ} {H a : ℝ} (hH : 1024 ≤ H)
    (hu : ContinuousOn u fullClosedStrip) (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hE : (∫ z in fullOpenStrip, ‖gradient u z‖^2) ≤ 2*Real.pi*H)
    (hz : ∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (complexCoordinates (x,y)) = 0)
    (ha : 0 ≤ a) (haH : a ≤ H/128) :
    Real.pi⁻¹*(∫ z in cartesianRectangle a (a+1) 0 Real.pi, u z) ≤ H/2 := by
  have hh := mul_le_mul_of_nonneg_left (slab_integral_comparison hu hl hg ha)
    (inv_nonneg.mpr Real.pi_pos.le)
  have hm := negativeSlab_mean_small hH hu hl hg hE hz (a := -1) (by norm_num)
  have hgR := hg.mono_measure (Measure.restrict_mono_ae (cartesianRectangle_ae_strip (-1) (a+1)))
  have hn := rectangle_norm_integral_le (by linarith : (-1:ℝ) ≤ a+1) hgR
  have hER := (rectangle_energy_le_total hg (-1) (a+1)).trans hE
  have hn' : (∫ z in cartesianRectangle (-1) (a+1) 0 Real.pi, ‖gradient u z‖) ≤ Real.pi*H/4 := by
    apply hn.trans
    apply (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hER
      (mul_nonneg (by linarith) Real.pi_pos.le))).trans
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hHn : 0 ≤ H := by linarith
      have hbase : 2*(a+2)*H ≤ H^2/16 := by
        nlinarith [mul_nonneg hHn (show 0 ≤ H-128 by linarith),
          mul_le_mul_of_nonneg_right haH hHn]
      nlinarith [mul_le_mul_of_nonneg_right hbase (sq_nonneg Real.pi)]
  have hn'' := mul_le_mul_of_nonneg_left hn' (inv_nonneg.mpr Real.pi_pos.le)
  have he : Real.pi⁻¹*(Real.pi*H/4) = H/4 := by field_simp
  rw [he] at hn''
  simp only [mul_add] at hh
  norm_num at hm
  linarith

theorem sourceSlabSmallMean : SourceSlabSmallMeanTarget := by
  refine ⟨1/128,1024,by norm_num,by norm_num,?_⟩
  intro H hH u hu hl hg hE hz j hj
  have hz' : ∀ x : ℝ, x ≤ 0 → ∃ y ∈ Icc (0:ℝ) Real.pi, u (complexCoordinates (x,y)) = 0 := hz
  by_cases hj0 : j < 0
  · exact (negativeSlab_mean_small hH hu hl hg hE hz' (a := (j:ℝ))
      (by have hh : (j:ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
          linarith)).trans (by linarith)
  · apply positiveSlab_mean_small hH hu hl hg hE hz'
    · exact_mod_cast (by omega : 0 ≤ j)
    · linarith

lemma complex_re_fiber_null (a : ℝ) : volume {z : ℂ | z.re = a} = 0 := by
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton a).prod MeasurableSet.univ).nullMeasurableSet
  simpa [Set.preimage,Measure.volume_eq_prod,Measure.prod_prod] using he

lemma complex_im_fiber_null (a : ℝ) : volume {z : ℂ | z.im = a} = 0 := by
  have he := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton a)).nullMeasurableSet
  simpa [Set.preimage,Measure.volume_eq_prod,Measure.prod_prod] using he

lemma closedIntegerStrip_ae_open (j : ℤ) : closedIntegerStrip j =ᵐ[volume] openIntegerStrip j := by
  have hr0 : ∀ᵐ z : ℂ ∂volume, z.re ≠ (j:ℝ) := by
    simpa only [ae_iff,not_not] using complex_re_fiber_null (j:ℝ)
  have hr1 : ∀ᵐ z : ℂ ∂volume, z.re ≠ (j:ℝ)+1 := by
    simpa only [ae_iff,not_not] using complex_re_fiber_null ((j:ℝ)+1)
  have hi0 : ∀ᵐ z : ℂ ∂volume, z.im ≠ 0 := by
    simpa only [ae_iff,not_not] using complex_im_fiber_null 0
  have hi1 : ∀ᵐ z : ℂ ∂volume, z.im ≠ Real.pi := by
    simpa only [ae_iff,not_not] using complex_im_fiber_null Real.pi
  filter_upwards [hr0,hr1,hi0,hi1] with z hz0 hz1 hw0 hw1
  apply propext
  change ((j:ℝ) ≤ z.re ∧ z.re ≤ (j:ℝ)+1 ∧ 0 ≤ z.im ∧ z.im ≤ Real.pi) ↔
    ((j:ℝ) < z.re ∧ z.re < (j:ℝ)+1 ∧ 0 < z.im ∧ z.im < Real.pi)
  constructor
  · rintro ⟨h0,h1,h2,h3⟩
    exact ⟨lt_of_le_of_ne h0 hz0.symm,lt_of_le_of_ne h1 hz1,
      lt_of_le_of_ne h2 hw0.symm,lt_of_le_of_ne h3 hw1⟩
  · rintro ⟨h0,h1,h2,h3⟩; exact ⟨h0.le,h1.le,h2.le,h3.le⟩

lemma openIntegerStrip_isOpen (j : ℤ) : IsOpen (openIntegerStrip j) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

lemma openIntegerStrip_disjoint : Pairwise (fun i j => Disjoint (openIntegerStrip i) (openIntegerStrip j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro z hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    exact (not_lt_of_ge (hi.2.1.le.trans hle)) hj.1
  · have hle : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    exact (not_lt_of_ge (hj.2.1.le.trans hle)) hi.1

lemma slabShift_continuous (j : ℤ) : Continuous (slabShift j) := by
  unfold slabShift
  fun_prop

lemma slabShift_isometry (j : ℤ) : Isometry (slabShift j) :=
  (IsometryEquiv.addLeft (j:ℂ)).isometry

lemma slabShift_preimage_closed (j : ℤ) : slabShift j ⁻¹' closedIntegerStrip j =
    cartesianRectangle 0 1 0 Real.pi := by
  ext z
  simp only [slabShift,closedIntegerStrip,cartesianRectangle,mem_preimage,mem_ofPred_eq,
    Complex.add_re,Complex.add_im,Complex.intCast_re,Complex.intCast_im,zero_add]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> exact ⟨by linarith,by linarith,h3,h4⟩

lemma slabShift_preimage_open (j : ℤ) : slabShift j ⁻¹' openIntegerStrip j = openUnitStrip := by
  ext z
  simp only [slabShift,openIntegerStrip,openUnitStrip,mem_preimage,mem_ofPred_eq,
    Complex.add_re,Complex.add_im,Complex.intCast_re,Complex.intCast_im,zero_add]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> exact ⟨by linarith,by linarith,h3,h4⟩

lemma slabShift_preserving_open (j : ℤ) : MeasurePreserving (slabShift j)
    (volume.restrict openUnitStrip) (volume.restrict (openIntegerStrip j)) := by
  have hh := (measurePreserving_add_left (volume : Measure ℂ) (j:ℂ)).restrict_preimage
    (openIntegerStrip_isOpen j).measurableSet
  change MeasurePreserving (slabShift j) (volume.restrict (slabShift j ⁻¹' openIntegerStrip j)) _ at hh
  rwa [slabShift_preimage_open] at hh

lemma slabShift_preserving_closed (j : ℤ) : MeasurePreserving (slabShift j)
    (volume.restrict (cartesianRectangle 0 1 0 Real.pi)) (volume.restrict (closedIntegerStrip j)) := by
  have hm : MeasurableSet (closedIntegerStrip j) := cartesianRectangle_measurable _ _ _ _
  have hh := (measurePreserving_add_left (volume : Measure ℂ) (j:ℂ)).restrict_preimage hm
  change MeasurePreserving (slabShift j) (volume.restrict (slabShift j ⁻¹' closedIntegerStrip j)) _ at hh
  rwa [slabShift_preimage_closed] at hh

lemma gradient_comp_slabShift (u : ℂ → ℝ) (j : ℤ) (z : ℂ) :
    gradient (u ∘ slabShift j) z = gradient u (slabShift j z) := by
  simp only [gradient,Function.comp_def,slabShift,fderiv_comp_add_left]

lemma slabShift_integral (u : ℂ → ℝ) (j : ℤ) :
    (∫ z in cartesianRectangle 0 1 0 Real.pi,u (slabShift j z)) =
      ∫ z in closedIntegerStrip j,u z :=
  (slabShift_preserving_closed j).integral_comp (IsometryEquiv.addLeft (j:ℂ)).toHomeomorph.measurableEmbedding u

lemma slabShift_energy (u : ℂ → ℝ) (j : ℤ) :
    stripDirichletEnergy (gradient (u ∘ slabShift j)) =
      ∫ z in closedIntegerStrip j,‖gradient u z‖^2 := by
  simp only [stripDirichletEnergy,gradient_comp_slabShift]
  rw [(slabShift_preserving_open j).integral_comp (IsometryEquiv.addLeft (j:ℂ)).toHomeomorph.measurableEmbedding (fun z => ‖gradient u z‖^2)]
  exact (setIntegral_congr_set (closedIntegerStrip_ae_open j)).symm

lemma slabShift_mem_strip (j : ℤ) {z : ℂ} (hz : z ∈ openUnitStrip) :
    slabShift j z ∈ fullOpenStrip := by
  simpa [slabShift,fullOpenStrip] using hz.2.2

lemma slabShift_locallyLipschitz {u : ℂ → ℝ}
    (hl : LocallyLipschitzOn fullOpenStrip u) (j : ℤ) :
    LocallyLipschitzOn openUnitStrip (u ∘ slabShift j) := by
  intro z hz
  obtain ⟨K,t,ht,hK⟩ := hl (slabShift_mem_strip j hz)
  rw [nhdsWithin_eq_nhds.mpr (fullOpenStrip_isOpen.mem_nhds (slabShift_mem_strip j hz))] at ht
  refine ⟨K,slabShift j ⁻¹' t,mem_nhdsWithin_of_mem_nhds
    ((slabShift_continuous j).continuousAt.preimage_mem_nhds ht),?_⟩
  intro x hx y hy
  exact (hK hx hy).trans_eq (by rw [(slabShift_isometry j).edist_eq])

lemma slabShift_gradient_memLp {u : ℂ → ℝ}
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip)) (j : ℤ) :
    MemLp (gradient (u ∘ slabShift j)) 2 (volume.restrict openUnitStrip) := by
  have hs : openIntegerStrip j ⊆ fullOpenStrip := fun _ hz => hz.2.2
  have hh := (hg.mono_measure (Measure.restrict_mono hs le_rfl)).comp_measurePreserving
    (slabShift_preserving_open j)
  have he : gradient (u ∘ slabShift j) = gradient u ∘ slabShift j := funext (gradient_comp_slabShift u j)
  rw [he]
  exact hh

lemma slabShift_source_weakGradient {u : ℂ → ℝ} {H : ℝ}
    (hc : ContinuousOn u fullClosedStrip)
    (hl : LocallyLipschitzOn fullOpenStrip u)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hb : ∀ z, 0 ≤ u z ∧ u z ≤ H) (j : ℤ) :
    SourceIsStripWeakGradient (u ∘ slabShift j) (gradient (u ∘ slabShift j)) := by
  apply locallyLipschitz_source_weakGradient (slabShift_locallyLipschitz hl j) _ (slabShift_gradient_memLp hg j)
  have hcont : ContinuousOn (u ∘ slabShift j) openUnitStrip :=
    hc.comp (slabShift_continuous j).continuousOn (fun z hz =>
      ⟨(slabShift_mem_strip j hz).1.le,(slabShift_mem_strip j hz).2.le⟩)
  exact memLp_of_bounded (Eventually.of_forall fun z => hb (slabShift j z))
    (hcont.aestronglyMeasurable openUnitStrip_isOpen.measurableSet) 2

lemma integerSlab_energy_budget {u : ℂ → ℝ} {H : ℝ}
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hE : (∫ z in fullOpenStrip, ‖gradient u z‖^2) ≤ 2*Real.pi*H) :
    (∑' j : ℤ, ENNReal.ofReal (∫ z in closedIntegerStrip j, ‖gradient u z‖^2)) ≤
      ENNReal.ofReal (2*Real.pi*H) := by
  have hint := hg.norm.integrable_sq
  have hsub (j : ℤ) : openIntegerStrip j ⊆ fullOpenStrip := fun _ hz => hz.2.2
  have hconv (j : ℤ) : ENNReal.ofReal (∫ z in closedIntegerStrip j, ‖gradient u z‖^2) =
      ∫⁻ z in openIntegerStrip j, ENNReal.ofReal (‖gradient u z‖^2) := by
    rw [setIntegral_congr_set (closedIntegerStrip_ae_open j)]
    exact ofReal_integral_eq_lintegral_ofReal (hint.mono_measure (Measure.restrict_mono (hsub j) le_rfl))
      (Eventually.of_forall fun z => sq_nonneg _)
  simp_rw [hconv]
  rw [← lintegral_iUnion (fun j => (openIntegerStrip_isOpen j).measurableSet) openIntegerStrip_disjoint]
  calc
    _ ≤ ∫⁻ z in fullOpenStrip, ENNReal.ofReal (‖gradient u z‖^2) :=
      lintegral_mono_set (iUnion_subset hsub)
    _ = ENNReal.ofReal (∫ z in fullOpenStrip, ‖gradient u z‖^2) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z => sq_nonneg _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hE

lemma abstract_slab_exponential_budget {E : ℤ → ℝ} {H C c : ℝ}
    (hH : 0 < H) (hEn : ∀ j, 0 ≤ E j)
    (hEs : (∑' j : ℤ, ENNReal.ofReal (E j)) ≤ ENNReal.ofReal (2*Real.pi*H))
    (hC : 0 ≤ C) (hc : 0 < c) :
    (∑' j : ℤ, ENNReal.ofReal (C*(E j/H^2)*Real.exp (-c*H^2/E j))) ≤
      ENNReal.ofReal ((2*Real.pi*C/H)*Real.exp (-c*H/(2*Real.pi))) := by
  have hv : 0 ≤ 2*Real.pi*H := by positivity
  have hE (j : ℤ) : E j ≤ 2*Real.pi*H := by
    exact (ENNReal.ofReal_le_ofReal_iff hv).mp ((ENNReal.le_tsum j).trans hEs)
  let K := C/H^2*Real.exp (-c*H/(2*Real.pi))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht (j : ℤ) : C*(E j/H^2)*Real.exp (-c*H^2/E j) ≤ E j*K := by
    by_cases hz : E j = 0
    · simp [hz]
    · have hj : 0 < E j := lt_of_le_of_ne (hEn j) (Ne.symm hz)
      have hb : H/(2*Real.pi) ≤ H^2/E j := by
        apply (le_div_iff₀ hj).mpr
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
        nlinarith [mul_le_mul_of_nonneg_left (hE j) hH.le]
      have hex : Real.exp (-c*H^2/E j) ≤ Real.exp (-c*H/(2*Real.pi)) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hb hc.le
        calc
          -c*H^2/E j = -(c*(H^2/E j)) := by ring
          _ ≤ -(c*(H/(2*Real.pi))) := neg_le_neg hh
          _ = -c*H/(2*Real.pi) := by ring
      calc
        _ ≤ C*(E j/H^2)*Real.exp (-c*H/(2*Real.pi)) :=
          mul_le_mul_of_nonneg_left hex (mul_nonneg hC (div_nonneg hj.le (sq_nonneg _)))
        _ = _ := by dsimp [K]; ring
  calc
    _ ≤ ∑' j : ℤ, ENNReal.ofReal (E j*K) := ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (ht j)
    _ = (∑' j : ℤ, ENNReal.ofReal (E j))*ENNReal.ofReal K := by
      calc
        _ = ∑' j : ℤ, ENNReal.ofReal (E j)*ENNReal.ofReal K :=
          tsum_congr (fun j => ENNReal.ofReal_mul (hEn j))
        _ = _ := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (2*Real.pi*H)*ENNReal.ofReal K := by gcongr
    _ = ENNReal.ofReal ((2*Real.pi*C/H)*Real.exp (-c*H/(2*Real.pi))) := by
      rw [← ENNReal.ofReal_mul hv]
      congr 1
      dsimp [K]
      field_simp [hH.ne']



lemma stripRectangle_zero_eq_cartesian :
    stripRectangle 0 0 1 = cartesianRectangle 0 1 0 Real.pi := by
  ext z
  simp [stripRectangle,cartesianRectangle]

lemma slabShift_average (u : ℂ → ℝ) (j : ℤ) :
    spatialAverage (u ∘ slabShift j) (stripRectangle 0 0 1) =
      Real.pi⁻¹ * ∫ z in closedIntegerStrip j, u z := by
  rw [spatialAverage,stripRectangle_volume]
  simp only [mul_one,ENNReal.ofReal_one,one_mul,ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [stripRectangle_zero_eq_cartesian]
  simp only [Function.comp_apply]
  rw [slabShift_integral,div_eq_mul_inv,mul_comm]

lemma slabShift_dyadic (j : ℤ) (k : ℕ) (i m : Fin (2^k)) :
    slabShift j ⁻¹' dyadicStripRectangle j k i m = dyadicStripRectangle 0 k i m := by
  ext z
  simp only [dyadicStripRectangle,stripRectangle,slabShift,mem_preimage,mem_ofPred_eq,
    Complex.add_re,Complex.add_im,Complex.intCast_re,Complex.intCast_im,zero_add,Int.cast_zero]
  constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> exact ⟨by linarith,by linarith,h3,h4⟩

lemma slabShift_continuousOn {u : ℂ → ℝ}
    (hu : ContinuousOn u fullClosedStrip) (j : ℤ) :
    ContinuousOn (u ∘ slabShift j) (stripRectangle 0 0 1) := by
  apply hu.comp (slabShift_continuous j).continuousOn
  intro z hz
  change 0 ≤ (slabShift j z).im ∧ (slabShift j z).im ≤ Real.pi
  simpa [slabShift,stripRectangle] using hz.2.2

lemma point_integer_slab (z : ℂ) (hz : 0 ≤ z.im ∧ z.im ≤ Real.pi) :
    ∃ w ∈ stripRectangle 0 0 1, slabShift ⌊z.re⌋ w = z := by
  refine ⟨z-(⌊z.re⌋:ℂ),?_,by simp [slabShift]⟩
  have h0 := Int.floor_le z.re
  have h1 := Int.lt_floor_add_one z.re
  simp only [stripRectangle,mem_ofPred_eq,Complex.sub_re,Complex.intCast_re,
    Complex.sub_im,Complex.intCast_im,sub_zero,zero_add,mul_one]
  exact ⟨by linarith,by linarith,hz.1,hz.2⟩

lemma slab_energy_le_total {u : ℂ → ℝ} {H : ℝ}
    (hH : 0 < H)
    (hg : MemLp (gradient u) 2 (volume.restrict fullOpenStrip))
    (hE : (∫ z in fullOpenStrip, ‖gradient u z‖^2) ≤ 2*Real.pi*H) (j : ℤ) :
    (∫ z in closedIntegerStrip j, ‖gradient u z‖^2) ≤ 2*Real.pi*H := by
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    ((ENNReal.le_tsum j).trans (integerSlab_energy_budget hg hE))

 theorem sourceStripLocalization : SourceStripLocalizationTarget := by
  intro C0 α hC0 hα
  obtain ⟨C,c,c0,hC,hc,hc0,hrect⟩ := sourceStripRectangleEnergy C0 α hC0 hα
  obtain ⟨b,Hm,hb,hHm,hmean⟩ := sourceSlabSmallMean
  refine ⟨b,2*Real.pi*C,c/(2*Real.pi),max Hm (max 1 (2*Real.pi/c0)),hb,
    by positivity,by positivity,lt_of_lt_of_le hHm (le_max_left _ _),?_⟩
  intro H hH u hu hl huB hg hE hz Ω mΩ P hP X hhit
  let := hP
  have hHm' : Hm ≤ H := (le_max_left _ _).trans hH
  have hH1 : 1 ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith
  have hHc : 2*Real.pi/c0 ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  let E : ℤ → ℝ := fun j => ∫ z in closedIntegerStrip j, ‖gradient u z‖^2
  let A : ℤ → Set Ω := fun j =>
    {xi | (j:ℝ) ≤ b*H ∧ ((slabShift j ⁻¹' X xi) ∩
      {z | z ∈ stripRectangle 0 0 1 ∧ (u ∘ slabShift j) z = H}).Nonempty}
  have hEn (j : ℤ) : 0 ≤ E j := integral_nonneg fun z => sq_nonneg _
  have hEj (j : ℤ) : E j ≤ 2*Real.pi*H := slab_energy_le_total hH0 hg hE j
  have hsmall (j : ℤ) : E j ≤ c0*H^2 := by
    have hhc := (div_le_iff₀ hc0).mp hHc
    exact (hEj j).trans (by nlinarith [mul_le_mul_of_nonneg_right hhc hH0.le])
  have hA (j : ℤ) : P (A j) ≤ ENNReal.ofReal (C*(E j/H^2)*Real.exp (-c*H^2/E j)) := by
    by_cases hj : (j:ℝ) ≤ b*H
    · have ht (k : ℕ) (i m : Fin (2^k)) :
          P {xi | ((slabShift j ⁻¹' X xi) ∩ dyadicStripRectangle 0 k i m).Nonempty} ≤
            ENNReal.ofReal (C0*(2:ℝ)^(-α*(k:ℝ))) := by
        apply (measure_mono ?_).trans (hhit j k i m)
        rintro xi ⟨z,hzX,hzQ⟩
        exact ⟨slabShift j z,hzX,by rwa [← slabShift_dyadic j k i m] at hzQ⟩
      have hm : spatialAverage (u ∘ slabShift j) (stripRectangle 0 0 1) ≤ H/2 := by
        rw [slabShift_average]
        exact hmean H hHm' u hu hl hg hE hz j hj
      have hh := hrect H hH0 (u ∘ slabShift j) (gradient (u ∘ slabShift j))
        (slabShift_source_weakGradient hu hl hg huB j) (slabShift_continuousOn hu j)
        (fun z _ => huB (slabShift j z)) hm Ω mΩ P hP (fun xi => slabShift j ⁻¹' X xi) ht
        (by rw [slabShift_energy]; exact hsmall j)
      rw [slabShift_energy] at hh
      apply (measure_mono ?_).trans hh
      exact fun xi hxi => hxi.2
    · have he : A j = ∅ := by ext xi; simp [A,hj]
      rw [he,measure_empty]
      exact bot_le
  have hcover : {xi | ∃ z ∈ X xi, 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*H ∧ u z = H} ⊆
      ⋃ j : ℤ, A j := by
    rintro xi ⟨z,hzX,hz0,hzπ,hzr,hzu⟩
    obtain ⟨w,hw,heq⟩ := point_integer_slab z ⟨hz0,hzπ⟩
    apply mem_iUnion.mpr
    refine ⟨⌊z.re⌋,⟨(Int.floor_le z.re).trans hzr,?_⟩⟩
    exact ⟨w,by simpa only [mem_preimage,heq] using hzX,hw,by simpa [Function.comp_def,heq] using hzu⟩
  calc
    _ ≤ P (⋃ j : ℤ, A j) := measure_mono hcover
    _ ≤ ∑' j : ℤ, P (A j) := measure_iUnion_le _
    _ ≤ ∑' j : ℤ, ENNReal.ofReal (C*(E j/H^2)*Real.exp (-c*H^2/E j)) := ENNReal.tsum_le_tsum hA
    _ ≤ ENNReal.ofReal ((2*Real.pi*C/H)*Real.exp (-c*H/(2*Real.pi))) :=
      abstract_slab_exponential_budget hH0 hEn (integerSlab_energy_budget hg hE) hC.le hc
    _ ≤ ENNReal.ofReal (2*Real.pi*C*Real.exp (-(c/(2*Real.pi))*H)) := by
      apply ENNReal.ofReal_le_ofReal
      have ht : 2*Real.pi*C/H ≤ 2*Real.pi*C := div_le_self (by positivity) hH1
      have he : -c*H/(2*Real.pi) = -(c/(2*Real.pi))*H := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le

end SLEExactGauge
end

 
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StripProbabilities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strip Probabilities for chordal SLE. -/

section
section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators NNReal
namespace SLEExactGauge
theorem comparison_path_strip_zero {η : ℝ → ℂ} {T : ℝ}
    (hT : 0 < T) (hη : ContinuousOn η (Icc 0 T)) (hstart : η 0 = 0)
    (hend : ‖η T‖ = 1) (hupper : ∀ t ∈ Icc 0 T, 0 ≤ (η t).im)
    (Fbar : ℂ → OnePoint ℂ) (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H)
    (himage : ∀ t ∈ Icc 0 T, ∃ w : ℂ, Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r)
    (v : ℝ) (hv : v ≤ 0) :
    ∃ φ : ℝ, φ ∈ Icc 0 Real.pi ∧
      sphericalTruncatedLog q r H (Fbar (Complex.exp ((v : ℂ)+(φ : ℂ)*Complex.I))) = 0 := by
  have her : Real.exp v ∈ Icc ‖η 0‖ ‖η T‖ := by
    rw [hstart,norm_zero,hend]
    exact ⟨(Real.exp_pos v).le,by simpa using Real.exp_le_exp.mpr hv⟩
  obtain ⟨t,ht,htr⟩ := intermediate_value_Icc hT.le hη.norm her
  change ‖η t‖ = Real.exp v at htr
  have hn : η t ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [htr]
    exact (Real.exp_pos v).ne'
  let φ := (η t).arg
  have hφ : φ ∈ Icc 0 Real.pi :=
    ⟨Complex.arg_nonneg_iff.mpr (hupper t ht),Complex.arg_le_pi _⟩
  have he : (v : ℂ)+(φ : ℂ)*Complex.I = Complex.log (η t) := by
    apply Complex.ext
    · simp [Complex.log_re,htr]
    · simp [Complex.log_im,φ]
  refine ⟨φ,hφ,?_⟩
  rw [he,Complex.exp_log hn]
  obtain ⟨w,hw,hwr⟩ := himage t ht
  rw [hw,sphericalTruncatedLog_coe]
  exact truncatedConformalLog_eq_zero hr hH.le hwr

end SLEExactGauge
end

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
lemma source_strip_log_locallyLipschitz {F : ℂ → ℂ} {Fbar : ℂ → OnePoint ℂ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hext : ∀ z : ℂ, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (q : ℂ) (r H : ℝ) (hr : 0 < r) (hH : 0 < H) :
    LocallyLipschitzOn fullOpenStrip (fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z))) := by
  let U := fun z : ℂ => sphericalTruncatedLog q r H (Fbar (Complex.exp z))
  let V := truncatedConformalLog (F ∘ Complex.exp) q r H
  have heq : EqOn U V fullOpenStrip := by
    intro z hz
    dsimp [U]
    rw [hext (Complex.exp z) (exp_strip_halfplane hz),sphericalTruncatedLog_coe]
    rfl
  have hcomp : DifferentiableOn ℂ (F ∘ Complex.exp) fullOpenStrip :=
    hF.comp Complex.differentiable_exp.differentiableOn exp_strip_halfplane
  intro z hz
  obtain ⟨K,S,hS,hzS,hK⟩ := truncated_log_lipschitz_near fullOpenStrip_isOpen hcomp hz q hr hH
  refine ⟨K,S ∩ fullOpenStrip,mem_nhdsWithin_of_mem_nhds ((hS.inter fullOpenStrip_isOpen).mem_nhds ⟨hzS,hz⟩),?_⟩
  intro x hx y hy
  change edist (U x) (U y) ≤ (K : ℝ≥0∞)*edist x y
  rw [heq hx.2,heq hy.2]
  exact hK hx.1 hy.1



universe u

lemma beforeFirstModulus_norm_le {γ : ℝ≥0 → ℂ} (hc : Continuous γ) (h0 : γ 0 = 0)
    {A : ℝ} (hA : 0 < A) {t : ℝ≥0} (ht : BeforeFirstModulus γ A t) :
    ‖γ t‖ ≤ A := by
  by_cases ht0 : t = 0
  · simp [ht0,h0,hA.le]
  have htpos : 0 < t := bot_lt_iff_ne_bot.mpr ht0
  have hcl : t ∈ closure (Iio t : Set ℝ≥0) := by
    rw [closure_Iio' (show (Iio t : Set ℝ≥0).Nonempty from ⟨0,htpos⟩)]
    exact (show t ≤ t from le_rfl)
  have hclosed : IsClosed {s : ℝ≥0 | ‖γ s‖ ≤ A} := isClosed_le hc.norm continuous_const
  exact (closure_minimal (fun s hs => (ht s hs).le) hclosed) hcl

lemma sphericalTruncatedLog_eq_height_of_notin_ball (q : ℂ) (r H : ℝ) (hr : 0 < r)
    (x : OnePoint ℂ)
    (hx : x ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (Real.exp H*r)) :
    sphericalTruncatedLog q r H x = H := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
    rw [sphericalTruncatedLog_coe]
    apply truncatedConformalLog_eq_height hr
    apply le_of_not_gt
    intro h
    apply hx
    exact ⟨z,by simpa [Metric.mem_ball,dist_eq_norm] using h,rfl⟩

lemma escape_forces_strip_level {γ : ℝ≥0 → ℂ} (hc : Continuous γ) (h0 : γ 0 = 0)
    (hupper : ∀ t, 0 ≤ (γ t).im)
    (Fbar : ℂ → OnePoint ℂ) (q : ℂ) {r L H b : ℝ} (hr : 0 < r) (hL : 1 < L)
    (hH : H = Real.log L)
    (hstart : ∃ w : ℂ, Fbar 0 = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r)
    (t : ℝ≥0) (ht : BeforeFirstModulus γ (L^b) t)
    (hbad : Fbar (γ t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)) :
    ∃ z : ℂ, Complex.exp z ∈ range γ ∧ 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*H ∧
      sphericalTruncatedLog q r H (Fbar (Complex.exp z)) = H := by
  have hLp : 0 < L := by linarith
  have hnorm := beforeFirstModulus_norm_le hc h0 (Real.rpow_pos_of_pos hLp b) ht
  have hn : γ t ≠ 0 := by
    intro heq
    rw [heq] at hbad
    obtain ⟨w,hw,hwr⟩ := hstart
    apply hbad
    exact ⟨w,by rw [Metric.mem_ball,dist_eq_norm]; nlinarith,hw.symm⟩
  refine ⟨Complex.log (γ t),by rw [Complex.exp_log hn]; exact mem_range_self t,?_,?_,?_,?_⟩
  · simpa only [Complex.log_im] using Complex.arg_nonneg_iff.mpr (hupper t)
  · simpa only [Complex.log_im] using Complex.arg_le_pi (γ t)
  · rw [Complex.log_re,hH]
    exact (Real.log_le_log (norm_pos_iff.mpr hn) hnorm).trans_eq (Real.log_rpow hLp b)
  · rw [Complex.exp_log hn]
    apply sphericalTruncatedLog_eq_height_of_notin_ball q r H hr
    simpa only [hH,Real.exp_log hLp] using hbad

theorem sourceUniformConformalLocalization : SourceUniformConformalLocalizationTarget := by
  intro κ hκ hκ8
  obtain ⟨C0,α,hC0,hα,hhit⟩ := ordinary_sle_strip_hitting_constants κ hκ hκ8
  obtain ⟨b,C,c,H0,hb,hC,hc,hH0,hstrip⟩ := sourceStripLocalization C0 α hC0 hα
  refine ⟨b,C,c,Real.exp (max H0 1),hb,hC,hc,?_,?_⟩
  · exact Real.one_lt_exp_iff.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  intro Ω mΩ P hP γ hγ F Fbar hF hi hbar hext q r hr η T hT hη hs he hu him L hL
  let := hP
  have hL1 : 1 < L := (Real.one_lt_exp_iff.mpr
    (lt_of_lt_of_le zero_lt_one (le_max_right H0 1))).trans_le hL
  have hLp : 0 < L := by linarith
  have hlog : max H0 1 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have hHH : H0 ≤ Real.log L := (le_max_left _ _).trans hlog
  have hHp : 0 < Real.log L := hH0.trans_le hHH
  let U := fun z : ℂ => sphericalTruncatedLog q r (Real.log L) (Fbar (Complex.exp z))
  let X := fun xi : Ω => Complex.exp ⁻¹' range (γ xi)
  obtain ⟨hcU,hbU,-,hgU,hEU⟩ := source_strip_log_regularity hF hi hbar hext q r (Real.log L) hr hHp
  have hzero (v : ℝ) (hv : v ≤ 0) : ∃ y ∈ Icc (0:ℝ) Real.pi, U (v+y*Complex.I) = 0 :=
    comparison_path_strip_zero hT hη hs he hu Fbar q r (Real.log L) hr hHp him v hv
  have hhits (j : ℤ) (k : ℕ) (i m : Fin (2^k)) :
      P {xi | (X xi ∩ dyadicStripRectangle j k i m).Nonempty} ≤
        ENNReal.ofReal (C0*(2:ℝ)^(-α*(k:ℝ))) := by
    apply (measure_mono ?_).trans (hhit γ hγ j k i m)
    rintro xi ⟨z,⟨t,ht⟩,hz⟩
    exact ⟨t,z,hz,ht.symm⟩
  have hh := hstrip (Real.log L) hHH U hcU
    (source_strip_log_locallyLipschitz hF hext q r (Real.log L) hr hHp)
    hbU hgU hEU hzero Ω mΩ P hP X hhits
  have hstart : ∃ w : ℂ, Fbar 0 = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r := by
    simpa only [hs] using him 0 ⟨le_rfl,hT.le⟩
  obtain ⟨B,hB,htrace⟩ := hγ.2
  have hsub : {xi | ∃ t : ℝ≥0, BeforeFirstModulus (γ xi) (L^b) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ≤ᵐ[P]
      {xi | ∃ z ∈ X xi, 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*Real.log L ∧ U z = Real.log L} := by
    filter_upwards [htrace] with xi hxi
    obtain ⟨G,Fw,hFw⟩ := hxi
    rintro ⟨t,ht,hbad⟩
    exact escape_forces_strip_level hFw.1 hFw.2.1 hFw.2.2.1 Fbar q hr hL1 rfl hstart t ht hbad
  calc
    _ ≤ P {xi | ∃ z ∈ X xi, 0 ≤ z.im ∧ z.im ≤ Real.pi ∧ z.re ≤ b*Real.log L ∧ U z = Real.log L} :=
      measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (C*Real.exp (-c*Real.log L)) := hh
    _ = ENNReal.ofReal (C*L^(-c)) := by
      rw [Real.rpow_def_of_pos hLp]
      congr 2
      congr 1
      ring

end SLEExactGauge

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem ordinary_survival_bound_regular
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 4 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (R : ℝ) (hR : 0 < R)
    (hN : greenLogNormSq κ (initialLogCoordinates z) 0 ≤ R^2)
    (T : ℝ≥0) (b : ℝ) (hb : 0 < b)
    (hbR : b ≤ Real.exp (((κ-4)/(2*κ))*Real.log R))
    (hbT : b ≤ (((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) * T) :
    P {ω | z ∈ survivingDomain (γ ω) T} ≤
      ENNReal.ofReal (swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8)
        (initialLogCoordinates z) 0 / b) := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let q₀ := initialLogCoordinates z
  let lo (n : ℕ) : ℝ := q₀.1.im-(n:ℝ)-1
  have hlo (n : ℕ) : lo n ≤ q₀.1.im := by dsimp [lo]; have := Nat.cast_nonneg (α := ℝ) n; linarith
  let c (n : ℕ) := Classical.choice
    (exists_clippedLogSolution B hm hBm hBc κ (lo n) q₀.1.im (hlo n) q₀)
  let a (n : ℕ) : RadialLocalization (c n) R T := Classical.choice
    (exists_radialLocalization hBc hB0 (c n) R T hN (hlo n))
  let E (n : ℕ) : Set Ω := {ω | (a n).τ ω = T ∨
    greenLogNormSq κ ((c n).Q ((a n).τ ω) ω) (B ((a n).τ ω) ω) = R^2}
  have hprob (n : ℕ) : P (E n) ≤
      ENNReal.ofReal (swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8) q₀ 0 / b) :=
    (a n).exit_probability hB hBm hBc hκ hR le_rfl b hb hbR hbT
  have hsub : {ω | z ∈ survivingDomain (γ ω) T} ≤ᵐ[P]
      {ω | ∀ᶠ n : ℕ in atTop, ω ∈ E n} := by
    filter_upwards [hw] with ω hω
    intro hlive
    obtain ⟨N, hN⟩ := exists_nat_gt (q₀.1.im-Real.log (G ω T z).im)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hlt : lo n < Real.log (G ω T z).im := by
      have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
      dsimp [lo]
      linarith
    exact (a n).alive_forces_radial_or_time_boundary hBc hz rfl le_rfl ω
      (γ ω) (G ω) (F ω) hω hlive hlt
  exact (measure_mono_ae hsub).trans (measure_eventually_sets_le P E _ hprob)

theorem ordinary_survival_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 4 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (R : ℝ) (hR : 0 < R)
    (hN : greenLogNormSq κ (initialLogCoordinates z) 0 ≤ R^2)
    (T : ℝ≥0) (b : ℝ) (hb : 0 < b)
    (hbR : b ≤ Real.exp (((κ-4)/(2*κ))*Real.log R))
    (hbT : b ≤ (((κ-4)/(2*κ))*((κ-4)/4)*Real.exp ((((κ-4)/(2*κ))-2)*Real.log R)) * T) :
    P {ω | z ∈ survivingDomain (γ ω) T} ≤
      ENNReal.ofReal (swallowLyapunov κ ((κ-4)/(2*κ)) (3*(κ-4)/8)
        (initialLogCoordinates z) 0 / b) := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw,hCB] with ω hω he
    simpa only [he] using hω
  exact ordinary_survival_bound_regular hC hCm hCc hC0 κ hκ γ G F hwC
    z hz R hR hN T b hb hbR hbT

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma greenLogNormSq_initial_norm (κ : ℝ) (z : ℂ) (hz : 0 < z.im) :
    greenLogNormSq κ (initialLogCoordinates z) 0 = ‖z‖^2 := by
  have he : Real.exp (2 * Real.log z.im) = z.im ^ 2 := by
    rw [show 2 * Real.log z.im = Real.log z.im + Real.log z.im by ring,
      Real.exp_add, Real.exp_log hz, pow_two]
  rw [← Complex.normSq_eq_norm_sq]
  simp only [greenLogNormSq, initialLogCoordinates, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_self, add_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, he,
      Complex.normSq_apply, pow_two]

theorem ordinary_survival_radial_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 4 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (hunit : ‖z‖ = 1)
    (R : ℝ) (hR : 1 ≤ R) :
    P {ω | z ∈ survivingDomain (γ ω) ((R^2).toNNReal)} ≤
      ENNReal.ofReal ((1+3*(κ-4)/8) / min 1 (((κ-4)/(2*κ))*((κ-4)/4)) *
        Real.exp (-((κ-4)/(2*κ))*Real.log R)) := by
  let β := (κ-4)/(2*κ)
  let C := 3*(κ-4)/8
  let d := β*((κ-4)/4)
  let m := min 1 d
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hm : 0 < m := lt_min (by norm_num) hd
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hN : greenLogNormSq κ (initialLogCoordinates z) 0 ≤ R^2 := by
    rw [greenLogNormSq_initial_norm κ z hz, hunit]
    nlinarith
  have hN1 : greenLogNormSq κ (initialLogCoordinates z) 0 ≤ (1:ℝ)^2 := by
    rw [greenLogNormSq_initial_norm κ z hz, hunit]
  have hF : swallowLyapunov κ β C (initialLogCoordinates z) 0 ≤ 1+C := by
    have hr := radialLogPower_le κ β hβ.le (initialLogCoordinates z) 0 1 (by norm_num) hN1
    have hy := heightLogPower_le κ β hβ.le (initialLogCoordinates z) 0 1 (by norm_num) hN1
    simp only [Real.log_one, mul_zero, Real.exp_zero] at hr hy
    exact (add_le_add hr (mul_le_mul_of_nonneg_left hy hC)).trans_eq (by ring)
  have he : Real.exp ((β-2)*Real.log R)*R^2 = Real.exp (β*Real.log R) := by
    have hh : R^2 = Real.exp (2*Real.log R) := by
      rw [show 2*Real.log R = Real.log R+Real.log R by ring, Real.exp_add,Real.exp_log hR0,pow_two]
    rw [hh,← Real.exp_add]
    congr 1
    ring
  have hbR : m*Real.exp (β*Real.log R) ≤ Real.exp (β*Real.log R) := by
    exact mul_le_of_le_one_left (Real.exp_pos _).le (min_le_left _ _)
  have hbT : m*Real.exp (β*Real.log R) ≤ d*Real.exp ((β-2)*Real.log R)*((R^2).toNNReal:ℝ) := by
    rw [Real.coe_toNNReal _ (sq_nonneg R),mul_assoc,he]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
  have hb : 0 < m*Real.exp (β*Real.log R) := mul_pos hm (Real.exp_pos _)
  have hp := ordinary_survival_bound hB κ hκ γ G F hw z hz R hR0 hN
    ((R^2).toNNReal) (m*Real.exp (β*Real.log R)) hb hbR hbT
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    swallowLyapunov κ β C (initialLogCoordinates z) 0/(m*Real.exp (β*Real.log R))
        ≤ (1+C)/(m*Real.exp (β*Real.log R)) := div_le_div_of_nonneg_right hF hb.le
    _ = (1+C)/m*Real.exp (-β*Real.log R) := by
      rw [show -β*Real.log R = -(β*Real.log R) by ring, Real.exp_neg]
      ring



end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma linear_subsolution_initial_nonpos (T : ℝ) (hT : 0 ≤ T)
    (f a g : ℝ → ℝ) (ha : ContinuousOn a (Icc 0 T))
    (hf : ∀ u ∈ Icc 0 T, HasDerivWithinAt f (g u) (Icc 0 T) u)
    (hg : ∀ u ∈ Icc 0 T, a u*f u ≤ g u) (hfT : f T ≤ 0) : f 0 ≤ 0 := by
  let A (u : ℝ) := a (projIcc 0 T hT u)
  have hA : Continuous A := ha.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun u => (projIcc 0 T hT u).property)
  have hAa (u : ℝ) (hu : u ∈ Icc 0 T) : A u = a u := by simp only [A,projIcc_of_mem hT hu]
  let I (u : ℝ) := ∫ v in (0:ℝ)..u, A v
  have hI (u : ℝ) : HasDerivAt I (A u) u :=
    intervalIntegral.integral_hasDerivAt_right (hA.intervalIntegrable _ _)
      hA.aestronglyMeasurable.stronglyMeasurableAtFilter hA.continuousAt
  have hd (u : ℝ) (hu : u ∈ Icc 0 T) :
      HasDerivWithinAt (fun v => f v*Real.exp (-I v))
        ((g u-a u*f u)*Real.exp (-I u)) (Icc 0 T) u := by
    convert (hf u hu).mul ((hI u).neg.exp.hasDerivWithinAt) using 1
    all_goals first | rfl | (simp only [Pi.neg_apply]; rw [hAa u hu]; ring) | (rw [hAa u hu]; ring)
  have hmono : MonotoneOn (fun v => f v*Real.exp (-I v)) (Icc 0 T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun u hu => (hd u hu).continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).mono interior_subset)
      (fun u hu => mul_nonneg (sub_nonneg.mpr (hg u (interior_subset hu))) (Real.exp_pos _).le)
  have hh := hmono (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) ⟨hT,le_rfl⟩ hT
  simp only [I,intervalIntegral.integral_same,neg_zero,Real.exp_zero,mul_one] at hh
  exact hh.trans (mul_nonpos_of_nonpos_of_nonneg hfT (Real.exp_pos _).le)

lemma IsCapacityTwoWitness.real_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
    HasDerivWithinAt (fun v : ℝ => (G v.toNNReal z).re)
      (2*((G u.toNNReal z).re-U u.toNNReal)/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)))
      (Icc 0 (T:ℝ)) u := by
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt u (h.time_derivative T z hz u hu)
  simpa [Function.comp_def,Complex.div_re] using hh

lemma IsCapacityTwoWitness.initial_real_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (M : ℝ)
    (hbound : ∀ u : ℝ≥0, u ≤ T → U u ≤ M) (hend : (G T z).re ≤ M) : z.re ≤ M := by
  let a (u : ℝ) := 2/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))
  have hnorm : ContinuousOn (fun u : ℝ => Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))) (Icc 0 (T:ℝ)) :=
    Complex.continuous_normSq.comp_continuousOn ((h.time_continuousOn T z hz).sub
      (Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)).continuousOn)
  have hne (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
      Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (h.centered_ne_zero u.toNNReal z
      (survivingDomain_antitone γ (Real.toNNReal_le_iff_le_coe.mpr hu.2) hz))).ne'
  have ha : ContinuousOn a (Icc 0 (T:ℝ)) := continuousOn_const.div hnorm hne
  have hh := linear_subsolution_initial_nonpos T T.coe_nonneg
    (fun u => (G u.toNNReal z).re-M) a
    (fun u => 2*((G u.toNNReal z).re-U u.toNNReal)/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))) ha
    (fun u hu => (h.real_derivative T z hz u hu).sub_const M)
    (fun u hu => by
      dsimp only [a]
      have hb := hbound u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)
      have hp : 0 ≤ Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) := Complex.normSq_nonneg _
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith) hp)
    (by simpa only [Real.toNNReal_coe] using sub_nonpos.mpr hend)
  simpa only [Real.toNNReal_zero,h.initial_value z hz.1.1,sub_nonpos] using hh

lemma IsCapacityTwoWitness.initial_real_ge
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) (M : ℝ)
    (hbound : ∀ u : ℝ≥0, u ≤ T → M ≤ U u) (hend : M ≤ (G T z).re) : M ≤ z.re := by
  let a (u : ℝ) := 2/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))
  have hnorm : ContinuousOn (fun u : ℝ => Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ))) (Icc 0 (T:ℝ)) :=
    Complex.continuous_normSq.comp_continuousOn ((h.time_continuousOn T z hz).sub
      (Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)).continuousOn)
  have hne (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
      Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) ≠ 0 := by
    exact (Complex.normSq_pos.mpr (h.centered_ne_zero u.toNNReal z
      (survivingDomain_antitone γ (Real.toNNReal_le_iff_le_coe.mpr hu.2) hz))).ne'
  have ha : ContinuousOn a (Icc 0 (T:ℝ)) := continuousOn_const.div hnorm hne
  have hh := linear_subsolution_initial_nonpos T T.coe_nonneg
    (fun u => M-(G u.toNNReal z).re) a
    (fun u => -(2*((G u.toNNReal z).re-U u.toNNReal)/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)))) ha
    (fun u hu => (h.real_derivative T z hz u hu).const_sub M)
    (fun u hu => by
      dsimp only [a]
      have hb := hbound u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)
      have hp : 0 ≤ Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) := Complex.normSq_nonneg _
      rw [div_mul_eq_mul_div,← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hp)
    (by simpa only [Real.toNNReal_coe] using sub_nonpos.mpr hend)
  simpa only [Real.toNNReal_zero,h.initial_value z hz.1.1,sub_nonpos] using hh

lemma IsCapacityTwoWitness.initial_imag_square_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) : z.im^2 ≤ (G T z).im^2+4*T := by
  have hd (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :=
    ((h.imag_derivative T z hz u hu).pow 2).add ((hasDerivWithinAt_id u (Icc 0 (T:ℝ))).const_mul 4)
  have hnonneg (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
      0 ≤ (2:ℝ)*(G u.toNNReal z).im^(2-1)*
        (-2*(G u.toNNReal z).im/Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)))+1*4 := by
    have hp := Complex.normSq_pos.mpr (h.centered_ne_zero u.toNNReal z
      (survivingDomain_antitone γ (Real.toNNReal_le_iff_le_coe.mpr hu.2) hz))
    have hn : (G u.toNNReal z).im^2 ≤ Complex.normSq (G u.toNNReal z-(U u.toNNReal:ℂ)) := by
      simp only [Complex.normSq_apply,Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,sub_zero]
      nlinarith [sq_nonneg ((G u.toNNReal z).re-U u.toNNReal)]
    norm_num only [Nat.reduceSub, pow_one, one_mul]
    field_simp
    nlinarith
  have hmono : MonotoneOn (fun u : ℝ => (G u.toNNReal z).im^2+4*u) (Icc 0 (T:ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun u hu => (hd u hu).continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).mono interior_subset)
      (fun u hu => by simpa only [Nat.cast_ofNat, mul_one, one_mul] using hnonneg u (interior_subset hu))
  have hh := hmono (show (0:ℝ) ∈ Icc 0 (T:ℝ) from ⟨le_rfl,T.coe_nonneg⟩)
    ⟨T.coe_nonneg,le_rfl⟩ T.coe_nonneg
  simpa only [Real.toNNReal_zero,Real.toNNReal_coe,h.initial_value z hz.1.1,mul_zero,add_zero] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsCapacityTwoWitness.trace_real_bounds
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (M : ℝ)
    (hbound : ∀ u : ℝ≥0, u ≤ T → |U u| ≤ M) : |(γ T).re| ≤ M := by
  have hh := h
  obtain ⟨_,_,_,_,_,_,hFmap,_,hinv,_,_,_,htip⟩ := hh
  have hm (y : ℝ) (hy : 0 < y) :
      |(F T ((U T:ℂ)+(y:ℂ)*Complex.I)).re| ≤ M := by
    have hyH : (U T:ℂ)+(y:ℂ)*Complex.I ∈ upperHalfPlane := by
      simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
        mul_zero, add_zero, zero_add] using hy
    have hz := hFmap T hyH
    have he := hinv T _ hyH
    apply abs_le.mpr
    constructor
    · apply IsCapacityTwoWitness.initial_real_ge hU h T _ hz (-M)
      · intro u hu; exact (abs_le.mp (hbound u hu)).1
      · rw [he]; simpa using (abs_le.mp (hbound T le_rfl)).1
    · apply IsCapacityTwoWitness.initial_real_le hU h T _ hz M
      · intro u hu; exact (abs_le.mp (hbound u hu)).2
      · rw [he]; simpa using (abs_le.mp (hbound T le_rfl)).2
  have ht := (continuous_abs.tendsto _).comp (Complex.continuous_re.tendsto _ |>.comp (htip T))
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun y hy => hm y hy)

lemma IsCapacityTwoWitness.trace_imag_square_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) : (γ T).im^2 ≤ 4*T := by
  have hh := h
  obtain ⟨_,_,_,_,_,_,hFmap,_,hinv,_,_,_,htip⟩ := hh
  have hm (y : ℝ) (hy : 0 < y) :
      (F T ((U T:ℂ)+(y:ℂ)*Complex.I)).im^2 ≤ y^2+4*T := by
    have hyH : (U T:ℂ)+(y:ℂ)*Complex.I ∈ upperHalfPlane := by
      simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
        mul_zero, add_zero, zero_add] using hy
    have hz := hFmap T hyH
    have he := hinv T _ hyH
    have hh := h.initial_imag_square_le T _ hz
    rw [he] at hh
    simpa using hh
  have ht := (Complex.continuous_im.tendsto _ |>.comp (htip T)).pow 2
  have hr : Tendsto (fun y : ℝ => y^2+4*(T:ℝ)) (𝓝[>] 0) (𝓝 (4*(T:ℝ))) := by
    simpa using (((tendsto_id : Tendsto (fun y : ℝ => y) (𝓝 (0:ℝ)) (𝓝 0)).pow 2).add_const (4*(T:ℝ))).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto ht hr (eventually_nhdsWithin_of_forall fun y hy => hm y hy)

lemma IsCapacityTwoWitness.trace_norm_square_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ u : ℝ≥0, u ≤ T → |U u| ≤ M) : ‖γ T‖^2 ≤ M^2+4*T := by
  have hr := h.trace_real_bounds hU T M hbound
  have hi := h.trace_imag_square_le T
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hs : (γ T).re^2 ≤ M^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr hr
  nlinarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma exists_compact_square_field (R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x, |x| ≤ R → φ (0,x) = x^2) ∧
      (∀ x, |x| ≤ R → iteratedDeriv 2 (fun y => φ (0,y)) x = 2) := by
  let b : ContDiffBump (0 : ℝ × ℝ) := ⟨R+1,R+2,by linarith,by linarith⟩
  let φ (p : ℝ × ℝ) := b p*p.2^2
  have hnear (x : ℝ) (hx : |x| ≤ R) : (fun y => φ (0,y)) =ᶠ[𝓝 x] (fun y => y^2) := by
    have hball : (0,x) ∈ Metric.ball (0:ℝ × ℝ) b.rIn := by
      simpa only [Metric.mem_ball,dist_zero_right,Prod.norm_def,norm_zero,Real.norm_eq_abs,
        max_eq_right (abs_nonneg x)] using (show |x| < R+1 by linarith)
    have he := (b.eventuallyEq_one_of_mem_ball hball).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto x)
    filter_upwards [he] with y hy
    change b (0,y) = 1 at hy
    simp only [φ,hy,one_mul]
  refine ⟨φ,b.contDiff.mul (contDiff_snd.pow 2),b.hasCompactSupport.mul_right,
    fun x hx => (hnear x hx).eq_of_nhds,?_⟩
  intro x hx
  rw [(hnear x hx).iteratedDeriv_eq 2,iteratedDeriv_pow]
  norm_num

lemma brownian_stopped_square
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (R : ℝ) (hR : 0 ≤ R) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hin : ∀ ω t, t ≤ τ ω → |B t ω| ≤ R) :
    Integrable (fun ω => (B (τ ω) ω)^2) P ∧
      (∫ ω, (B (τ ω) ω)^2 ∂P) = ∫ ω, (τ ω:ℝ) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨φ,hφ,hφc,he,h2⟩ := exists_compact_square_field R hR
  obtain ⟨K,hfield⟩ := compact_state_smooth_brownian_field B hm
    (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) 0 measurable_const (fun _ => measurable_const)
    (fun _ => LipschitzWith.const 0) measurable_const (by simp)
    (fun t ω ht => (hasDerivWithinAt_const t (Ici 0) (0:ℝ))) φ hφ hφc
  let F (t : ℝ≥0) (ω : Ω) (x : ℝ) := φ (0,x)
  let a (t : ℝ≥0) (ω : Ω) (x : ℝ) := fderiv ℝ φ (0,x) ((0:ℝ),0)
  have hg (ω : Ω) (u : ℝ) (hu : u ∈ Icc 0 (τ ω:ℝ)) : brownianFieldDrift B F a u ω = 1 := by
    have hi := hin ω u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)
    simp only [brownianFieldDrift,F,a,show ((0:ℝ),0) = (0:ℝ × ℝ) from rfl,map_zero,h2 _ hi]
    norm_num
  have hopt := brownian_time_field_stopped_dynkin hB hm hBm hBc K F a hfield τ hτ T hb
  have hτm := stopping_time_measurable_nnreal hτ
  have hBi : Integrable (fun ω => (B (τ ω) ω)^2) P := by
    apply Integrable.of_bound ((hBm.comp (hτm.prodMk measurable_id)).pow_const 2).aestronglyMeasurable (R^2)
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hh : (B (τ ω) ω)^2 ≤ R^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hin ω (τ ω) le_rfl)
      simpa only [Function.comp_def, id_eq] using hh
  refine ⟨hBi,?_⟩
  have hef : (fun ω => F (τ ω) ω (B (τ ω) ω)) = fun ω => (B (τ ω) ω)^2 :=
    funext fun ω => he _ (hin ω (τ ω) le_rfl)
  rw [hef] at hopt
  have h0 : (∫ ω, F 0 ω (B 0 ω) ∂P) = 0 := by
    have he0 : (fun ω => F 0 ω (B 0 ω)) =ᵐ[P] (fun _ => (0:ℝ)) := by
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      change φ (0,B 0 ω) = 0
      rw [hω,he 0 (by simpa using hR)]
      norm_num
    rw [integral_congr_ae he0,integral_zero]
  rw [h0,zero_add] at hopt
  rw [hopt]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    calc
      (∫ u in (0:ℝ)..(τ ω:ℝ), brownianFieldDrift B F a u ω) = ∫ _ in (0:ℝ)..(τ ω:ℝ), (1:ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact hg ω u (by simpa only [uIcc_of_le (τ ω).coe_nonneg] using hu)
      _ = (τ ω:ℝ) := by simp

end SLEExactGauge
end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_InteriorEntrance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior Entrance for chordal SLE. -/

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
lemma brownian_maximal_tail_regular
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (r : ℝ) (hr : 0 < r) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} ≤ ENNReal.ofReal ((T:ℝ)/r^2) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hDa : Adapted f (fun t ω => r-|B t ω|) := by
    intro t
    have ha := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted t
    let : MeasurableSpace Ω := f t
    exact measurable_const.sub ha.abs
  obtain ⟨τ,hτ,hb,hin,hpre,hat⟩ := first_margin_stopping f (fun t ω => r-|B t ω|)
    hDa (fun ω => continuous_const.sub (hBc ω).abs)
    (fun ω => by rw [hB0 ω, abs_zero,sub_zero]; exact hr.le) T
  have hsq := brownian_stopped_square hB hm hBm hBc r hr.le τ hτ T hb
    (fun ω t ht => sub_nonneg.mp (hin ω t ht))
  have hτi := bounded_nnreal_integrable (P := P) τ (stopping_time_measurable_nnreal hτ) T hb
  have hmean : (∫ ω, (B (τ ω) ω)^2 ∂P) ≤ (T:ℝ) := by
    rw [hsq.2]
    calc
      (∫ ω, (τ ω:ℝ) ∂P) ≤ ∫ _ : Ω, (T:ℝ) ∂P :=
        integral_mono hτi (integrable_const _) (fun ω => NNReal.coe_le_coe.mpr (hb ω))
      _ = (T:ℝ) := by simp
  apply (measure_mono (show {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|}
      ⊆ {ω | r^2 ≤ (B (τ ω) ω)^2} from ?_)).trans
    (nonnegative_integral_tail _ hsq.1 (fun _ => sq_nonneg _) _ (r^2) (sq_pos_of_pos hr) hmean)
  rintro ω ⟨t,ht,he⟩
  have hlt : τ ω < T := by
    by_contra hh
    have htτ : t ≤ τ ω := ht.trans (not_lt.mp hh)
    exact (not_lt_of_ge (sub_nonneg.mp (hin ω t htτ))) he
  have heq : |B (τ ω) ω| = r := by linarith [hat ω hlt]
  change r^2 ≤ (B (τ ω) ω)^2
  rw [← sq_abs (B (τ ω) ω),heq]

 
theorem brownian_maximal_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (r : ℝ) (hr : 0 < r) (T : ℝ≥0) :
    P {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} ≤ ENNReal.ofReal ((T:ℝ)/r^2) := by
  obtain ⟨C,hCm,hCc,hC0,hC,hCB⟩ := exists_regular_brownian_version hB
  have he : {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} =ᵐ[P]
      {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |C t ω|} := by
    filter_upwards [hCB] with ω hω
    change (∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|) = (∃ t : ℝ≥0, t ≤ T ∧ r < |C t ω|)
    simp only [hω]
  rw [measure_congr he]
  exact brownian_maximal_tail_regular hC hCm hCc hC0 r hr T

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

theorem ordinary_trace_excursion_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (A : ℝ) (hA : 16 ≤ A) :
    P {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ≤ ENNReal.ofReal (4*κ/A) := by
  obtain ⟨C,hCm,hCc,hC0,hC,hCB⟩ := exists_regular_brownian_version hB
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  let r := A/(2*Real.sqrt κ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hp := brownian_maximal_tail hC r hr A.toNNReal
  have hsub : {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ≤ᵐ[P]
      {ω | ∃ t : ℝ≥0, t ≤ A.toNNReal ∧ r < |C t ω|} := by
    filter_upwards [hw,hCB] with ω hω he
    have hwC : IsCapacityTwoWitness (fun t => Real.sqrt κ*C t ω) (γ ω) (G ω) (F ω) := by
      simpa only [he] using hω
    rintro ⟨t,ht,hn⟩
    by_contra hh
    have hb : ∀ u, u ≤ t → |Real.sqrt κ*C u ω| ≤ A/2 := by
      intro u hu
      have hl : |C u ω| ≤ r := le_of_not_gt (fun hh' => hh ⟨u,
        (by apply NNReal.coe_le_coe.mp; rw [Real.coe_toNNReal _ hA0.le]; exact (NNReal.coe_le_coe.mpr hu).trans ht),hh'⟩)
      rw [abs_mul,abs_of_pos hs]
      calc
        Real.sqrt κ*|C u ω| ≤ Real.sqrt κ*r := mul_le_mul_of_nonneg_left hl hs.le
        _ = A/2 := by dsimp [r]; field_simp
    have hg := hwC.trace_norm_square_le (continuous_const.mul (hCc ω)) t (A/2) (by positivity) hb
    have hns : A^2 ≤ ‖γ ω t‖^2 := (sq_le_sq₀ hA0.le (norm_nonneg _)).mpr hn
    nlinarith [sq_nonneg (A-16)]
  apply (measure_mono_ae hsub).trans
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  rw [Real.coe_toNNReal _ hA0.le]
  dsimp [r]
  have hs2 := Real.sq_sqrt hκ.le
  have hAe := ne_of_gt hA0
  have hse := ne_of_gt hs
  field_simp
  nlinarith

end SLEExactGauge
end


open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 
theorem ordinary_survival_constants
    (κ : ℝ) (hκ : 4 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {B : ℝ≥0 → Ω → ℝ}, IsBrownianReal B P →
      ∀ (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ),
      (∀ᵐ ω ∂P, IsCapacityTwoWitness
        (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) →
      ∀ z ∈ upperHalfPlane, ‖z‖ = 1 →
        ∀ T : ℝ≥0, 1 ≤ T →
        P {ω | z ∈ survivingDomain (γ ω) T} ≤ ENNReal.ofReal (C*(T:ℝ)^(-c)) := by
  let β := (κ-4)/(2*κ)
  let C := (1+3*(κ-4)/8) / min 1 (β*((κ-4)/4))
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  have hβ : 0 < β := by dsimp [β]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,β/2,hC,by positivity,?_⟩
  intro Ω _ P B hB γ G F hw z hz hu T hT
  have ht : 0 < (T:ℝ) := lt_of_lt_of_le (by norm_num) (NNReal.coe_le_coe.mpr hT)
  have hR : 1 ≤ Real.sqrt (T:ℝ) := (Real.le_sqrt (by norm_num) T.coe_nonneg).mpr (by simpa only [one_pow, NNReal.coe_one] using NNReal.coe_le_coe.mpr hT)
  have hp := ordinary_survival_radial_tail hB κ hκ γ G F hw z hz hu (Real.sqrt T) hR
  rw [Real.sq_sqrt T.coe_nonneg,Real.toNNReal_coe] at hp
  convert hp using 2
  all_goals try with_reducible_and_instances rfl
  rw [Real.rpow_def_of_pos ht,Real.log_sqrt ht.le]
  congr 2
  ring

theorem ordinary_pre_swallow_constants (κ : ℝ) (hκ : 4 < κ) :
    ∃ D c : ℝ, 0 < D ∧ 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {B : ℝ≥0 → Ω → ℝ}, IsBrownianReal B P →
      ∀ (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ),
      (∀ᵐ ω ∂P, IsCapacityTwoWitness
        (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) →
      ∀ z ∈ upperHalfPlane, ‖z‖ = 1 →
      ∀ A : ℝ, 2 ≤ A → P {ω | PreSwallowExcursion (γ ω) z A} ≤
        ENNReal.ofReal (D*A^(-c)) := by
  obtain ⟨C,c₀,hC,hc₀,hsurv⟩ := ordinary_survival_constants κ hκ
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  let c := min c₀ 1
  let D := C+4*κ+(16:ℝ)^c
  have hc : 0 < c := lt_min hc₀ (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,c,hD,hc,?_⟩
  intro Ω _ P B hB γ G F hw z hz hunit A hA
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hA1 : 1 ≤ A := le_trans (by norm_num) hA
  have hpow : 0 < A^(-c) := Real.rpow_pos_of_pos hA0 _
  by_cases hlarge : 16 ≤ A
  · have hsub : {ω | PreSwallowExcursion (γ ω) z A} ⊆
        {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ∪
        {ω | z ∈ survivingDomain (γ ω) A.toNNReal} := by
      rintro ω ⟨t,hn,hl⟩
      by_cases ht : (t:ℝ) ≤ A
      · exact Or.inl ⟨t,ht,hn⟩
      · exact Or.inr (hl A.toNNReal (by
          apply NNReal.coe_lt_coe.mp
          rw [Real.coe_toNNReal _ hA0.le]
          exact not_le.mp ht))
    have hT : (1:ℝ≥0) ≤ A.toNNReal := by
      apply NNReal.coe_le_coe.mp
      simpa only [Real.coe_toNNReal _ hA0.le, NNReal.coe_one] using hA1
    have hp₁ := ordinary_trace_excursion_tail hB κ hk γ G F hw A hlarge
    have hp₂ := hsurv hB γ G F hw z hz hunit A.toNNReal hT
    rw [Real.coe_toNNReal _ hA0.le] at hp₂
    have he₁ : A^(-1:ℝ) ≤ A^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_right _ _))
    have he₂ : A^(-c₀) ≤ A^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hA1 (neg_le_neg (min_le_left _ _))
    have hsum : 4*κ/A+C*A^(-c₀) ≤ D*A^(-c) := by
      calc
        _ = 4*κ*A^(-1:ℝ)+C*A^(-c₀) := by rw [Real.rpow_neg_one]; ring
        _ ≤ 4*κ*A^(-c)+C*A^(-c) := add_le_add
          (mul_le_mul_of_nonneg_left he₁ (by positivity))
          (mul_le_mul_of_nonneg_left he₂ hC.le)
        _ ≤ D*A^(-c) := by
          have hp16 : 0 ≤ (16:ℝ)^c := Real.rpow_nonneg (by norm_num) _
          dsimp [D]
          nlinarith
    calc
      _ ≤ P ({ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖} ∪
          {ω | z ∈ survivingDomain (γ ω) A.toNNReal}) := measure_mono hsub
      _ ≤ P {ω | ∃ t : ℝ≥0, (t:ℝ) ≤ A ∧ A ≤ ‖γ ω t‖}+
          P {ω | z ∈ survivingDomain (γ ω) A.toNNReal} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (4*κ/A)+ENNReal.ofReal (C*A^(-c₀)) := add_le_add hp₁ hp₂
      _ = ENNReal.ofReal (4*κ/A+C*A^(-c₀)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (D*A^(-c)) := ENNReal.ofReal_le_ofReal hsum
  · have hpowEq : A^c*A^(-c) = 1 := by rw [← Real.rpow_add hA0]; simp
    have h16 : A^c ≤ (16:ℝ)^c := Real.rpow_le_rpow hA0.le (not_le.mp hlarge).le hc.le
    have hD16 : (16:ℝ)^c ≤ D := by dsimp [D]; linarith
    have hbound : 1 ≤ D*A^(-c) := by
      rw [← hpowEq]
      exact mul_le_mul_of_nonneg_right (h16.trans hD16) hpow.le
    exact prob_le_one.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hbound)

 

lemma mapped_live_exit_split (γ : ℝ≥0 → ℂ) (Fbar : ℂ → OnePoint ℂ)
    (z q : ℂ) (A R : ℝ)
    (h : ∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧
      Fbar (γ t) ∉ (fun w : ℂ => (w : OnePoint ℂ)) '' Metric.ball q R) :
    (∃ t : ℝ≥0, BeforeFirstModulus γ A t ∧
      Fbar (γ t) ∉ (fun w : ℂ => (w : OnePoint ℂ)) '' Metric.ball q R) ∨
      PreSwallowExcursion γ z A := by
  classical
  obtain ⟨t,hl,hout⟩ := h
  by_cases hp : BeforeFirstModulus γ A t
  · exact Or.inl ⟨t,hp,hout⟩
  · simp only [BeforeFirstModulus,not_forall,not_lt] at hp
    obtain ⟨s,hst,hs⟩ := hp
    exact Or.inr ⟨s,hs,fun u hu => survivingDomain_antitone γ (hu.trans hst).le hl⟩

universe u


theorem sourceChartedDiskRule : SourceChartedDiskRuleTarget := by
  intro κ hκ hκ8
  have hk : 0 < κ := lt_trans (by norm_num) hκ
  obtain ⟨b,C₁,c₁,L₀,hb,hC₁,hc₁,hL₀,hloc⟩ := sourceUniformConformalLocalization κ hk hκ8
  obtain ⟨C₂,c₂,hC₂,hc₂,hsw⟩ := ordinary_pre_swallow_constants κ hκ
  let c : ℝ := min c₁ (b*c₂)
  let L₁ : ℝ := max L₀ ((2:ℝ)^(1/b))
  let C : ℝ := C₁+C₂+L₁^c
  have hc : 0 < c := lt_min hc₁ (mul_pos hb hc₂)
  have hL₁ : 1 < L₁ := hL₀.trans_le (le_max_left _ _)
  have hC : 0 < C := by
    have hpow : 0 ≤ L₁^c := Real.rpow_nonneg (by linarith) _
    dsimp [C]; linarith
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω mΩ P hP γ hγ F Fbar hF hi hbar hext q r hr η T hT hη hη0 hu hηi hηq hupper hpath L hL
  let : IsProbabilityMeasure P := hP
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow : 0 < L^(-c) := Real.rpow_pos_of_pos hLp _
  by_cases hlarge : L₁ ≤ L
  · have hA : 2 ≤ L^b := by
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (1/b))
        ((le_max_right L₀ ((2:ℝ)^(1/b))).trans hlarge) hb.le
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),one_div_mul_cancel hb.ne',Real.rpow_one] at hh
      exact hh
    have hp₁ := hloc Ω mΩ P hP γ hγ F Fbar hF hi hbar hext q r hr η T hT hη hη0 hu hupper hpath L
      ((le_max_left _ _).trans hlarge)
    obtain ⟨B,G,Fw,hB,hw⟩ := hγ.exists_charts
    have hp₂ := hsw hB γ G Fw hw (η T) hηi hu (L^b) hA
    have heq : (L^b)^(-c₂) = L^(-(b*c₂)) := by
      rw [← Real.rpow_mul hLp.le]
      congr 1
      ring
    rw [heq] at hp₂
    have hsub : {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ⊆
      {xi | ∃ t : ℝ≥0, BeforeFirstModulus (γ xi) (L^b) t ∧
        Fbar (γ xi t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)} ∪
      {xi | PreSwallowExcursion (γ xi) (η T) (L^b)} := by
      intro xi hxi
      exact mapped_live_exit_split (γ xi) Fbar (η T) q (L^b) (L*r) hxi
    have he₁ : L^(-c₁) ≤ L^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_left _ _))
    have he₂ : L^(-(b*c₂)) ≤ L^(-c) :=
      Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_right _ _))
    have hsum : C₁*L^(-c₁)+C₂*L^(-(b*c₂)) ≤ C*L^(-c) := by
      have hnon : 0 ≤ L₁^c := Real.rpow_nonneg (by linarith) _
      calc
        _ ≤ C₁*L^(-c)+C₂*L^(-c) := add_le_add
          (mul_le_mul_of_nonneg_left he₁ hC₁.le)
          (mul_le_mul_of_nonneg_left he₂ hC₂.le)
        _ ≤ C*L^(-c) := by dsimp [C]; nlinarith
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans
      ((add_le_add hp₁ hp₂).trans (by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal hsum)))
  · have hprod : L^c*L^(-c) = 1 := by
      rw [← Real.rpow_add hLp,add_neg_cancel,Real.rpow_zero]
    have hle : L^c ≤ L₁^c := Real.rpow_le_rpow hLp.le (not_le.mp hlarge).le hc.le
    have hbound : 1 ≤ C*L^(-c) := by
      rw [← hprod]
      apply mul_le_mul_of_nonneg_right _ hpow.le
      dsimp [C]
      linarith
    exact prob_le_one.trans (by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hbound)

end SLEExactGauge
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_InteriorDiskProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior Disk Proof for chordal SLE. -/

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma access_positive_height_cut {η : ℝ → ℂ} {T ε : ℝ}
    (hT : 0 < T) (hc : ContinuousOn η (Icc 0 T)) (h0 : η 0 = 0)
    (hpos : ∀ t ∈ Ioc 0 T, 0 < (η t).im) (hε : 0 < ε) :
    ∃ s ∈ Ioo 0 T, ‖η s‖ < ε ∧ ∀ t ∈ Icc s T, (η s).im ≤ (η t).im := by
  have hc0 := Metric.continuousWithinAt_iff.mp (hc 0 ⟨le_rfl,hT.le⟩)
  obtain ⟨δ,hδ,hδlim⟩ := hc0 ε hε
  let a : ℝ := min (T/2) (δ/2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haT : a < T := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc a T).Nonempty from ⟨a,le_rfl,haT.le⟩)
    ((Complex.continuous_im.comp_continuousOn hc).mono (Icc_subset_Icc_left ha.le))
  have hmpos : 0 < (η m).im := hpos m ⟨ha.trans_le hm.1,hm.2⟩
  obtain ⟨δ',hδ',hδlim'⟩ := hc0 (η m).im hmpos
  let b : ℝ := min (a/2) (δ'/2)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hba : b < a := (min_le_left _ _).trans_lt (by linarith)
  have hbT : b < T := hba.trans haT
  have hbnorm : ‖η b‖ < (η m).im := by
    have hh := hδlim' ⟨hb.le,hbT.le⟩
      (show dist b 0 < δ' by
        rw [Real.dist_eq,sub_zero,abs_of_pos hb]
        exact (min_le_right _ _).trans_lt (by linarith))
    simpa only [h0,dist_zero_right] using hh
  obtain ⟨s,hs,hsmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc b T).Nonempty from ⟨b,le_rfl,hbT.le⟩)
    ((Complex.continuous_im.comp_continuousOn hc).mono (Icc_subset_Icc_left hb.le))
  have hsa : s < a := by
    by_contra hh
    have hh₁ := hmin ⟨not_lt.mp hh,hs.2⟩
    have hh₂ := hsmin ⟨le_rfl,hbT.le⟩
    have hh₃ := Complex.im_le_norm (η b)
    change (η m).im ≤ (η s).im at hh₁
    change (η s).im ≤ (η b).im at hh₂
    linarith
  refine ⟨s,⟨hb.trans_le hs.1,hsa.trans haT⟩,?_,?_⟩
  · have hh := hδlim ⟨(hb.trans_le hs.1).le,hs.2⟩
      (show dist s 0 < δ by
        rw [Real.dist_eq,sub_zero,abs_of_pos (hb.trans_le hs.1)]
        exact hsa.trans_le ((min_le_right _ _).trans (by linarith)))
    simpa only [h0,dist_zero_right] using hh
  · intro t ht
    exact hsmin ⟨hs.1.trans ht.1,ht.2⟩

lemma measure_eventually_mem_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : ℕ → Set Ω) (b : ℝ≥0∞) (hb : ∀ n, P (E n) ≤ b) :
    P {xi | ∀ᶠ n in atTop, xi ∈ E n} ≤ b := by
  let A : ℕ → Set Ω := fun m => {xi | ∀ n, m ≤ n → xi ∈ E n}
  have hm : Monotone A := by
    intro i j hij xi hxi n hjn
    exact hxi n (hij.trans hjn)
  have he : {xi | ∀ᶠ n in atTop, xi ∈ E n} = ⋃ m, A m := by
    ext xi
    simp only [mem_ofPred_eq, mem_iUnion, Filter.eventually_atTop, A]
  rw [he,hm.measure_iUnion]
  apply iSup_le
  intro n
  exact (measure_mono (show A n ⊆ E n from fun xi hxi => hxi n le_rfl)).trans (hb n)
end SLEExactGauge
namespace SLEExactGauge

lemma positive_affine_im {a z : ℂ} {c : ℝ} (ha : 0 < a.im)
    (hc : 0 < c) (hz : 0 ≤ z.im) : 0 < (a+(c:ℂ)*z).im := by
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  positivity

lemma positive_affine_chart {F : ℂ → ℂ} {a : ℂ} {c : ℝ}
    (hF : DifferentiableOn ℂ F {z | 0 < z.im}) (hi : InjOn F {z | 0 < z.im})
    (ha : 0 < a.im) (hc : 0 < c) :
    DifferentiableOn ℂ (fun z => F (a+(c:ℂ)*z)) {z | 0 < z.im} ∧
    InjOn (fun z => F (a+(c:ℂ)*z)) {z | 0 < z.im} ∧
    ContinuousOn (fun z => (F (a+(c:ℂ)*z) : OnePoint ℂ)) {z : ℂ | 0 ≤ z.im} := by
  have haff : Differentiable ℂ (fun z : ℂ => a+(c:ℂ)*z) := by fun_prop
  have hm (z : ℂ) (hz : 0 ≤ z.im) := positive_affine_im ha hc hz
  refine ⟨hF.comp haff.differentiableOn (fun z hz => hm z hz.le),?_,?_⟩
  · intro z hz w hw heq
    have hh := add_left_cancel (hi (hm z hz.le) (hm w hw.le) heq)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne') hh
  · apply OnePoint.continuous_coe.comp_continuousOn
    exact hF.continuousOn.comp haff.continuous.continuousOn (fun z hz => hm z hz)

lemma affine_access_cut {F : ℂ → ℂ} {η : ℝ → ℂ} {T s r : ℝ} {q : ℂ}
    (_hT : 0 < T) (hc : ContinuousOn η (Icc 0 T))
    (hs : s ∈ Ioo 0 T) (_hpos : ∀ t ∈ Ioc 0 T, 0 < (η t).im)
    (hpath : ∀ t ∈ Ioc 0 T, ‖F (η t)-q‖ ≤ r)
    (hmin : ∀ t ∈ Icc s T, (η s).im ≤ (η t).im)
    (hsmall : (η s).im < (η T).im) (hq : F (η T) = q) :
    let c := ‖η T-η s‖
    let ξ := fun t : ℝ => (η (s+t)-η s)/(c:ℂ)
    0 < c ∧ ContinuousOn ξ (Icc 0 (T-s)) ∧ ξ 0 = 0 ∧
    ‖ξ (T-s)‖ = 1 ∧ 0 < (ξ (T-s)).im ∧
    F (η s+(c:ℂ)*ξ (T-s)) = q ∧
    (∀ t ∈ Icc 0 (T-s), 0 ≤ (ξ t).im) ∧
    (∀ t ∈ Icc 0 (T-s), ∃ w : ℂ,
      (F (η s+(c:ℂ)*ξ t) : OnePoint ℂ) = (w : OnePoint ℂ) ∧ ‖w-q‖ ≤ r) := by
  dsimp only
  let c : ℝ := ‖η T-η s‖
  have hne : η T-η s ≠ 0 := by
    intro he
    have hh := congrArg Complex.im (sub_eq_zero.mp he)
    linarith
  have hcp : 0 < c := norm_pos_iff.mpr hne
  have hcz : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcp.ne'
  have hm {t : ℝ} (ht : t ∈ Icc 0 (T-s)) : s+t ∈ Ioc 0 T := by
    constructor <;> linarith [ht.1,ht.2,hs.1]
  have hcancel (t : ℝ) : η s+(c:ℂ)*((η (s+t)-η s)/(c:ℂ)) = η (s+t) := by
    field_simp
    ring
  have hend : s+(T-s) = T := by ring
  change 0 < c ∧ _
  refine ⟨hcp,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (hc.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => ⟨(hm ht).1.le,(hm ht).2⟩)).sub continuousOn_const |>.div_const (c:ℂ)
  · simp
  · simp only [hend,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    exact div_self hcp.ne'
  · simp only [hend,Complex.div_ofReal_im,Complex.sub_im]
    exact div_pos (sub_pos.mpr hsmall) hcp
  · rw [hcancel,hend,hq]
  · intro t ht
    simp only [Complex.div_ofReal_im,Complex.sub_im]
    exact div_nonneg (sub_nonneg.mpr (hmin (s+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩)) hcp.le
  · intro t ht
    refine ⟨F (η (s+t)),?_,hpath _ (hm ht)⟩
    rw [hcancel]

end SLEExactGauge
namespace SLEExactGauge


theorem sourceInteriorDiskRule_proved : SourceInteriorDiskRuleTarget := by
  intro κ hκ hκ8
  obtain ⟨C,c,hC,hc,hbound⟩ := sourceChartedDiskRule κ hκ hκ8
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω mΩ P hP γ hγ F hF hi q r hr η T hT hη h0 hu hq hpos hpath L hL
  let : IsProbabilityMeasure P := hP
  have huim : 0 < (η T).im := hpos T ⟨hT,le_rfl⟩
  have hsmall (n : ℕ) : 0 < min (1/((n:ℝ)+1)) ((η T).im/2) := by positivity
  choose s hs hnorm hmin using fun n : ℕ => access_positive_height_cut hT hη h0 hpos (hsmall n)
  let a : ℕ → ℂ := fun n => η (s n)
  let d : ℕ → ℝ := fun n => ‖η T-a n‖
  let u : ℕ → ℂ := fun n => (η T-a n)/(d n:ℂ)
  let Ψ : ℕ → ℂ → ℂ := fun n z => F (a n+(d n:ℂ)*z)
  let ξ : ℕ → ℝ → ℂ := fun n t => (η (s n+t)-a n)/(d n:ℂ)
  have hn (n : ℕ) : ‖a n‖ < 1/((n:ℝ)+1) := (hnorm n).trans_le (min_le_left _ _)
  have hasmall (n : ℕ) : (a n).im < (η T).im := by
    have hh := (hnorm n).trans_le (min_le_right _ _)
    have hh' := Complex.im_le_norm (a n)
    change ‖a n‖ < _ at hh
    linarith
  have hcut (n : ℕ) := affine_access_cut hT hη (hs n) hpos hpath (hmin n) (hasmall n) hq
  have hdp (n : ℕ) : 0 < d n := (hcut n).1
  have hai (n : ℕ) : 0 < (a n).im := hpos (s n) ⟨(hs n).1,(hs n).2.le⟩
  have ha0 : Tendsto a atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
    refine ⟨N,fun n hnn => ?_⟩
    rw [dist_zero_right]
    exact (hn n).trans (by simpa only [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < 1/((n:ℝ)+1))] using hN n hnn)
  have hd1 : Tendsto d atTop (𝓝 1) := by
    have hh := ((tendsto_const_nhds (x := η T)).sub ha0).norm
    simpa only [sub_zero,hu] using hh
  have hu1 : Tendsto u atTop (𝓝 (η T)) := by
    have hh := ((tendsto_const_nhds (x := η T)).sub ha0).div (Complex.continuous_ofReal.tendsto 1 |>.comp hd1)
      (by norm_num : (1:ℂ) ≠ 0)
    convert hh using 1
    · ext n
      simp only [u,Pi.div_apply,Function.comp_apply]
    · simp
  let E : ℕ → Set Ω := fun n => {xi | ∃ t : ℝ≥0, u n ∈ survivingDomain (γ xi) t ∧
    (Ψ n (γ xi t) : OnePoint ℂ) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' Metric.ball q (L*r)}
  have hE (n : ℕ) : P (E n) ≤ ENNReal.ofReal (C*L^(-c)) := by
    have hh := hcut n
    obtain ⟨hd,hct,hz,hnormT,hposT,hqT,hupper,hpaths⟩ := hh
    have hξ : ξ n (T-s n) = u n := by simp only [ξ,u, show s n+(T-s n)=T by ring]
    obtain ⟨hFn,hin,hbc⟩ := positive_affine_chart hF hi (hai n) (hdp n)
    have hb := hbound Ω mΩ P hP γ hγ (Ψ n) (fun z => (Ψ n z : OnePoint ℂ))
      hFn hin hbc (fun _ _ => rfl) q r hr (ξ n) (T-s n) (sub_pos.mpr (hs n).2)
      hct hz hnormT hposT hqT hupper hpaths L hL
    simpa only [hξ] using hb
  have hf (z : ℂ) (hz : 0 < z.im) : Tendsto (fun n => Ψ n z) atTop (𝓝 (F z)) := by
    have harg : Tendsto (fun n => a n+(d n:ℂ)*z) atTop (𝓝 z) := by
      have hh := ha0.add ((Complex.continuous_ofReal.tendsto 1 |>.comp hd1).mul (tendsto_const_nhds (x := z)))
      convert hh using 1
      · ext n
        simp only [Function.comp_apply]
      · simp
    exact (hF.continuousOn.continuousAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz)).tendsto.comp harg
  obtain ⟨B,G,Fw,hB,hw⟩ := hγ.exists_charts
  have hsub : {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
      0 < (γ xi t).im ∧ L*r < ‖F (γ xi t)-q‖} ≤ᵐ[P]
      {xi | ∀ᶠ n in atTop, xi ∈ E n} := by
    filter_upwards [hw] with xi hxi
    rintro ⟨t,ht,hzi,hbig⟩
    have hlive := hu1.eventually ((isOpen_survivingDomain hxi.1 t).eventually_mem ht)
    have hnormlim := ((hf (γ xi t) hzi).sub_const q).norm
    have hbig' := hnormlim.eventually (eventually_gt_nhds hbig)
    filter_upwards [hlive,hbig'] with n hnt hnb
    refine ⟨t,hnt,?_⟩
    rintro ⟨w,hwball,hweq⟩
    have heq : w = Ψ n (γ xi t) := OnePoint.coe_injective hweq
    subst w
    exact (not_lt_of_ge hnb.le) (by simpa only [Metric.mem_ball,dist_eq_norm] using hwball)
  exact (measure_mono_ae hsub).trans (measure_eventually_mem_le P E _ hE)

end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

theorem sourceCapacityScaling : SourceCapacityScalingTarget := by
  refine ⟨source_scale_witness, ?_⟩
  intro Ω m P κ hκ hκ8 γ hγ c hc
  rcases hγ with ⟨hm, B, hB, hw⟩
  refine ⟨fun t => measurable_const.mul (hm (sourceScaleTime c t)),
    (fun t ω => (c : ℝ) * B (sourceScaleTime c t) ω), ?_, ?_⟩
  · have hh := hB.smul (c := (c ^ 2)⁻¹) (inv_ne_zero (pow_ne_zero 2 hc.ne'))
    simpa only [sourceScaleTime, NNReal.coe_inv, NNReal.coe_pow, Real.sqrt_inv,
      Real.sqrt_sq c.coe_nonneg, inv_inv, div_eq_mul_inv, mul_comm] using hh
  · filter_upwards [hw] with ω hω
    obtain ⟨G, F, hGF⟩ := hω
    refine ⟨sourceScaleChart c G, sourceScaleChart c F, ?_⟩
    have hh := source_scale_witness c hc (fun t => Real.sqrt κ * B t ω) (γ ω) G F hGF
    simpa only [mul_left_comm (c : ℝ) (Real.sqrt κ)] using hh
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_interior_disk_unnormalized_oai (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ γ : Ω → ℝ≥0 → ℂ, IsOrdinaryChordalSLE κ γ P →
    ∀ F : ℂ → ℂ,
    DifferentiableOn ℂ F upperHalfPlane → InjOn F upperHalfPlane →
    ∀ (q : ℂ) (r : ℝ), 0 < r →
    ∀ (η : ℝ → ℂ) (T : ℝ), 0 < T → ContinuousOn η (Icc 0 T) →
    η 0 = 0 → F (η T) = q →
    (∀ t ∈ Ioc 0 T, 0 < (η t).im) →
    (∀ t ∈ Ioc 0 T, ‖F (η t)-q‖ ≤ r) →
    ∀ L : ℝ, 1 ≤ L →
      P {xi | ∃ t : ℝ≥0, η T ∈ survivingDomain (γ xi) t ∧
        0 < (γ xi t).im ∧ L*r < ‖F (γ xi t)-q‖} ≤
        ENNReal.ofReal (C*L^(-c)) := by
  obtain ⟨C,c,hC,hc,hbound⟩ := sourceInteriorDiskRule_proved κ hκ hκ8
  refine ⟨C,c,hC,hc,?_⟩
  intro Ω mΩ P hP γ hγ F hF hi q r hr η T hT hη hη0 hq hupper hpath L hL
  let d : ℝ≥0 := ‖η T‖₊
  have hd : 0 < d := by
    exact nnnorm_pos.mpr (fun he => by simpa [he] using hupper T ⟨hT,le_rfl⟩)
  let a : ℝ≥0 := d⁻¹
  have ha : 0 < a := inv_pos.mpr hd
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  let Ψ : ℂ → ℂ := fun z => F (z/(a : ℂ))
  let ξ : ℝ → ℂ := fun t => (a : ℂ)*η t
  have hmap (z : ℂ) (hz : z ∈ upperHalfPlane) : z/(a : ℂ) ∈ upperHalfPlane := by
    exact (source_scale_halfplane_iff a ha z).mpr hz
  have hΨ : DifferentiableOn ℂ Ψ upperHalfPlane :=
    hF.comp (differentiable_id.div_const (a : ℂ)).differentiableOn hmap
  have hΨi : InjOn Ψ upperHalfPlane := by
    intro x hx y hy he
    exact (div_left_inj' hane).mp (hi (hmap x hx) (hmap y hy) he)
  have hξ : ContinuousOn ξ (Icc 0 T) := continuousOn_const.mul hη
  have hξnorm : ‖ξ T‖ = 1 := by
    simp only [ξ,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg a.coe_nonneg]
    change (d : ℝ)⁻¹ * (d : ℝ) = 1
    exact inv_mul_cancel₀ (by exact_mod_cast hd.ne')
  have hΨξ (t : ℝ) : Ψ (ξ t) = F (η t) := by
    simp only [Ψ,ξ,mul_div_cancel_left₀ _ hane]
  have hξup (t : ℝ) (ht : t ∈ Ioc 0 T) : 0 < (ξ t).im := by
    simpa only [ξ, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos (show 0 < (a : ℝ) from ha) (hupper t ht)
  have hγa := sourceCapacityScaling.2 κ (by linarith) hκ8 γ hγ a ha
  have hb := hbound Ω mΩ P hP (fun ω => sourceScaleTrace a (γ ω)) hγa Ψ hΨ hΨi q r hr
    ξ T hT hξ (by simp [ξ,hη0]) hξnorm (by simpa [hΨξ] using hq) hξup
    (fun t ht => by simpa only [hΨξ] using hpath t ht) L hL
  apply (measure_mono ?_).trans hb
  rintro ω ⟨t,hl,ht,hb⟩
  let s : ℝ≥0 := t*a^2
  have hs : sourceScaleTime a s = t := by dsimp [s,sourceScaleTime]; exact mul_div_cancel_right₀ _ (pow_ne_zero 2 ha.ne')
  have htip : sourceScaleTrace a (γ ω) s = (a : ℂ)*γ ω t := by simp only [sourceScaleTrace,hs]
  refine ⟨s,?_,?_,?_⟩
  · apply (source_scale_domain_iff a s ha (γ ω) (ξ T)).mpr
    simpa only [ξ, mul_div_cancel_left₀ _ hane, hs] using hl
  · rw [htip]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos (show 0 < (a : ℝ) from ha) ht
  · simpa only [htip,Ψ,mul_div_cancel_left₀ _ hane] using hb
end SLEExactGauge
end

end OAI
end

theorem solution : type_of% @OAI.SLEExactGauge.source_interior_disk_unnormalized_oai := @OAI.SLEExactGauge.source_interior_disk_unnormalized_oai
