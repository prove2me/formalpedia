-- Prove2me | solution 1 for OAI.SLEExactGauge.RegularSLEPresentation.spatial_slab_terminal_exponential
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:41:40.213387+00:00
-- url     : https://prove2.me/submissions/c7feb889-072d-49d1-a8bd-de20671c10ba

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
/-- The `mpr` direction of Mathlib d13f23b's `unifIntegrable_iff`, whose `UnifIntegrable` takes
extended-real `ε` and `δ` and bounds `eLpNorm (f i) p (μ.restrict s)`; ours takes real ones and a
measurable set `s` (SLE IntegralLimits, oaiq-027). -/
theorem unifIntegrable_of_enn {α β ι : Type*} {m : MeasurableSpace α} [NormedAddCommGroup β]
    {f : ι → α → β} {p : ENNReal} {μ : MeasureTheory.Measure α}
    (h : ∀ ε : ENNReal, 0 < ε → ∃ δ : ENNReal, 0 < δ ∧
      ∀ i s, μ s ≤ δ → MeasureTheory.eLpNorm (f i) p (μ.restrict s) ≤ ε) :
    MeasureTheory.UnifIntegrable f p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hne : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min δ 1).toReal, ENNReal.toReal_pos (lt_min hδ one_pos).ne' hne,
    fun i s hsm hs => ?_⟩
  rw [MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hsm]
  refine hb i s (hs.trans ?_)
  rw [ENNReal.ofReal_toReal hne]
  exact min_le_left _ _
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

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge



theorem compensated_exponential_limit_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X E : ℕ → Ω → ℝ) (Y Q : Ω → ℝ) (θ : ℝ)
    (hm : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal
      (Real.exp (θ * X n ω - θ ^ 2 * E n ω / 2))) P)
    (hX : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hE : ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop (𝓝 (Q ω)))
    (hexp : ∀ n, (∫⁻ ω, ENNReal.ofReal
      (Real.exp (θ * X n ω - θ ^ 2 * E n ω / 2)) ∂P) ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * Q ω / 2)) ∂P) ≤ 1 := by
  let f (n : ℕ) (ω : Ω) := ENNReal.ofReal (Real.exp (θ * X n ω - θ ^ 2 * E n ω / 2))
  have hl : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (θ * Y ω - θ ^ 2 * Q ω / 2)) =
      liminf (fun n => f n ω) atTop := by
    filter_upwards [hX, hE] with ω hx he
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp ((hx.const_mul θ).sub
        ((he.const_mul (θ^2)).div_const 2)))).liminf_eq.symm
  calc
    _ = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P := lintegral_congr_ae hl
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' hm
    _ ≤ 1 := liminf_le_of_frequently_le (Frequently.of_forall hexp)


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


section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

lemma complex_bilinear_rotation_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (e : ℂ) :
    B e e + B (e * I) (e * I) = ‖e‖ ^ 2 * (B 1 1 + B I I) := by
  have he : e = e.re • (1 : ℂ) + e.im • I := by apply Complex.ext <;> simp
  have heI : e * I = (-e.im) • (1 : ℂ) + e.re • I := by apply Complex.ext <;> simp
  calc
    _ = B (e.re • 1 + e.im • I) (e.re • 1 + e.im • I) +
      B ((-e.im) • 1 + e.re • I) ((-e.im) • 1 + e.re • I) := by rw [← he, ← heI]
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply]
      ring

lemma complex_hessian_rotation {u : ℂ → ℝ} (z e : ℂ) :
    fderiv ℝ (fderiv ℝ u) z e e + fderiv ℝ (fderiv ℝ u) z (e * I) (e * I) =
      ‖e‖ ^ 2 * (Δ u) z := by
  rw [complex_bilinear_rotation_trace]
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

lemma polarPoint_eq_circleMap (r θ : ℝ) : polarPoint r θ = circleMap 0 r θ := by
  simp [polarPoint, circleMap]

lemma polarPoint_norm (r θ : ℝ) : ‖polarPoint r θ‖ = |r| := by
  simp [polarPoint, norm_circleMap_zero]

lemma polarPoint_radial_hasDeriv (r θ : ℝ) :
    HasDerivAt (fun s => polarPoint s θ) (circleMap 0 1 θ) r := by
  simpa [polarPoint] using (hasDerivAt_id r).smul_const (circleMap 0 1 θ)

lemma polarPoint_angular_hasDeriv (r θ : ℝ) :
    HasDerivAt (polarPoint r) (polarPoint r θ * I) θ := by
  simpa only [funext (polarPoint_eq_circleMap r), polarPoint_eq_circleMap] using
    hasDerivAt_circleMap 0 r θ

lemma radial_partial_hasDeriv {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun s => u (polarPoint s θ))
      (fderiv ℝ u (polarPoint r θ) (circleMap 0 1 θ)) r :=
  (hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r
    (polarPoint_radial_hasDeriv r θ)

lemma radial_second_hasDeriv {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun s => fderiv ℝ u (polarPoint s θ) (circleMap 0 1 θ))
      (fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (circleMap 0 1 θ) (circleMap 0 1 θ)) r := by
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasDerivAt (fun s => fderiv ℝ u (polarPoint s θ))
      (fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (circleMap 0 1 θ)) r :=
    hd.comp_hasDerivAt r (polarPoint_radial_hasDeriv r θ)
  have ha := hc.clm_apply (hasDerivAt_const r (circleMap 0 1 θ))
  simpa only [map_zero, add_zero] using ha

lemma angular_second_hasDeriv {u : ℂ → ℝ} {r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun φ => fderiv ℝ u (polarPoint r φ) (polarPoint r φ * I))
      (fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (polarPoint r θ * I) (polarPoint r θ * I)
        - fderiv ℝ u (polarPoint r θ) (polarPoint r θ)) θ := by
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have ht := (polarPoint_angular_hasDeriv r θ).mul_const I
  have hmul : (polarPoint r θ * I) * I = -polarPoint r θ := by rw [mul_assoc, I_mul_I, mul_neg_one]
  rw [hmul] at ht
  simpa [sub_eq_add_neg] using
    (hd.comp_hasDerivAt θ (polarPoint_angular_hasDeriv r θ)).clm_apply ht

 

lemma polar_laplacian_identity {u : ℂ → ℝ} (r θ : ℝ) :
    r ^ 2 * (Δ u) (polarPoint r θ) =
      r ^ 2 * fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (circleMap 0 1 θ) (circleMap 0 1 θ) +
      fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (polarPoint r θ * I) (polarPoint r θ * I) := by
  have hh := complex_hessian_rotation (u := u) (polarPoint r θ) (circleMap 0 1 θ)
  have he : polarPoint r θ * I = r • (circleMap 0 1 θ * I) := by
    simp [polarPoint, mul_assoc]
  rw [he]
  simp only [map_smul, smul_apply, smul_eq_mul]
  simp only [norm_circleMap_zero, abs_one, one_pow, one_mul] at hh
  nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian
namespace SLEExactGauge

lemma polarPoint_contDiff : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => polarPoint p.1 p.2) := by
  have hc : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  have he : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => circleMap 0 1 p.2) := by
    have hExp : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
    simpa only [circleMap, Complex.ofReal_one, one_mul, zero_add, Function.comp_def] using
      hExp.comp (hc.mul (contDiff_const (c := I)))
  exact contDiff_fst.smul he

lemma polarRadialFlux_differentiableAt {u : ℂ → ℝ} {R r θ : ℝ}
    (hr : r ≠ 0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    DifferentiableAt ℝ (polarRadialFlux u R) (r, θ) := by
  have hp := polarPoint_contDiff.differentiable (by simp) (r, θ)
  have hv := (hu.differentiableAt (by norm_num)).comp (r, θ) hp
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).comp (r, θ) hp
  unfold polarRadialFlux
  exact ((differentiableAt_fst.mul ((differentiableAt_const (Real.log R)).sub
    (differentiableAt_fst.log hr))).mul (hd.clm_apply (by unfold circleMap; fun_prop))).add hv

lemma polarAngularFlux_differentiableAt {u : ℂ → ℝ} {R r θ : ℝ}
    (hr : r ≠ 0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    DifferentiableAt ℝ (polarAngularFlux u R) (r, θ) := by
  have hp := polarPoint_contDiff.differentiable (by simp) (r, θ)
  have hd := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).comp (r, θ) hp
  have hfst : DifferentiableAt ℝ (Prod.fst : ℝ × ℝ → ℝ) (r, θ) := differentiableAt_fst
  have hl : DifferentiableAt ℝ (fun p : ℝ × ℝ => (Real.log R - Real.log p.1) / p.1) (r, θ) :=
    by
      simp only [div_eq_mul_inv]
      exact ((differentiableAt_const (Real.log R)).sub (hfst.log hr)).mul (hfst.inv hr)
  exact hl.mul (hd.clm_apply (hp.mul_const I))

lemma polarRadialFlux_radial_hasDeriv {u : ℂ → ℝ} {R r θ : ℝ}
    (hr : r ≠ 0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun s => polarRadialFlux u R (s, θ))
      ((Real.log R - Real.log r) * fderiv ℝ u (polarPoint r θ) (circleMap 0 1 θ) +
        r * (Real.log R - Real.log r) *
          fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (circleMap 0 1 θ) (circleMap 0 1 θ)) r := by
  have hl := (Real.hasDerivAt_log hr).const_sub (Real.log R)
  have hh := (((hasDerivAt_id r).mul hl).mul (radial_second_hasDeriv hu)).add
    (radial_partial_hasDeriv hu)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [id_eq, Pi.mul_apply]
  field_simp [hr]
  ring

lemma polarAngularFlux_angular_hasDeriv {u : ℂ → ℝ} {R r θ : ℝ}
    (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    HasDerivAt (fun φ => polarAngularFlux u R (r, φ))
      ((Real.log R - Real.log r) / r *
        (fderiv ℝ (fderiv ℝ u) (polarPoint r θ) (polarPoint r θ * I) (polarPoint r θ * I) -
          fderiv ℝ u (polarPoint r θ) (polarPoint r θ))) θ :=
  (angular_second_hasDeriv hu).const_mul ((Real.log R - Real.log r) / r)

lemma polarGreen_divergence {u : ℂ → ℝ} {R r θ : ℝ}
    (hr : r ≠ 0) (hu : ContDiffAt ℝ 2 u (polarPoint r θ)) :
    fderiv ℝ (polarRadialFlux u R) (r, θ) (1, 0) +
      fderiv ℝ (polarAngularFlux u R) (r, θ) (0, 1) =
        r * (Real.log R - Real.log r) * (Δ u) (polarPoint r θ) := by
  have hf := (polarRadialFlux_differentiableAt (R := R) hr hu).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ))
  have hg := (polarAngularFlux_differentiableAt (R := R) hr hu).hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ))
  rw [hf.unique (polarRadialFlux_radial_hasDeriv hr hu),
    hg.unique (polarAngularFlux_angular_hasDeriv hu)]
  have he : fderiv ℝ u (polarPoint r θ) (polarPoint r θ) =
      r * fderiv ℝ u (polarPoint r θ) (circleMap 0 1 θ) := by
    conv_lhs => arg 2; rw [polarPoint]
    simp only [map_smul, smul_eq_mul]
  rw [he]
  have hh := polar_laplacian_identity (u := u) r θ
  apply (mul_right_cancel₀ hr)
  field_simp [hr]
  have hmul := congrArg (fun x : ℝ => (Real.log R - Real.log r) * x) hh
  nlinarith only [hmul]

lemma polarPoint_endpoints (r : ℝ) : polarPoint r (-Real.pi) = polarPoint r Real.pi := by
  have hp := periodic_circleMap 0 1 (-Real.pi)
  have he : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [he] at hp
  exact congrArg (fun z : ℂ => r • z) hp.symm

lemma polarAngularFlux_endpoints (u : ℂ → ℝ) (R r : ℝ) :
    polarAngularFlux u R (r, -Real.pi) = polarAngularFlux u R (r, Real.pi) := by
  simp only [polarAngularFlux, polarPoint_endpoints]

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

lemma plane_laplacian_continuousAt {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    ContinuousAt (Δ u) z := by
  have hh := ((hu.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
    (by norm_num)).continuousAt
  have h1 := (hh.clm_apply (continuousAt_const (y := (1 : ℂ)))).clm_apply
    (continuousAt_const (y := (1 : ℂ)))
  have hI := (hh.clm_apply (continuousAt_const (y := I))).clm_apply
    (continuousAt_const (y := I))
  simpa only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Fin.isValue, Pi.add_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    using h1.add hI

lemma polarPoint_mem_ball {a R r θ : ℝ} (ha : 0 < a) (hR : R < 1)
    (hr : r ∈ Icc a R) : polarPoint r θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, polarPoint_norm, abs_of_pos (ha.trans_le hr.1)]
  exact hr.2.trans_lt hR

 

lemma annulus_green_identity {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    (∫ r in a..R, ∫ θ in -Real.pi..Real.pi,
      r * (Real.log R - Real.log r) * (Δ u) (polarPoint r θ)) =
      (∫ θ in -Real.pi..Real.pi, u (polarPoint R θ)) -
        ∫ θ in -Real.pi..Real.pi, polarRadialFlux u R (a, θ) := by
  let S := uIcc a R ×ˢ uIcc (-Real.pi) Real.pi
  have hmem (p : ℝ × ℝ) (hp : p ∈ S) : p.1 ≠ 0 ∧ polarPoint p.1 p.2 ∈ ball (0 : ℂ) 1 := by
    have hr : p.1 ∈ Icc a R := by simpa only [uIcc_of_le haR] using hp.1
    exact ⟨(ha.trans_le hr.1).ne', polarPoint_mem_ball ha hR hr⟩
  have hf : ContinuousOn (polarRadialFlux u R) S := fun p hp =>
    (polarRadialFlux_differentiableAt (hmem p hp).1 (hu _ (hmem p hp).2)).continuousAt.continuousWithinAt
  have hg : ContinuousOn (polarAngularFlux u R) S := fun p hp =>
    (polarAngularFlux_differentiableAt (hmem p hp).1 (hu _ (hmem p hp).2)).continuousAt.continuousWithinAt
  have hl : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * (Real.log R - Real.log p.1) * (Δ u) (polarPoint p.1 p.2)) S := by
    intro p hp
    exact ((continuousAt_fst.mul (continuousAt_const.sub (continuousAt_fst.log (hmem p hp).1))).mul
      ((plane_laplacian_continuousAt (hu _ (hmem p hp).2)).comp (f := fun p : ℝ × ℝ => polarPoint p.1 p.2)
        polarPoint_contDiff.continuous.continuousAt)).continuousWithinAt
  have he : EqOn (fun p : ℝ × ℝ => fderiv ℝ (polarRadialFlux u R) p (1, 0) +
      fderiv ℝ (polarAngularFlux u R) p (0, 1))
      (fun p => p.1 * (Real.log R - Real.log p.1) * (Δ u) (polarPoint p.1 p.2)) S :=
    fun p hp => polarGreen_divergence (hmem p hp).1 (hu _ (hmem p hp).2)
  have hi : IntegrableOn (fun p : ℝ × ℝ => fderiv ℝ (polarRadialFlux u R) p (1, 0) +
      fderiv ℝ (polarAngularFlux u R) p (0, 1)) S :=
    (hl.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun
      (fun p hp => (he hp).symm) (measurableSet_uIcc.prod measurableSet_uIcc)
  have hm : Ioo (min a R) (max a R) ×ˢ Ioo (min (-Real.pi) Real.pi) (max (-Real.pi) Real.pi) ⊆ S :=
    prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hh := integral2_divergence_prod_of_hasFDerivAt (polarRadialFlux u R) (polarAngularFlux u R)
    (fderiv ℝ (polarRadialFlux u R)) (fderiv ℝ (polarAngularFlux u R)) a (-Real.pi) R Real.pi hf hg
    (fun p hp => (polarRadialFlux_differentiableAt (hmem p (hm hp)).1
      (hu _ (hmem p (hm hp)).2)).hasFDerivAt)
    (fun p hp => (polarAngularFlux_differentiableAt (hmem p (hm hp)).1
      (hu _ (hmem p (hm hp)).2)).hasFDerivAt) hi
  have hi_eq : (∫ r in a..R, ∫ θ in -Real.pi..Real.pi,
      fderiv ℝ (polarRadialFlux u R) (r, θ) (1, 0) +
        fderiv ℝ (polarAngularFlux u R) (r, θ) (0, 1)) =
      ∫ r in a..R, ∫ θ in -Real.pi..Real.pi,
        r * (Real.log R - Real.log r) * (Δ u) (polarPoint r θ) := by
    apply intervalIntegral.integral_congr
    intro r hr
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact he ⟨hr, hθ⟩
  rw [hi_eq] at hh
  simpa only [polarAngularFlux_endpoints, sub_self, zero_add,
    polarRadialFlux, sub_self, mul_zero, zero_mul, zero_add] using hh

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian
namespace SLEExactGauge

lemma annulus_green_le {u : ℂ → ℝ} {a R C M : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z)
    (hun : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    (hub : ∀ z ∈ ball (0 : ℂ) 1, u z ≤ C)
    (hM : 0 ≤ M) (hgrad : ∀ θ : ℝ, ‖fderiv ℝ u (polarPoint a θ)‖ ≤ M) :
    (∫ r in a..R, ∫ θ in -Real.pi..Real.pi,
      r * (Real.log R - Real.log r) * (-(Δ u) (polarPoint r θ))) ≤
        2 * Real.pi * (C + M * (-a * Real.log a)) := by
  have hRpos := ha.trans_le haR
  have ha_mem (θ : ℝ) : polarPoint a θ ∈ ball (0 : ℂ) 1 :=
    polarPoint_mem_ball ha hR ⟨le_rfl, haR⟩
  have hR_mem (θ : ℝ) : polarPoint R θ ∈ ball (0 : ℂ) 1 :=
    polarPoint_mem_ball ha hR ⟨haR, le_rfl⟩
  have hL : 0 ≤ Real.log R - Real.log a := sub_nonneg.mpr (Real.log_le_log ha haR)
  have hlogR : Real.log R ≤ 0 := Real.log_nonpos hRpos.le hR.le
  have hbound (θ : ℝ) : polarRadialFlux u R (a, θ) ≤ C + M * (-a * Real.log a) := by
    have hb : fderiv ℝ u (polarPoint a θ) (circleMap 0 1 θ) ≤ M := by
      apply (le_abs_self _).trans
      calc
        _ = ‖fderiv ℝ u (polarPoint a θ) (circleMap 0 1 θ)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ u (polarPoint a θ)‖ * ‖circleMap 0 1 θ‖ :=
          (fderiv ℝ u (polarPoint a θ)).le_opNorm _
        _ ≤ M := by simpa using hgrad θ
    have hm := mul_le_mul_of_nonneg_left hb (mul_nonneg ha.le hL)
    have hn := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha.le hM) hlogR
    unfold polarRadialFlux
    nlinarith [hub _ (ha_mem θ)]
  have hf : Continuous (fun θ => polarRadialFlux u R (a, θ)) :=
    continuous_iff_continuousAt.mpr fun θ =>
      (polarRadialFlux_differentiableAt ha.ne' (hu _ (ha_mem θ))).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)
  have hf_int := hf.intervalIntegrable (μ := volume) (-Real.pi) Real.pi
  have hlo_pi : -Real.pi ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hf_le := intervalIntegral.integral_mono_on hlo_pi hf_int
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C + M * (-a * Real.log a)) volume
      (-Real.pi) Real.pi) (fun θ _ => hbound θ)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hf_le
  have huR := intervalIntegral.integral_nonneg_of_forall (μ := volume) hlo_pi (fun θ => hun _ (hR_mem θ))
  have hh := annulus_green_identity ha haR hR hu
  simp only [mul_neg, intervalIntegral.integral_neg]
  linarith

lemma derivative_locally_bounded {u : ℂ → ℝ}
    (hu : ContDiffAt ℝ 2 u 0) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ < δ → ‖fderiv ℝ u z‖ ≤ M := by
  have hc := (hu.fderiv_right (m := 1) (by norm_num)).continuousAt.norm
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), ‖fderiv ℝ u z‖ < ‖fderiv ℝ u 0‖ + 1 :=
    hc (Iio_mem_nhds (show ‖fderiv ℝ u 0‖ < ‖fderiv ℝ u 0‖ + 1 by linarith))
  rcases Metric.eventually_nhds_iff.mp he with ⟨δ, hδ, hd⟩
  refine ⟨δ, ‖fderiv ℝ u 0‖ + 1, hδ, by positivity, ?_⟩
  intro z hz
  exact (hd (by simpa only [dist_zero_right] using hz)).le

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge

lemma annulusDensity_continuousOn {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    ContinuousOn (annulusDensity u R) (greenRectangle a R) := by
  intro p hp
  have hr : p.1 ≠ 0 := (ha.trans_le hp.1.1).ne'
  have hz := polarPoint_mem_ball (θ := p.2) ha hR hp.1
  exact ((continuousAt_fst.mul (continuousAt_const.sub (continuousAt_fst.log hr))).mul
    ((plane_laplacian_continuousAt (hu _ hz)).neg.comp (f := fun p : ℝ × ℝ => polarPoint p.1 p.2)
      polarPoint_contDiff.continuous.continuousAt)).continuousWithinAt

lemma annulusDensity_integrableOn {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    IntegrableOn (annulusDensity u R) (greenRectangle a R) :=
  (annulusDensity_continuousOn ha hR hu).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma greenTruncation_integrable {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    Integrable (greenTruncation u a R) :=
  (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).mpr
    (annulusDensity_integrableOn ha hR hu)

lemma greenTruncation_nonneg {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (hR : R < 1)
    (hΔ : ∀ z ∈ ball (0 : ℂ) 1, (Δ u) z ≤ 0) (p : ℝ × ℝ) :
    0 ≤ greenTruncation u a R p := by
  by_cases hp : p ∈ greenRectangle a R
  · rw [greenTruncation, indicator_of_mem hp]
    have hr := ha.trans_le hp.1.1
    exact mul_nonneg (mul_nonneg hr.le (sub_nonneg.mpr (Real.log_le_log hr hp.1.2)))
      (neg_nonneg.mpr (hΔ _ (polarPoint_mem_ball ha hR hp.1)))
  · simp [greenTruncation, indicator_of_notMem hp]

lemma greenTruncation_integral {u : ℂ → ℝ} {a R : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z) :
    (∫ p, greenTruncation u a R p) =
      ∫ r in a..R, ∫ θ in -Real.pi..Real.pi, annulusDensity u R (r, θ) := by
  rw [greenTruncation, greenRectangle, integral_indicator (measurableSet_Icc.prod measurableSet_Icc)]
  have hf := annulusDensity_integrableOn ha hR hu
  rw [Measure.volume_eq_prod] at hf ⊢
  rw [setIntegral_prod _ hf]
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  simp only [intervalIntegral.integral_of_le haR, intervalIntegral.integral_of_le hpi,
    integral_Icc_eq_integral_Ioc]

lemma greenTruncation_lintegral_le {u : ℂ → ℝ} {a R C M : ℝ}
    (ha : 0 < a) (haR : a ≤ R) (hR : R < 1)
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z)
    (hun : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    (hub : ∀ z ∈ ball (0 : ℂ) 1, u z ≤ C)
    (hΔ : ∀ z ∈ ball (0 : ℂ) 1, (Δ u) z ≤ 0)
    (hM : 0 ≤ M) (hgrad : ∀ θ : ℝ, ‖fderiv ℝ u (polarPoint a θ)‖ ≤ M) :
    (∫⁻ p, ENNReal.ofReal (greenTruncation u a R p)) ≤
      ENNReal.ofReal (2 * Real.pi * (C + M * (-a * Real.log a))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (greenTruncation_integrable ha hR hu)
    (Eventually.of_forall (greenTruncation_nonneg ha hR hΔ)), greenTruncation_integral ha haR hR hu]
  exact ENNReal.ofReal_le_ofReal (annulus_green_le ha haR hR hu hun hub hM hgrad)

end SLEExactGauge

end


end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_AngularLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular Laws for chordal SLE. -/

section
section
section
open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge

lemma greenInner_pos (n : ℕ) : 0 < greenInner n := by unfold greenInner; positivity

lemma greenInner_le_half (n : ℕ) : greenInner n ≤ 1 / 2 := by
  unfold greenInner
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hh : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr hn
  linarith

lemma greenInner_le_outer (n : ℕ) : greenInner n ≤ greenOuter n := by
  unfold greenOuter
  linarith [greenInner_le_half n]

lemma greenOuter_lt_one (n : ℕ) : greenOuter n < 1 := by
  unfold greenOuter
  linarith [greenInner_pos n]

lemma greenInner_tendsto : Tendsto greenInner atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1 / 2) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0)
  simpa only [greenInner, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)

lemma greenOuter_tendsto : Tendsto greenOuter atTop (𝓝 1) := by
  change Tendsto (fun n => 1 - greenInner n) atTop (𝓝 1)
  simpa only [greenOuter, sub_zero] using tendsto_const_nhds.sub greenInner_tendsto

lemma greenInner_log_tendsto : Tendsto (fun n => -greenInner n * Real.log (greenInner n)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, zero_mul, neg_zero, neg_mul] using
    ((Real.continuous_mul_log.tendsto 0).comp greenInner_tendsto).neg

lemma greenTruncation_tendsto {u : ℂ → ℝ} {p : ℝ × ℝ} (hp : p ∈ polarUnitDisk) :
    Tendsto (fun n => ENNReal.ofReal (greenTruncation u (greenInner n) (greenOuter n) p)) atTop
      (𝓝 (ENNReal.ofReal (p.1 * (-Real.log p.1) * (-(Δ u) (polarPoint p.1 p.2))))) := by
  have he : ∀ᶠ n in atTop, greenTruncation u (greenInner n) (greenOuter n) p =
      p.1 * (Real.log (greenOuter n) - Real.log p.1) * (-(Δ u) (polarPoint p.1 p.2)) := by
    filter_upwards [greenInner_tendsto (Iio_mem_nhds hp.1.1),
      greenOuter_tendsto (Ioi_mem_nhds hp.1.2)] with n ha hR
    have hm : p ∈ greenRectangle (greenInner n) (greenOuter n) :=
      ⟨⟨ha.le, hR.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
    simp only [greenTruncation, indicator_of_mem hm, annulusDensity]
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp greenOuter_tendsto
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (((hl.sub_const (Real.log p.1)).const_mul p.1).mul_const
      (-(Δ u) (polarPoint p.1 p.2)))
  simp only [Function.comp_def, Real.log_one, zero_sub] at ht
  exact ht.congr' (he.mono fun n hn => congrArg ENNReal.ofReal hn.symm)

 

lemma polar_green_le {u : ℂ → ℝ} {C : ℝ}
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z)
    (hun : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    (hub : ∀ z ∈ ball (0 : ℂ) 1, u z ≤ C)
    (hΔ : ∀ z ∈ ball (0 : ℂ) 1, (Δ u) z ≤ 0) :
    (∫⁻ p, polarGreenTarget u p) ≤ ENNReal.ofReal (2 * Real.pi * C) := by
  let F : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (greenTruncation u (greenInner n) (greenOuter n) p)
  have hmeas (n : ℕ) : AEMeasurable (F n) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (greenTruncation_integrable (greenInner_pos n) (greenOuter_lt_one n) hu).aemeasurable
  have hp : polarGreenTarget u ≤ fun p => liminf (fun n => F n p) atTop := by
    intro p
    by_cases hp : p ∈ polarUnitDisk
    · rw [polarGreenTarget, indicator_of_mem hp]
      exact le_of_eq (greenTruncation_tendsto (u := u) hp).liminf_eq.symm
    · simp only [polarGreenTarget, indicator_of_notMem hp]
      exact bot_le
  rcases derivative_locally_bounded (hu 0 (by simp)) with ⟨δ, M, hδ, hM, hgrad⟩
  have hbound : ∀ᶠ n in atTop, (∫⁻ p, F n p) ≤
      ENNReal.ofReal (2 * Real.pi * (C + M * (-greenInner n * Real.log (greenInner n)))) := by
    filter_upwards [greenInner_tendsto (Iio_mem_nhds hδ)] with n hn
    change greenInner n < δ at hn
    exact greenTruncation_lintegral_le (greenInner_pos n) (greenInner_le_outer n)
      (greenOuter_lt_one n) hu hun hub hΔ hM (fun θ => hgrad _ (by
        simpa only [polarPoint_norm, abs_of_pos (greenInner_pos n)] using hn))
  have ht : Tendsto (fun n => ENNReal.ofReal
      (2 * Real.pi * (C + M * (-greenInner n * Real.log (greenInner n))))) atTop
      (𝓝 (ENNReal.ofReal (2 * Real.pi * C))) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds.add (greenInner_log_tendsto.const_mul M)).const_mul (2 * Real.pi))
  exact (lintegral_mono hp).trans ((lintegral_liminf_le' hmeas).trans
    ((liminf_le_liminf hbound).trans_eq ht.liminf_eq))

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

lemma polarPoint_eq_polarCoord (p : ℝ × ℝ) :
    polarPoint p.1 p.2 = Complex.polarCoord.symm p := by
  rw [polarPoint_eq_circleMap]
  apply Complex.ext
  · simp [circleMap_zero_re, Complex.polarCoord_symm_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  · simp [circleMap_zero_im, Complex.polarCoord_symm_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

lemma disk_log_lintegral_polar (h : ℂ → ℝ) :
    (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((-Real.log ‖z‖) * h z)) =
      ∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (p.1 * (-Real.log p.1) * h (polarPoint p.1 p.2)) := by
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  let S : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo (-Real.pi) Real.pi
  have hT : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hST : S ⊆ T := prod_mono Ioo_subset_Ioi_self subset_rfl
  let f : ℂ → ℝ≥0∞ := (ball (0 : ℂ) 1).indicator (fun z => ENNReal.ofReal ((-Real.log ‖z‖) * h z))
  calc
    _ = ∫⁻ z, f z := (lintegral_indicator measurableSet_ball _).symm
    _ = ∫⁻ p in T, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) :=
      (Complex.lintegral_comp_polarCoord_symm f).symm
    _ = ∫⁻ p in T, S.indicator (fun p : ℝ × ℝ =>
        ENNReal.ofReal (p.1 * (-Real.log p.1) * h (polarPoint p.1 p.2))) p := by
      apply setLIntegral_congr_fun hT
      intro p hp
      have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
      by_cases hr : p.1 < 1
      · have hz : Complex.polarCoord.symm p ∈ ball (0 : ℂ) 1 := by
          rw [mem_ball_zero_iff, hn]
          exact hr
        have hs : p ∈ S := ⟨⟨hp.1, hr⟩, hp.2⟩
        simp only [f, indicator_of_mem hz, indicator_of_mem hs, hn, smul_eq_mul,
          polarPoint_eq_polarCoord, ← ENNReal.ofReal_mul hp.1.le, mul_assoc]
      · have hz : Complex.polarCoord.symm p ∉ ball (0 : ℂ) 1 := by
          simpa only [mem_ball_zero_iff, hn] using hr
        have hs : p ∉ S := fun hs => hr hs.1.2
        simp only [f, indicator_of_notMem hz, indicator_of_notMem hs, smul_zero]
    _ = _ := by
      rw [lintegral_indicator hS, Measure.restrict_restrict hS, inter_eq_left.mpr hST]

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge

 
lemma disk_green_le {u : ℂ → ℝ} {C : ℝ}
    (hu : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 u z)
    (hun : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ u z)
    (hub : ∀ z ∈ ball (0 : ℂ) 1, u z ≤ C)
    (hΔ : ∀ z ∈ ball (0 : ℂ) 1, (Δ u) z ≤ 0) :
    (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((-Real.log ‖z‖) * (-(Δ u) z))) ≤
      ENNReal.ofReal (2 * Real.pi * C) := by
  rw [disk_log_lintegral_polar]
  have hh := polar_green_le hu hun hub hΔ
  simpa only [polarGreenTarget, polarUnitDisk,
    lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)] using hh

end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

lemma second_direction_chain {f : ℝ → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hg : ContDiffAt ℝ 2 g z) (hf : ContDiffAt ℝ 2 f (g z)) (v : ℂ) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) z v v =
      deriv (deriv f) (g z) * (fderiv ℝ g z v) ^ 2 +
        deriv f (g z) * fderiv ℝ (fderiv ℝ g) z v v := by
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hfdd : DifferentiableAt ℝ (deriv f) (g z) :=
    (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgdd : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcompdd : DifferentiableAt ℝ (fderiv ℝ (f ∘ g)) z :=
    ((hf.comp z hg).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun w => fderiv ℝ (f ∘ g) w v) =ᶠ[𝓝 z]
      (fun w => deriv f (g w) * fderiv ℝ g w v) := by
    filter_upwards [hg.eventually (by norm_num),
      hgd.continuousAt (hf.eventually (by norm_num))] with w hgw hfw
    change ContDiffAt ℝ 2 f (g w) at hfw
    rw [fderiv_comp w (hfw.differentiableAt (by norm_num)) (hgw.differentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul, mul_comm]
  have hleft : fderiv ℝ (fun w => fderiv ℝ (f ∘ g) w v) z v =
      fderiv ℝ (fderiv ℝ (f ∘ g)) z v v := by
    rw [fderiv_clm_apply hcompdd (differentiableAt_const v)]
    simp
  have hright : fderiv ℝ (fun w => deriv f (g w) * fderiv ℝ g w v) z v =
      deriv (deriv f) (g z) * (fderiv ℝ g z v) ^ 2 +
        deriv f (g z) * fderiv ℝ (fderiv ℝ g) z v v := by
    have hmul := fderiv_fun_mul (hfdd.comp z hgd) (hgdd.clm_apply (differentiableAt_const v))
    simp only [Function.comp_apply] at hmul
    rw [hmul]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_comp z hfdd hgd, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
      fderiv_clm_apply hgdd (differentiableAt_const v)]
    simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  rw [← hleft, heq.fderiv_eq, hright]

 

lemma plane_laplacian_chain {f : ℝ → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hg : ContDiffAt ℝ 2 g z) (hf : ContDiffAt ℝ 2 f (g z)) :
    (Δ (f ∘ g)) z = deriv f (g z) * (Δ g) z +
      deriv (deriv f) (g z) * ((fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z I) ^ 2) := by
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [second_direction_chain hg hf 1, second_direction_chain hg hf I]
  ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian RealInnerProductSpace
namespace SLEExactGauge

lemma diskWeight_pos {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : 0 < diskWeight z := by
  have hn := mem_ball_zero_iff.mp hz
  dsimp [diskWeight]
  nlinarith [norm_nonneg z]

lemma diskWeight_contDiff : ContDiff ℝ 2 diskWeight :=
  contDiff_const.sub (contDiff_id.norm_sq ℂ)

lemma diskWeight_fderiv (z : ℂ) :
    fderiv ℝ diskWeight z = (-2 : ℝ) • innerSL ℝ z := by
  change fderiv ℝ (fun w : ℂ => 1 - ‖w‖ ^ 2) z = _
  rw [fderiv_const_sub, fderiv_norm_sq_apply]
  ext v
  simp [smul_apply, nsmul_eq_mul]
  ring

lemma diskWeight_laplacian (z : ℂ) : (Δ diskWeight) z = -4 := by
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have heq : fderiv ℝ diskWeight = fun z => (-2 : ℝ) • innerSL ℝ z := funext diskWeight_fderiv
  rw [heq]
  rw [fderiv_fun_const_smul (𝕜 := ℝ) (x := z)
    (innerSL ℝ (E := ℂ)).differentiableAt (-2 : ℝ)]
  simp only [ContinuousLinearMap.fderiv, smul_apply, smul_eq_mul]
  change -2 * inner ℝ (1 : ℂ) 1 + -2 * inner ℝ (I : ℂ) I = -4
  norm_num [real_inner_self_eq_norm_sq]

lemma log_diskWeight_laplacian {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (Δ (fun w => Real.log (diskWeight w))) z = -4 / diskWeight z ^ 2 := by
  have hg := diskWeight_contDiff.contDiffAt (x := z)
  have hf : ContDiffAt ℝ 2 Real.log (diskWeight z) := Real.contDiffAt_log.mpr (diskWeight_pos hz).ne'
  have hh := plane_laplacian_chain hg hf
  have hlog2 : deriv (deriv Real.log) (diskWeight z) = -(diskWeight z ^ 2)⁻¹ := by
    rw [Real.deriv_log']
    exact (hasDerivAt_inv (diskWeight_pos hz).ne').deriv
  change (Δ (fun w => Real.log (diskWeight w))) z = _ at hh
  rw [Real.deriv_log, hlog2, diskWeight_laplacian, diskWeight_fderiv] at hh
  rw [hh]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  have he : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by simpa [Complex.normSq_apply, sq] using Complex.sq_norm z
  have hwne : 1 - ‖z‖ ^ 2 ≠ 0 := (diskWeight_pos hz).ne'
  simp [diskWeight, Complex.mul_re]
  field_simp [hwne]
  nlinarith [he]

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology
namespace SLEExactGauge

lemma log_norm_direction_bound {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) (v : ℂ) :
    |fderiv ℝ (fun w => Real.log ‖f w‖) z v| ≤ ‖deriv f z / f z‖ * ‖v‖ := by
  have hnorm : DifferentiableAt ℝ (fun w : ℂ => ‖w‖) (f z) :=
    differentiableAt_id.norm ℂ hne
  have hd := ((hnorm.hasFDerivAt.comp z (hf.restrictScalars ℝ).hasFDerivAt).log (norm_ne_zero_iff.mpr hne)).fderiv
  change fderiv ℝ (fun w => Real.log ‖f w‖) z = _ at hd
  rw [hd]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, abs_mul,
    abs_inv, Function.comp_apply, abs_norm]
  have hbound := (fderiv ℝ (fun w : ℂ => ‖w‖) (f z)).le_opNorm (fderiv ℝ f z v)
  rw [norm_fderiv_norm hnorm, one_mul, Real.norm_eq_abs] at hbound
  have hvalue : fderiv ℝ f z v = v * deriv f z := by
    rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
    change fderiv ℂ f z v = _
    rw [fderiv_eq_smul_deriv, smul_eq_mul]
  rw [hvalue, norm_mul] at hbound
  rw [hvalue]
  calc
    ‖f z‖⁻¹ * |(fderiv ℝ (fun w : ℂ => ‖w‖) (f z)) (v * deriv f z)|
        ≤ ‖f z‖⁻¹ * (‖v‖ * ‖deriv f z‖) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (norm_nonneg _))
    _ = ‖deriv f z / f z‖ * ‖v‖ := by rw [norm_div]; ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma univalent_omitted_value_bound_ball {f : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball z r))
    (hi : InjOn f (ball z r)) (a : ℂ) (ha : a ∉ f '' ball z r) :
    r * ‖deriv f z‖ ≤ (128 * Real.pi) * ‖f z - a‖ := by
  let g : ℂ → ℂ := fun w => z + (r : ℂ) * w
  have hgmap : MapsTo g (ball 0 1) (ball z r) := by
    intro w hw
    rw [mem_ball_iff_norm]
    dsimp only [g]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left (by simpa [mem_ball_zero_iff] using hw) hr).trans_eq (mul_one r)
  have hgd : Differentiable ℂ g := (differentiable_const z).add ((differentiable_const (r : ℂ)).mul differentiable_id)
  have hgi : Function.Injective g := by
    intro v w he
    exact mul_left_cancel₀ (by exact_mod_cast hr.ne') (add_left_cancel he)
  have hfd : DifferentiableOn ℂ (f ∘ g) (ball 0 1) := hd.comp hgd.differentiableOn hgmap
  have hfi : InjOn (f ∘ g) (ball 0 1) := by
    intro v hv w hw he
    exact hgi (hi (hgmap hv) (hgmap hw) he)
  have hfa : a ∉ (f ∘ g) '' ball 0 1 := by
    rintro ⟨w, hw, he⟩
    exact ha ⟨g w, hgmap hw, he⟩
  have hg0 : g 0 = z := by simp [g]
  have hgder : HasDerivAt g (r : ℂ) 0 := by
    simpa [g] using ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add z
  have hfz := (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
  have hder : deriv (f ∘ g) 0 = deriv f z * (r : ℂ) := by
    have hfg : HasDerivAt f (deriv f z) (g 0) := by rw [hg0]; exact hfz
    exact (hfg.comp 0 hgder).deriv
  have hh := univalent_omitted_value_bound hfd hfi a hfa
  simpa [hder, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Function.comp_apply, hg0, mul_comm] using hh

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma logarithmic_lift_deriv_bound {f h : ℂ → ℂ} {a : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (ha : a ∉ f '' ball 0 1)
    (hh : ∀ z ∈ ball (0 : ℂ) 1, deriv h z = deriv f z / (f z - a))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (1 / 2 : ℝ)) :
    ‖deriv h z‖ ≤ 256 * Real.pi := by
  have hsub : ball z (1 / 2 : ℝ) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    apply mem_ball.mpr
    have hw' := mem_ball.mp hw
    have hz' := mem_closedBall.mp hz
    exact (dist_triangle w z 0).trans_lt (by linarith)
  have hz' : z ∈ ball (0 : ℂ) 1 := (closedBall_subset_ball (by norm_num)) hz
  have hn : f z - a ≠ 0 := by
    intro he
    exact ha ⟨z, hz', sub_eq_zero.mp he⟩
  have hb := univalent_omitted_value_bound_ball (by norm_num : (0 : ℝ) < 1 / 2)
    (hd.mono hsub) (hi.mono hsub) a (fun he => ha (image_mono hsub he))
  rw [hh z hz', norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr
  linarith

lemma logarithmic_lift_second_bound {f h : ℂ → ℂ} {a : ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (ha : a ∉ f '' ball 0 1) (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hh : ∀ z ∈ ball (0 : ℂ) 1, deriv h z = deriv f z / (f z - a)) :
    ‖deriv (deriv h) 0‖ ≤ 512 * Real.pi := by
  have hs : closedBall (0 : ℂ) (1 / 2 : ℝ) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 2)
    ((hhd.deriv isOpen_ball).diffContOnCl_ball hs)
    (fun z hz => logarithmic_lift_deriv_bound hd hi ha hh (sphere_subset_closedBall hz))
  convert hb using 1 <;> first | rfl | ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma exists_omitted_near_of_inverse {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hf0 : deriv f 0 ≠ 0)
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ z ∈ ball (0 : ℂ) 1, g (f z) = z) :
    ∃ a : ℂ, a ∉ f '' ball 0 1 ∧ ‖f 0 - a‖ < 2 * ‖deriv f 0‖ := by
  have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self (by norm_num)
  have hn : 0 < ‖deriv f 0‖ := norm_pos_iff.mpr hf0
  have hr : 0 < 2 * ‖deriv f 0‖ := by positivity
  by_contra! hcontra
  have hsub : ball (f 0) (2 * ‖deriv f 0‖) ⊆ f '' ball 0 1 := by
    intro a ha
    by_contra hnot
    have hh := hcontra a hnot
    have hn' : ‖f 0 - a‖ < 2 * ‖deriv f 0‖ := by
      simpa only [mem_ball_iff_norm, norm_sub_rev] using ha
    linarith
  have hgd := hg.mono hsub
  have hgm : MapsTo g (ball (f 0) (2 * ‖deriv f 0‖)) (closedBall (g (f 0)) 1) := by
    intro w hw
    obtain ⟨z, hz', rfl⟩ := hsub hw
    rw [hgf z hz', hgf 0 hz]
    exact ball_subset_closedBall hz'
  have hbound := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hgm hr
  have hdf := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hdg := (hgd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
  have heq : (g ∘ f) =ᶠ[𝓝 (0 : ℂ)] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with z hz'
    exact hgf z hz'
  have hprod : deriv g (f 0) * deriv f 0 = 1 :=
    ((hdg.comp 0 hdf).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id 0)
  have hnormprod : ‖deriv g (f 0)‖ * ‖deriv f 0‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hh := (le_div_iff₀ hr).mp hbound
  nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma preSchwarzian_bound_of_inverse {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hf0 : deriv f 0 ≠ 0)
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ z ∈ ball (0 : ℂ) 1, g (f z) = z) :
    ‖deriv (deriv f) 0 / deriv f 0‖ ≤ 1280 * Real.pi := by
  obtain ⟨a, ha, hnear⟩ := exists_omitted_near_of_inverse hd hf0 hg hgf
  have hz : (0 : ℂ) ∈ ball 0 1 := mem_ball_self (by norm_num)
  have hnon (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : f z - a ≠ 0 := by
    intro he
    exact ha ⟨z, hz, sub_eq_zero.mp he⟩
  obtain ⟨h, hhd, hexp, hh⟩ := exists_holomorphic_log_on_ball (by norm_num : (0 : ℝ) < 1)
    (hd.sub_const a) hnon
  have hh' (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      deriv h z = deriv f z / (f z - a) := by
    rw [hh z hz]
    congr 1
    exact ((hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const a).deriv
  have hdf := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hddf := ((hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have heq : deriv h =ᶠ[𝓝 (0 : ℂ)] (fun z => deriv f z / (f z - a)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with z hz'
    exact hh' z hz'
  have hsecond : deriv (deriv h) 0 =
      (deriv (deriv f) 0 * (f 0 - a) - deriv f 0 * deriv f 0) / (f 0 - a) ^ 2 :=
    ((hddf.div (hdf.sub_const a) (hnon 0 hz)).congr_of_eventuallyEq heq).deriv
  have halg : deriv (deriv f) 0 / deriv f 0 =
      deriv (deriv h) 0 / deriv h 0 + deriv h 0 := by
    rw [hsecond, hh' 0 hz]
    field_simp [hf0, hnon 0 hz]
    ring
  have hfirst := logarithmic_lift_deriv_bound hd hi ha hh'
    (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have htwo := logarithmic_lift_second_bound hd hi ha hhd hh'
  have hlower : (1 / 2 : ℝ) ≤ ‖deriv h 0‖ := by
    rw [hh' 0 hz, norm_div]
    apply (le_div_iff₀ (norm_pos_iff.mpr (hnon 0 hz))).mpr
    linarith
  have hpos : 0 < ‖deriv h 0‖ := by linarith
  have hratio : ‖deriv (deriv h) 0‖ / ‖deriv h 0‖ ≤ 1024 * Real.pi := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [Real.pi_pos]
  rw [halg]
  calc
    ‖deriv (deriv h) 0 / deriv h 0 + deriv h 0‖ ≤
        ‖deriv (deriv h) 0‖ / ‖deriv h 0‖ + ‖deriv h 0‖ := by
      simpa only [norm_div] using norm_add_le (deriv (deriv h) 0 / deriv h 0) (deriv h 0)
    _ ≤ 1280 * Real.pi := by linarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma preSchwarzian_bound_ball {f g : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball z r))
    (hi : InjOn f (ball z r)) (hf0 : deriv f z ≠ 0)
    (hg : DifferentiableOn ℂ g (f '' ball z r))
    (hgf : ∀ w ∈ ball z r, g (f w) = w) :
    r * ‖deriv (deriv f) z / deriv f z‖ ≤ 1280 * Real.pi := by
  let A : ℂ → ℂ := fun w => z + (r : ℂ) * w
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hAmap : MapsTo A (ball 0 1) (ball z r) := by
    intro w hw
    rw [mem_ball_iff_norm]
    dsimp only [A]
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hw) hr).trans_eq (mul_one r)
  have hAd : Differentiable ℂ A :=
    (differentiable_const z).add ((differentiable_const (r : ℂ)).mul differentiable_id)
  have hAder (w : ℂ) : HasDerivAt A (r : ℂ) w := by
    simpa [A] using ((hasDerivAt_id w).const_mul (r : ℂ)).const_add z
  have hAi : Function.Injective A := by
    intro v w he
    exact mul_left_cancel₀ hrC (add_left_cancel he)
  have hA0 : A 0 = z := by simp [A]
  let F := f ∘ A
  let G := fun w => (g w - z) / (r : ℂ)
  have hFd : DifferentiableOn ℂ F (ball 0 1) := hd.comp hAd.differentiableOn hAmap
  have hFi : InjOn F (ball 0 1) := by
    intro v hv w hw he
    exact hAi (hi (hAmap hv) (hAmap hw) he)
  have hsub : F '' ball 0 1 ⊆ f '' ball z r := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨A v, hAmap hv, rfl⟩
  have hGd : DifferentiableOn ℂ G (F '' ball 0 1) :=
    ((hg.mono hsub).sub_const z).div_const (r : ℂ)
  have hGF : ∀ w ∈ ball (0 : ℂ) 1, G (F w) = w := by
    intro w hw
    dsimp [G, F]
    rw [hgf _ (hAmap hw)]
    dsimp [A]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hrC]
  have hdf := (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
  have hFder : deriv F 0 = deriv f z * (r : ℂ) := by
    have hh : HasDerivAt f (deriv f z) (A 0) := by rw [hA0]; exact hdf
    exact (hh.comp 0 (hAder 0)).deriv
  have hbound := preSchwarzian_bound_of_inverse hFd hFi
    (by rw [hFder]; exact mul_ne_zero hf0 hrC) hGd hGF
  have hFsecond : deriv (deriv F) 0 = deriv (deriv f) z * (r : ℂ) ^ 2 := by
    have heq : deriv F =ᶠ[𝓝 (0 : ℂ)] (fun w => deriv f (A w) * (r : ℂ)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 1))] with w hw
      exact (((hd.differentiableAt (isOpen_ball.mem_nhds (hAmap hw))).hasDerivAt).comp w (hAder w)).deriv
    have hdd := ((hd.deriv isOpen_ball).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
    have hh : HasDerivAt (deriv f) (deriv (deriv f) z) (A 0) := by rw [hA0]; exact hdd
    have hh' := (((hh.comp 0 (hAder 0)).mul_const (r : ℂ)).congr_of_eventuallyEq heq).deriv
    simpa only [pow_two, mul_assoc] using hh'
  have halg : deriv (deriv F) 0 / deriv F 0 = (r : ℂ) * (deriv (deriv f) z / deriv f z) := by
    rw [hFsecond, hFder]
    field_simp
  rw [halg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hbound
  exact hbound

 

lemma disk_preSchwarzian_bound {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hfz : deriv f z ≠ 0) :
    ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) z / deriv f z) - 2 * star z‖ ≤
      2560 * Real.pi + 2 := by
  have hn := mem_ball_zero_iff.mp hz
  have hr : 0 < 1 - ‖z‖ := by linarith
  have hsub : ball z (1 - ‖z‖) ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    apply mem_ball.mpr
    have hh := mem_ball.mp hw
    have hd0 : dist z 0 = ‖z‖ := dist_zero_right z
    exact (dist_triangle w z 0).trans_lt (by linarith)
  have hb := preSchwarzian_bound_ball hr (hd.mono hsub) (hi.mono hsub) hfz
    (hg.mono (image_mono hsub)) (fun w hw => hgf w (hsub hw))
  have hrad : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  calc
    _ ≤ ‖((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * (deriv (deriv f) z / deriv f z)‖ + ‖2 * star z‖ := norm_sub_le _ _
    _ = (1 - ‖z‖ ^ 2) * ‖deriv (deriv f) z / deriv f z‖ + 2 * ‖z‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrad,
        norm_ofNat, norm_star]
    _ ≤ 2560 * Real.pi + 2 := by
      have hprod := mul_le_mul_of_nonneg_right (show (1 + ‖z‖) ≤ 2 by linarith)
        (mul_nonneg hr.le (norm_nonneg (deriv (deriv f) z / deriv f z)))
      nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian RealInnerProductSpace
namespace SLEExactGauge

lemma diskLogRadius_contDiffAt {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    ContDiffAt ℝ 2 (diskLogRadius f) z := by
  have hh := (((hd.deriv isOpen_ball).analyticAt (isOpen_ball.mem_nhds hz))).harmonicAt_log_norm hne
  exact (diskWeight_contDiff.contDiffAt.log (diskWeight_pos hz).ne').add hh.1

end SLEExactGauge
end
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

end AngularLocalization
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

end SLEExactGauge
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
open scoped Topology Laplacian RealInnerProductSpace
namespace SLEExactGauge
lemma diskLogRadius_laplacian {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    (Δ (diskLogRadius f)) z = -4 / diskWeight z ^ 2 := by
  have hh := (((hd.deriv isOpen_ball).analyticAt (isOpen_ball.mem_nhds hz))).harmonicAt_log_norm hne
  have he := hh.2.eq_of_nhds
  change (Δ (fun w => Real.log ‖deriv f w‖)) z = 0 at he
  rw [show diskLogRadius f = (fun w => Real.log (diskWeight w)) +
      (fun w => Real.log ‖deriv f w‖) from rfl,
    (diskWeight_contDiff.contDiffAt.log (diskWeight_pos hz).ne').laplacian_add hh.1,
    he, add_zero, log_diskWeight_laplacian hz]

lemma diskLogRadius_exp {f : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    Real.exp (diskLogRadius f z) = diskWeight z * ‖deriv f z‖ := by
  simp only [diskLogRadius, Real.exp_add, Real.exp_log (diskWeight_pos hz),
    Real.exp_log (norm_pos_iff.mpr hne)]

lemma log_diskWeight_direction_bound {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (v : ℂ) :
    diskWeight z * |fderiv ℝ (fun w => Real.log (diskWeight w)) z v| ≤ 2 * ‖v‖ := by
  have hh := ((diskWeight_contDiff.differentiable (by norm_num) z).hasFDerivAt.log
    (diskWeight_pos hz).ne').fderiv
  rw [hh, diskWeight_fderiv]
  simp only [smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos (diskWeight_pos hz),
    abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  rw [← mul_assoc, mul_inv_cancel₀ (diskWeight_pos hz).ne', one_mul]
  have hinner := abs_real_inner_le_norm z v
  have hn : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  change 2 * |inner ℝ z v| ≤ 2 * ‖v‖
  calc
    _ ≤ 2 * (‖z‖ * ‖v‖) := mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ ≤ 2 * ‖v‖ := by nlinarith [norm_nonneg v]

lemma disk_preSchwarzian_weight {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    diskWeight z * ‖deriv (deriv f) z / deriv f z‖ ≤ 2560 * Real.pi + 4 := by
  have hh := disk_preSchwarzian_bound hd hi hg hgf hz hne
  have hb := norm_add_le
    (((diskWeight z : ℝ) : ℂ) * (deriv (deriv f) z / deriv f z) - 2 * star z) (2 * star z)
  rw [sub_add_cancel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (diskWeight_pos hz)] at hb
  have he : ‖(2 : ℂ) * star z‖ = 2 * ‖z‖ := by simp
  rw [he] at hb
  have hn := mem_ball_zero_iff.mp hz
  change ‖((diskWeight z : ℝ) : ℂ) * (deriv (deriv f) z / deriv f z) - 2 * star z‖ ≤ _ at hh
  linarith

lemma diskLogRadius_direction_bound {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) (v : ℂ) :
    diskWeight z * |fderiv ℝ (diskLogRadius f) z v| ≤ (2560 * Real.pi + 6) * ‖v‖ := by
  have hdd := ((hd.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hz))
  have hn : DifferentiableAt ℝ (fun w => Real.log ‖deriv f w‖) z :=
    ((hdd.restrictScalars ℝ).norm ℂ hne).log (norm_ne_zero_iff.mpr hne)
  have hw : DifferentiableAt ℝ (fun w => Real.log (diskWeight w)) z :=
    (diskWeight_contDiff.differentiable (by norm_num) z).log (diskWeight_pos hz).ne'
  have hp := disk_preSchwarzian_weight hd hi hg hgf hz hne
  have h1 := log_diskWeight_direction_bound hz v
  have h2 := log_norm_direction_bound hdd hne v
  have he : fderiv ℝ (diskLogRadius f) z =
      fderiv ℝ (fun w => Real.log (diskWeight w)) z +
        fderiv ℝ (fun w => Real.log ‖deriv f w‖) z := by
    exact fderiv_fun_add hw hn
  rw [he, add_apply]
  have hb := mul_le_mul_of_nonneg_left (abs_add_le
    (fderiv ℝ (fun w => Real.log (diskWeight w)) z v)
    (fderiv ℝ (fun w => Real.log ‖deriv f w‖) z v)) (diskWeight_pos hz).le
  have hb2 := mul_le_mul_of_nonneg_left h2 (diskWeight_pos hz).le
  have hb3 := mul_le_mul_of_nonneg_right hp (norm_nonneg v)
  nlinarith

lemma diskLogRadius_gradient_bound {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) :
    diskWeight z ^ 2 * ((fderiv ℝ (diskLogRadius f) z 1) ^ 2 +
      (fderiv ℝ (diskLogRadius f) z I) ^ 2) ≤ 2 * (2560 * Real.pi + 6) ^ 2 := by
  have h1 := diskLogRadius_direction_bound hd hi hg hgf hz hne 1
  have hI := diskLogRadius_direction_bound hd hi hg hgf hz hne I
  simp only [norm_one, norm_I, mul_one] at h1 hI
  have hw := (diskWeight_pos hz).le
  have hc : 0 ≤ 2560 * Real.pi + 6 := by positivity
  have h1' := sq_le_sq₀ (mul_nonneg hw (abs_nonneg _)) hc |>.mpr h1
  have hI' := sq_le_sq₀ (mul_nonneg hw (abs_nonneg _)) hc |>.mpr hI
  simp only [mul_pow, sq_abs] at h1' hI'
  nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric
open scoped Topology
namespace SLEExactGauge



lemma layerProfile_hasDeriv (r q x : ℝ) :
    HasDerivAt (layerProfile r q) (layerProfileDeriv r q x) x := by
  have ht := (((hasDerivAt_id x).sub_const (Real.log r)).const_mul q).exp
  have hp := ((ht.const_mul (r ^ 2)).div (ht.const_add 1)
    (by positivity : 1 + Real.exp (q * (x - Real.log r)) ≠ 0))
  have hne : 1 + Real.exp (q * (x - Real.log r)) ≠ 0 := by positivity
  convert! hp using 1
  all_goals try with_reducible_and_instances rfl
  simp only [layerProfileDeriv, id_eq, mul_one]
  field_simp [hne]
  ring

lemma layerProfileDeriv_hasDeriv (r q x : ℝ) :
    HasDerivAt (layerProfileDeriv r q)
      (q * layerProfileDeriv r q x *
        ((1 - Real.exp (q * (x - Real.log r))) /
          (1 + Real.exp (q * (x - Real.log r))))) x := by
  have ht := (((hasDerivAt_id x).sub_const (Real.log r)).const_mul q).exp
  have hp := ((ht.const_mul (q * r ^ 2)).div ((ht.const_add 1).pow 2)
    (by positivity : (1 + Real.exp (q * (x - Real.log r))) ^ 2 ≠ 0))
  have hne : 1 + Real.exp (q * (x - Real.log r)) ≠ 0 := by positivity
  convert! hp using 1
  all_goals try with_reducible_and_instances rfl
  simp only [layerProfileDeriv, id_eq, Pi.pow_apply, mul_one,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hne]
  ring

lemma layerProfile_contDiff (r q : ℝ) : ContDiff ℝ 2 (layerProfile r q) := by
  unfold layerProfile
  fun_prop (disch := intros; positivity)

lemma layerProfile_nonneg (r q x : ℝ) : 0 ≤ layerProfile r q x := by
  unfold layerProfile
  positivity

lemma layerProfile_le (r q x : ℝ) : layerProfile r q x ≤ r ^ 2 := by
  unfold layerProfile
  apply (div_le_iff₀ (by positivity)).mpr
  have ht := Real.exp_pos (q * (x - Real.log r))
  nlinarith [sq_nonneg r]

lemma layerProfile_deriv_nonneg {r q x : ℝ} (hq : 0 ≤ q) :
    0 ≤ deriv (layerProfile r q) x := by
  rw [(layerProfile_hasDeriv r q x).deriv]
  unfold layerProfileDeriv
  positivity

lemma layerProfile_second_le {r q x : ℝ} (hq : 0 ≤ q) :
    deriv (deriv (layerProfile r q)) x ≤ q * deriv (layerProfile r q) x := by
  have he : deriv (layerProfile r q) = layerProfileDeriv r q :=
    funext fun x => (layerProfile_hasDeriv r q x).deriv
  rw [he, (layerProfileDeriv_hasDeriv r q x).deriv]
  have ht : 0 < Real.exp (q * (x - Real.log r)) := Real.exp_pos _
  have hratio : (1 - Real.exp (q * (x - Real.log r))) /
      (1 + Real.exp (q * (x - Real.log r))) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hd : 0 ≤ layerProfileDeriv r q x := by unfold layerProfileDeriv; positivity
  simpa using mul_le_mul_of_nonneg_left hratio (mul_nonneg hq hd)

lemma layerProfile_deriv_lower {r q x : ℝ}
    (hr : 0 < r) (hq : 0 ≤ q) (hq2 : q ≤ 2) (hx : x ≤ Real.log r) :
    q / 4 * Real.exp x ^ 2 ≤ deriv (layerProfile r q) x := by
  rw [(layerProfile_hasDeriv r q x).deriv]
  let t := Real.exp (q * (x - Real.log r))
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr hx)
  have hlow : Real.exp (2 * (x - Real.log r)) ≤ t := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_right hq2 (sub_nonpos.mpr hx)
  have he : Real.exp x ^ 2 = r ^ 2 * Real.exp (2 * (x - Real.log r)) := by
    have h2 (y : ℝ) : Real.exp (2 * y) = Real.exp y ^ 2 := by simpa using Real.exp_nat_mul y 2
    rw [mul_sub, Real.exp_sub, h2, h2, Real.exp_log hr]
    field_simp [hr.ne']
  have he' : Real.exp x ^ 2 ≤ r ^ 2 * t := by rw [he]; exact mul_le_mul_of_nonneg_left hlow (sq_nonneg r)
  change q / 4 * Real.exp x ^ 2 ≤ q * r ^ 2 * t / (1 + t) ^ 2
  apply (le_div_iff₀ (by positivity)).mpr
  have hden : (1 + t) ^ 2 ≤ 4 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg (div_nonneg hq (by norm_num : (0 : ℝ) ≤ 4)) (sq_nonneg (Real.exp x)))
  have hh' := mul_le_mul_of_nonneg_left he' hq
  nlinarith

end SLEExactGauge

end

 
section

open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
namespace SLEExactGauge

lemma layerExponent_pos : 0 < layerExponent := by unfold layerExponent; positivity
lemma layerExponent_le_one : layerExponent ≤ 1 := by
  unfold layerExponent
  apply (inv_le_one₀ (by positivity)).mpr
  nlinarith [sq_nonneg (2560 * Real.pi + 6)]
lemma layerExponent_gradient : layerExponent * (2 * (2560 * Real.pi + 6) ^ 2) ≤ 1 := by
  unfold layerExponent
  have hp : 0 < 2 * (2560 * Real.pi + 6) ^ 2 + 1 := by positivity
  have he := inv_mul_cancel₀ hp.ne'
  have hn : 0 ≤ (2 * (2560 * Real.pi + 6) ^ 2 + 1)⁻¹ := by positivity
  nlinarith

lemma diskLayerBarrier_bounds (f : ℂ → ℂ) (r : ℝ) (z : ℂ) :
    0 ≤ diskLayerBarrier f r z ∧ diskLayerBarrier f r z ≤ r ^ 2 :=
  ⟨layerProfile_nonneg _ _ _, layerProfile_le _ _ _⟩

lemma diskLayerBarrier_contDiffAt {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) (r : ℝ) :
    ContDiffAt ℝ 2 (diskLayerBarrier f r) z :=
  (layerProfile_contDiff r layerExponent).contDiffAt.comp z (diskLogRadius_contDiffAt hd hz hne)

lemma diskLayerBarrier_laplacian_le {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) (r : ℝ) :
    (Δ (diskLayerBarrier f r)) z ≤
      -3 * deriv (layerProfile r layerExponent) (diskLogRadius f z) / diskWeight z ^ 2 := by
  let b := deriv (layerProfile r layerExponent) (diskLogRadius f z)
  let c := deriv (deriv (layerProfile r layerExponent)) (diskLogRadius f z)
  let S := (fderiv ℝ (diskLogRadius f) z 1) ^ 2 + (fderiv ℝ (diskLogRadius f) z I) ^ 2
  have hb : 0 ≤ b := layerProfile_deriv_nonneg layerExponent_pos.le
  have hc : c ≤ layerExponent * b := layerProfile_second_le layerExponent_pos.le
  have hS : 0 ≤ S := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hgrad := diskLogRadius_gradient_bound hd hi hg hgf hz hne
  change diskWeight z ^ 2 * S ≤ 2 * (2560 * Real.pi + 6) ^ 2 at hgrad
  have hterm : c * (diskWeight z ^ 2 * S) ≤ b := calc
    _ ≤ (layerExponent * b) * (diskWeight z ^ 2 * S) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hS)
    _ ≤ (layerExponent * b) * (2 * (2560 * Real.pi + 6) ^ 2) :=
      mul_le_mul_of_nonneg_left hgrad (mul_nonneg layerExponent_pos.le hb)
    _ = b * (layerExponent * (2 * (2560 * Real.pi + 6) ^ 2)) := by ring
    _ ≤ b * 1 := mul_le_mul_of_nonneg_left layerExponent_gradient hb
    _ = b := mul_one b
  have hh := plane_laplacian_chain (diskLogRadius_contDiffAt hd hz hne)
    ((layerProfile_contDiff r layerExponent).contDiffAt)
  rw [diskLogRadius_laplacian hd hz hne] at hh
  change (Δ (diskLayerBarrier f r)) z = b * (-4 / diskWeight z ^ 2) + c * S at hh
  rw [hh]
  change b * (-4 / diskWeight z ^ 2) + c * S ≤ -3 * b / diskWeight z ^ 2
  have hw : 0 < diskWeight z ^ 2 := sq_pos_of_pos (diskWeight_pos hz)
  apply (le_div_iff₀ hw).mpr
  field_simp [(diskWeight_pos hz).ne']
  nlinarith [hterm]

lemma diskLayerBarrier_superharmonic {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0) (r : ℝ) :
    (Δ (diskLayerBarrier f r)) z ≤ 0 := by
  apply (diskLayerBarrier_laplacian_le hd hi hg hgf hz hne r).trans
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (layerProfile_deriv_nonneg layerExponent_pos.le))
    (sq_nonneg _)

lemma diskLayerBarrier_layer_lower {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : deriv f z ≠ 0)
    {r : ℝ} (hr : 0 < r) (hsmall : diskWeight z * ‖deriv f z‖ ≤ r) :
    layerExponent / 4 * ‖deriv f z‖ ^ 2 ≤ -(Δ (diskLayerBarrier f r)) z := by
  have hx : diskLogRadius f z ≤ Real.log r := by
    apply Real.exp_le_exp.mp
    rw [diskLogRadius_exp hz hne, Real.exp_log hr]
    exact hsmall
  have hlow := layerProfile_deriv_lower hr layerExponent_pos.le
    (layerExponent_le_one.trans (by norm_num : (1 : ℝ) ≤ 2)) hx
  rw [diskLogRadius_exp hz hne, mul_pow] at hlow
  have hh := diskLayerBarrier_laplacian_le hd hi hg hgf hz hne r
  have hb := layerProfile_deriv_nonneg (r := r) (x := diskLogRadius f z) layerExponent_pos.le
  have hw : 0 < diskWeight z ^ 2 := sq_pos_of_pos (diskWeight_pos hz)
  have hh' := (le_div_iff₀ hw).mp hh
  apply (mul_le_mul_iff_right₀ hw).mp
  nlinarith [hlow, hh']

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology Laplacian ENNReal
namespace SLEExactGauge

lemma conformal_layer_measurable {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (r : ℝ) :
    MeasurableSet {z | z ∈ ball (0 : ℂ) 1 ∧ diskWeight z * ‖deriv f z‖ ≤ r} := by
  have hcont : ContinuousOn (fun z => diskWeight z * ‖deriv f z‖) (ball (0 : ℂ) 1) :=
    diskWeight_contDiff.continuous.continuousOn.mul (hd.deriv isOpen_ball).continuousOn.norm
  rcases continuousOn_iff_isClosed.mp hcont (Iic r) isClosed_Iic with ⟨K, hK, heK⟩
  change MeasurableSet (ball (0 : ℂ) 1 ∩ (fun z => diskWeight z * ‖deriv f z‖) ⁻¹' Iic r)
  rw [inter_comm, heK]
  exact hK.measurableSet.inter measurableSet_ball

lemma disk_conformal_layer_green_le {f g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hg : DifferentiableOn ℂ g (f '' ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    (hne : ∀ w ∈ ball (0 : ℂ) 1, deriv f w ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ z in {z | z ∈ ball (0 : ℂ) 1 ∧ diskWeight z * ‖deriv f z‖ ≤ r},
      ENNReal.ofReal ((-Real.log ‖z‖) * ‖deriv f z‖ ^ 2)) ≤
      ENNReal.ofReal ((8 * Real.pi / layerExponent) * r ^ 2) := by
  let S := {z | z ∈ ball (0 : ℂ) 1 ∧ diskWeight z * ‖deriv f z‖ ≤ r}
  let V := diskLayerBarrier f r
  have hV := disk_green_le (fun z hz => diskLayerBarrier_contDiffAt hd hz (hne z hz) r)
    (fun z _ => (diskLayerBarrier_bounds f r z).1)
    (fun z _ => (diskLayerBarrier_bounds f r z).2)
    (fun z hz => diskLayerBarrier_superharmonic hd hi hg hgf hz (hne z hz) r)
  have hS : MeasurableSet S := conformal_layer_measurable hd r
  have hc : 0 ≤ (4 : ℝ) / layerExponent := div_nonneg (by norm_num) layerExponent_pos.le
  calc
    _ ≤ ∫⁻ z in S, ENNReal.ofReal ((4 / layerExponent) *
        ((-Real.log ‖z‖) * (-(Δ V) z))) := by
      apply setLIntegral_mono' hS
      intro z hz
      apply ENNReal.ofReal_le_ofReal
      have hl := diskLayerBarrier_layer_lower hd hi hg hgf hz.1 (hne z hz.1) hr hz.2
      have h'd : ‖deriv f z‖ ^ 2 ≤ 4 / layerExponent * (-(Δ V) z) := by
        have he : (4 / layerExponent) * (layerExponent / 4 * ‖deriv f z‖ ^ 2) =
            ‖deriv f z‖ ^ 2 := by field_simp [layerExponent_pos.ne']
        rw [← he]
        exact mul_le_mul_of_nonneg_left hl hc
      have hlog : 0 ≤ -Real.log ‖z‖ := neg_nonneg.mpr
        (Real.log_nonpos (norm_nonneg z) (mem_ball_zero_iff.mp hz.1).le)
      nlinarith [mul_le_mul_of_nonneg_left h'd hlog]
    _ ≤ ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((4 / layerExponent) *
        ((-Real.log ‖z‖) * (-(Δ V) z))) :=
      lintegral_mono_set (fun z hz => hz.1)
    _ = ENNReal.ofReal (4 / layerExponent) *
        ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((-Real.log ‖z‖) * (-(Δ V) z)) := by
      simp only [ENNReal.ofReal_mul hc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (4 / layerExponent) * ENNReal.ofReal (2 * Real.pi * r ^ 2) :=
      mul_le_mul_right hV _
    _ = _ := by rw [← ENNReal.ofReal_mul hc]; congr 1; ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

lemma complex_derivative_det (c : ℂ) :
    (((1 : ℂ →L[ℂ] ℂ).smulRight c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

lemma conformal_disk_area_change {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (H : ℂ → ℝ≥0∞) :
    (∫⁻ w in f '' ball (0 : ℂ) 1, H w) =
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) * H (f z) := by
  have hf (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      HasFDerivWithinAt f (((1 : ℂ →L[ℂ] ℂ).smulRight (deriv f z)).restrictScalars ℝ)
        (ball (0 : ℂ) 1) z :=
    ((hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hf hi H
  simpa only [complex_derivative_det, abs_pow, abs_norm] using hh

lemma chart_deriv_ne_zero {D : Set ℂ} {f g : ℂ → ℂ}
    (hD : IsOpen D) (hd : DifferentiableOn ℂ f (ball 0 1))
    (hg : DifferentiableOn ℂ g D) (hm : MapsTo f (ball 0 1) D)
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : deriv f z ≠ 0 := by
  have hfz := (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hgz := (hg.differentiableAt (hD.mem_nhds (hm hz))).hasDerivAt
  have heq : (g ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hgf w hw
  have he : deriv g (f z) * deriv f z = 1 :=
    ((hgz.comp z hfz).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id z)
  intro hn
  simp only [hn, mul_zero, zero_ne_one] at he

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology
namespace SLEExactGauge

 

lemma disk_radius_le_frontier_distance {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hfront : (frontier D).Nonempty)
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hImage : f '' ball (0 : ℂ) 1 = D) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    diskWeight z * ‖deriv f z‖ ≤ (256 * Real.pi) * infDist (f z) (frontier D) := by
  have hc : 0 < 256 * Real.pi := by positivity
  have hr : 0 < 1 - ‖z‖ := sub_pos.mpr (mem_ball_zero_iff.mp hz)
  have hsub : ball z (1 - ‖z‖) ⊆ ball (0 : ℂ) 1 :=
    ball_subset_ball' (by simp only [dist_zero_right]; linarith)
  have hh : diskWeight z * ‖deriv f z‖ / (256 * Real.pi) ≤ infDist (f z) (frontier D) := by
    apply (le_infDist hfront).mpr
    intro a ha
    have hnot : a ∉ f '' ball z (1 - ‖z‖) := by
      intro hm
      have hIn : a ∈ D := hImage ▸ image_mono hsub hm
      exact ha.2 (by simpa only [hD.interior_eq] using hIn)
    have hk := univalent_omitted_value_bound_ball hr (hd.mono hsub) (hi.mono hsub) a hnot
    apply (div_le_iff₀ hc).mpr
    rw [dist_eq_norm]
    unfold diskWeight
    have hn := mul_nonneg (sq_nonneg (1 - ‖z‖)) (norm_nonneg (deriv f z))
    nlinarith [hk, hn]
  have hb := (div_le_iff₀ hc).mp hh
  simpa only [mul_comm] using hb

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace SLEExactGauge

lemma centered_boundary_layer_green_le {D : Set ℂ} {f g : ℂ → ℂ}
    (hD : IsOpen D) (hfront : (frontier D).Nonempty)
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hg : DifferentiableOn ℂ g D)
    (hmf : MapsTo f (ball 0 1) D) (hmg : MapsTo g D (ball 0 1))
    (hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w)
    (hfg : ∀ w ∈ D, f (g w) = w)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in {w | w ∈ D ∧ infDist w (frontier D) ≤ r},
      ENNReal.ofReal (-Real.log ‖g w‖)) ≤ ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
  have hImage : f '' ball (0 : ℂ) 1 = D := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hmf hz
    · intro hw
      exact ⟨g w, hmg hw, hfg w hw⟩
  have hi : InjOn f (ball 0 1) := by
    intro z hz w hw he
    simpa only [hgf z hz, hgf w hw] using congrArg g he
  have hgrange : DifferentiableOn ℂ g (f '' ball (0 : ℂ) 1) := by rw [hImage]; exact hg
  have hne : ∀ z ∈ ball (0 : ℂ) 1, deriv f z ≠ 0 :=
    fun z hz => chart_deriv_ne_zero hD hd hg hmf hgf hz
  let L := {w | w ∈ D ∧ infDist w (frontier D) ≤ r}
  let T := {z | z ∈ ball (0 : ℂ) 1 ∧ diskWeight z * ‖deriv f z‖ ≤ (256 * Real.pi) * r}
  have hL : MeasurableSet L := hD.measurableSet.inter
    (measurableSet_le (continuous_infDist_pt (frontier D)).measurable measurable_const)
  have hT : MeasurableSet T := conformal_layer_measurable hd _
  have hLD : L ⊆ D := fun w hw => hw.1
  have hTB : T ⊆ ball (0 : ℂ) 1 := fun z hz => hz.1
  have hscale : 0 < (256 * Real.pi) * r := by positivity
  calc
    _ = ∫⁻ w in D, L.indicator (fun w => ENNReal.ofReal (-Real.log ‖g w‖)) w := by
      rw [lintegral_indicator hL, Measure.restrict_restrict hL, inter_eq_left.mpr hLD]
    _ = ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f z‖ ^ 2) *
        L.indicator (fun w => ENNReal.ofReal (-Real.log ‖g w‖)) (f z) := by
      rw [← hImage]
      exact conformal_disk_area_change hd hi _
    _ ≤ ∫⁻ z in ball (0 : ℂ) 1, T.indicator
        (fun z => ENNReal.ofReal ((-Real.log ‖z‖) * ‖deriv f z‖ ^ 2)) z := by
      apply setLIntegral_mono' measurableSet_ball
      intro z hz
      by_cases hl : f z ∈ L
      · have ht : z ∈ T := ⟨hz, (disk_radius_le_frontier_distance hD hfront hd hi hImage hz).trans
          (mul_le_mul_of_nonneg_left hl.2 (by positivity))⟩
        simp only [indicator_of_mem hl, indicator_of_mem ht, hgf z hz]
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        exact le_of_eq (congrArg ENNReal.ofReal (mul_comm _ _))
      · simp only [indicator_of_notMem hl, mul_zero]
        exact bot_le
    _ = ∫⁻ z in T, ENNReal.ofReal ((-Real.log ‖z‖) * ‖deriv f z‖ ^ 2) := by
      rw [lintegral_indicator hT, Measure.restrict_restrict hT, inter_eq_left.mpr hTB]
    _ ≤ ENNReal.ofReal ((8 * Real.pi / layerExponent) * ((256 * Real.pi) * r) ^ 2) :=
      disk_conformal_layer_green_le hd hi hgrange hgf hne hscale
    _ = _ := by congr 1; unfold layerGreenConstant; ring

end SLEExactGauge

end

 
section

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma halfPlane_denominator_ne {w v : ℂ} (hw : 0 < w.im) (hv : 0 < v.im) :
    v - star w ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hh
  linarith

lemma halfPlaneToDisk_maps {w : ℂ} (hw : 0 < w.im) :
    MapsTo (halfPlaneToDisk w) upperHalfPlane (ball 0 1) := by
  intro v hv
  exact mem_ball_zero_iff.mpr (upper_mobius_norm_lt_one hv hw)

lemma halfPlaneToDisk_differentiable {w : ℂ} (hw : 0 < w.im) :
    DifferentiableOn ℂ (halfPlaneToDisk w) upperHalfPlane :=
  (differentiableOn_id.sub_const w).div (differentiableOn_id.sub_const (star w))
    (fun _ hv => halfPlane_denominator_ne hw hv)

lemma halfPlaneToDisk_diskToHalfPlane {w ζ : ℂ} (hw : 0 < w.im)
    (hζ : ζ ∈ ball (0 : ℂ) 1) : halfPlaneToDisk w (diskToHalfPlane w ζ) = ζ := by
  have hn : w - star w ≠ 0 := halfPlane_denominator_ne hw hw
  have hd := disk_denominator_ne hζ
  have hv := halfPlane_denominator_ne hw (diskToHalfPlane_maps hw hζ)
  unfold halfPlaneToDisk
  apply (div_eq_iff hv).mpr
  unfold diskToHalfPlane
  field_simp [hd]
  ring

end SLEExactGauge

end

 
section

open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
namespace SLEExactGauge



lemma hasDerivWithinAt_log_norm {f : ℝ → ℂ} {v : ℂ} {S : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f v S t) (h0 : f t ≠ 0) :
    HasDerivWithinAt (fun s => Real.log ‖f s‖) (v / f t).re S t := by
  have hh := (hf.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))).div_const 2
  have he : (fun s => Real.log (‖f s‖ ^ 2) / 2) = (fun s => Real.log ‖f s‖) := by
    funext s
    rw [Real.log_pow]
    ring
  rw [he] at hh
  apply hh.congr_deriv
  rw [Complex.div_re, Complex.sq_norm, real_inner_eq_re_inner ℂ]
  simp only [inner, Complex.star_def, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma hasDerivWithinAt_conj {f : ℝ → ℂ} {v : ℂ} {S : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f v S t) :
    HasDerivWithinAt (fun s => conj (f s)) (conj v) S t := by
  exact Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t hf

lemma hasDerivWithinAt_log_norm_div {f g : ℝ → ℂ} {v w : ℂ} {S : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f v S t) (hg : HasDerivWithinAt g w S t)
    (hf0 : f t ≠ 0) (hg0 : g t ≠ 0) :
    HasDerivWithinAt (fun s => Real.log ‖f s / g s‖)
      (v / f t - w / g t).re S t := by
  apply (hasDerivWithinAt_log_norm (hf.div hg hg0) (div_ne_zero hf0 hg0)).congr_deriv
  congr 1
  change ((v * g t - f t * w) / g t ^ 2) / (f t / g t) = v / f t - w / g t
  field_simp

lemma green_decrease_algebra (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) (hne : z ≠ w) :
    ((2 / z - conj (2 / w)) / (z - conj w) - (2 / z - 2 / w) / (z - w)).re =
      -4 * (z.im / ‖z‖ ^ 2) * (w.im / ‖w‖ ^ 2) := by
  have hz0 : z ≠ 0 := fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hz
  have hw0 : w ≠ 0 := fun h => by simp only [h, Complex.zero_im, lt_self_iff_false] at hw
  have hcw0 : conj w ≠ 0 := by simpa using hw0
  have hn : z - w ≠ 0 := sub_ne_zero.mpr hne
  have hn' : z - conj w ≠ 0 := by
    intro hh
    have he := congrArg Complex.im (sub_eq_zero.mp hh)
    simp only [Complex.conj_im] at he
    linarith
  have h₁ : (2 / z - conj (2 / w)) / (z - conj w) = -2 / (z * conj w) := by
    simp only [map_div₀, map_ofNat]
    field_simp
    ring
  have h₂ : (2 / z - 2 / w) / (z - w) = -2 / (z * w) := by
    field_simp
    ring
  rw [h₁, h₂]
  simp only [Complex.sub_re, Complex.div_re, Complex.neg_re, Complex.neg_im,
    Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_mul, Complex.normSq_conj, Complex.sq_norm]
  norm_num
  ring

 

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
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
namespace SLEExactGauge
lemma halfPlaneGreen_derivative {f g : ℝ → ℂ} {S : Set ℝ} {t u : ℝ}
    (hf : HasDerivWithinAt f (2 / (f t - (u : ℂ))) S t)
    (hg : HasDerivWithinAt g (2 / (g t - (u : ℂ))) S t)
    (hfi : 0 < (f t).im) (hgi : 0 < (g t).im) (hne : f t ≠ g t) :
    HasDerivWithinAt (fun s => halfPlaneGreen (f s) (g s))
      (-4 * ((f t).im / ‖f t - (u : ℂ)‖ ^ 2) *
        ((g t).im / ‖g t - (u : ℂ)‖ ^ 2)) S t := by
  have hn : f t - g t ≠ 0 := sub_ne_zero.mpr hne
  have hnc : f t - conj (g t) ≠ 0 := by
    intro h
    have he := congrArg Complex.im (sub_eq_zero.mp h)
    simp only [Complex.conj_im] at he
    linarith
  have hd := hasDerivWithinAt_log_norm_div (hf.sub (hasDerivWithinAt_conj hg)) (hf.sub hg) hnc hn
  apply hd.congr_deriv
  have h₁ : f t - conj (g t) = (f t - (u : ℂ)) - conj (g t - (u : ℂ)) := by
    simp only [map_sub, Complex.conj_ofReal]
    ring
  have h₂ : f t - g t = (f t - (u : ℂ)) - (g t - (u : ℂ)) := by ring
  change ((2 / (f t - (u : ℂ)) - conj (2 / (g t - (u : ℂ)))) / (f t - conj (g t)) -
    (2 / (f t - (u : ℂ)) - 2 / (g t - (u : ℂ))) / (f t - g t)).re = _
  rw [h₁, h₂, green_decrease_algebra _ _ (by simpa using hfi) (by simpa using hgi)
    (sub_left_inj.not.mpr hne)]
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]

 

theorem IsCapacityTwoWitness.green_kernel_derivative
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z w : ℂ)
    (hz : z ∈ survivingDomain γ t) (hw' : w ∈ survivingDomain γ t) (hne : z ≠ w) :
    HasDerivWithinAt (fun s : ℝ => halfPlaneGreen (G (Real.toNNReal s) z) (G (Real.toNNReal s) w))
      (-4 * ((G t z).im / ‖G t z - (U t : ℂ)‖ ^ 2) *
        ((G t w).im / ‖G t w - (U t : ℂ)‖ ^ 2)) (Ici 0) (t : ℝ) := by
  rcases hw with ⟨hc, h0, him, hG, hF, hGmap, hFmap, hinv, hinv', hinit, hode, hnorm, htip⟩
  have hneq : G t z ≠ G t w := by
    intro he
    apply hne
    rw [← hinv t z hz, he, hinv t w hw']
  simpa only [Real.toNNReal_coe] using halfPlaneGreen_derivative
    (f := fun s => G (Real.toNNReal s) z) (g := fun s => G (Real.toNNReal s) w)
    (S := Ici 0) (t := (t : ℝ)) (u := U t)
    (by simpa only [Real.toNNReal_coe] using hode t z hz)
    (by simpa only [Real.toNNReal_coe] using hode t w hw')
    (by simpa only [Real.toNNReal_coe, upperHalfPlane, Set.mem_ofPred_eq] using hGmap t hz)
    (by simpa only [Real.toNNReal_coe, upperHalfPlane, Set.mem_ofPred_eq] using hGmap t hw')
    (by simpa only [Real.toNNReal_coe] using hneq)

end SLEExactGauge

end

 
section

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal NNReal ComplexConjugate
namespace SLEExactGauge

lemma diskToHalfPlane_halfPlaneToDisk {w v : ℂ} (hw : 0 < w.im) (hv : 0 < v.im) :
    diskToHalfPlane w (halfPlaneToDisk w v) = v := by
  have hd := halfPlane_denominator_ne hw hv
  have hζ := halfPlaneToDisk_maps hw hv
  have he := disk_denominator_ne hζ
  unfold diskToHalfPlane
  apply (div_eq_iff he).mpr
  unfold halfPlaneToDisk
  field_simp [hd]
  ring

lemma halfPlaneGreen_eq_disk (z w : ℂ) :
    halfPlaneGreen z w = -Real.log ‖halfPlaneToDisk z w‖ := by
  have hn : ‖z - conj w‖ = ‖w - conj z‖ := by
    calc
      _ = ‖conj (z - conj w)‖ := (Complex.norm_conj _).symm
      _ = ‖-(w - conj z)‖ := by congr 1; simp only [map_sub, Complex.conj_conj]; ring
      _ = _ := norm_neg _
  rw [halfPlaneGreen, halfPlaneToDisk, Complex.star_def, norm_div, norm_div,
    hn, norm_sub_rev z w, ← Real.log_inv, inv_div]

lemma halfPlaneGreen_nonneg {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 ≤ halfPlaneGreen z w := by
  rw [halfPlaneGreen_eq_disk]
  exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (upper_mobius_norm_lt_one hw hz).le)

 

lemma halfplane_boundary_layer_green_le {D : Set ℂ} {G F : ℂ → ℂ}
    (hD : IsOpen D) (hfront : (frontier D).Nonempty)
    (hG : DifferentiableOn ℂ G D) (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hGm : MapsTo G D upperHalfPlane) (hFm : MapsTo F upperHalfPlane D)
    (hFG : ∀ w ∈ D, F (G w) = w) (hGF : ∀ w ∈ upperHalfPlane, G (F w) = w)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ D) :
    (∫⁻ w in {w | w ∈ D ∧ infDist w (frontier D) ≤ r},
      ENNReal.ofReal (halfPlaneGreen (G z) (G w))) ≤
      ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
  let f := F ∘ diskToHalfPlane (G z)
  let g := halfPlaneToDisk (G z) ∘ G
  have hz' : 0 < (G z).im := hGm hz
  have hf : DifferentiableOn ℂ f (ball 0 1) :=
    hF.comp (diskToHalfPlane_differentiable _) (diskToHalfPlane_maps hz')
  have hg : DifferentiableOn ℂ g D := (halfPlaneToDisk_differentiable hz').comp hG hGm
  have hfm : MapsTo f (ball 0 1) D := hFm.comp (diskToHalfPlane_maps hz')
  have hgm : MapsTo g D (ball 0 1) := (halfPlaneToDisk_maps hz').comp hGm
  have hgf : ∀ w ∈ ball (0 : ℂ) 1, g (f w) = w := by
    intro w hw
    dsimp only [g, f, Function.comp_apply]
    rw [hGF _ (diskToHalfPlane_maps hz' hw), halfPlaneToDisk_diskToHalfPlane hz' hw]
  have hfg : ∀ w ∈ D, f (g w) = w := by
    intro w hw
    dsimp only [g, f, Function.comp_apply]
    rw [diskToHalfPlane_halfPlaneToDisk hz' (hGm hw), hFG w hw]
  have hh := centered_boundary_layer_green_le hD hfront hf hg hfm hgm hgf hfg hr
  simpa only [g, Function.comp_apply, ← halfPlaneGreen_eq_disk] using hh

 

theorem IsCapacityTwoWitness.boundary_layer_green
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : z ∈ survivingDomain γ t) :
    (∫⁻ w in {w | w ∈ survivingDomain γ t ∧ infDist w (frontier (survivingDomain γ t)) ≤ r},
      ENNReal.ofReal (halfPlaneGreen (G t z) (G t w))) ≤
      ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
  have hD := isOpen_survivingDomain hw.1 t
  have hDne : survivingDomain γ t ≠ univ := by
    intro he
    have h0 : (0 : ℂ) ∈ survivingDomain γ t := by rw [he]; exact mem_univ _
    exact (lt_irrefl (0 : ℝ)) h0.1.1
  have hfront : (frontier (survivingDomain γ t)).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨z, hz⟩, hDne⟩
  rcases hw with ⟨hc, h0, him, hG, hF, hGmap, hFmap, hinv, hinv', hrest⟩
  exact halfplane_boundary_layer_green_le hD hfront (hG t) (hF t) (hGmap t) (hFmap t)
    (hinv t) (hinv' t) hr hz

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.poissonRate_continuousOn
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    ContinuousOn (fun t : ℝ => chartPoissonRate U G t.toNNReal z) (Icc 0 (T : ℝ)) := by
  have hc := h.time_continuousOn T z hz
  have huc : Continuous (fun t : ℝ => (U t.toNNReal : ℂ)) :=
    Complex.continuous_ofReal.comp (hU.comp continuous_real_toNNReal)
  exact (Complex.continuous_im.comp_continuousOn hc).div
    ((hc.sub huc.continuousOn).norm.pow 2)
    (fun t ht => pow_ne_zero 2 (norm_ne_zero_iff.mpr
      (h.centered_ne_zero _ z (h.live_at_real_time T z hz t ht.2))))

lemma IsCapacityTwoWitness.poissonRate_nonneg
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) : 0 ≤ chartPoissonRate U G t z :=
  div_nonneg (h.imag_positive t z hz).le (sq_nonneg _)

lemma IsCapacityTwoWitness.green_pair_integral
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (s T : ℝ≥0) (hsT : s ≤ T) (z w : ℂ)
    (hz : z ∈ survivingDomain γ T) (hw : w ∈ survivingDomain γ T) (hne : z ≠ w) :
    4 * (∫ t in (s : ℝ)..(T : ℝ),
      chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w) =
      halfPlaneGreen (G s z) (G s w) - halfPlaneGreen (G T z) (G T w) := by
  have hsub : Icc (s : ℝ) (T : ℝ) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc s.coe_nonneg le_rfl
  have hab : (s : ℝ) ≤ T := hsT
  let K : ℝ → ℝ := fun t => halfPlaneGreen (G t.toNNReal z) (G t.toNNReal w)
  let R : ℝ → ℝ := fun t => chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w
  have hr : ContinuousOn R (Icc (s : ℝ) (T : ℝ)) :=
    ((h.poissonRate_continuousOn hU T z hz).mul (h.poissonRate_continuousOn hU T w hw)).mono hsub
  have hd : ∀ t ∈ Icc (s : ℝ) (T : ℝ), HasDerivWithinAt K (-4 * R t) (Ici 0) t := by
    intro t ht
    have ht0 : 0 ≤ t := s.coe_nonneg.trans ht.1
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have hh := h.green_kernel_derivative t.toNNReal z w
      (survivingDomain_antitone γ htT hz) (survivingDomain_antitone γ htT hw) hne
    simpa only [K, R, chartPoissonRate, Real.coe_toNNReal _ ht0, mul_assoc] using hh
  have hc : ContinuousOn K (Icc (s : ℝ) (T : ℝ)) := by
    intro t ht
    exact ((hd t ht).mono (fun x hx => le_trans s.coe_nonneg hx.1)).continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hc
    (fun t ht => (hd t ⟨ht.1.le, ht.2.le⟩).mono (fun x hx =>
      le_trans (s.coe_nonneg.trans ht.1.le) hx.le))
    ((continuousOn_const.mul hr).intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_const_mul] at he
  dsimp only [K] at he
  simp only [Real.toNNReal_coe] at he
  change -4 * (∫ t in (s : ℝ)..(T : ℝ), R t) = _ at he
  change 4 * (∫ t in (s : ℝ)..(T : ℝ), R t) = _
  linarith

 

theorem IsCapacityTwoWitness.green_pair_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (s T : ℝ≥0) (hsT : s ≤ T) (z w : ℂ)
    (hz : z ∈ survivingDomain γ T) (hw : w ∈ survivingDomain γ T) (hne : z ≠ w) :
    (∫ t in (s : ℝ)..(T : ℝ),
      chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w) ≤
      halfPlaneGreen (G s z) (G s w) / 4 := by
  have he := h.green_pair_integral hU s T hsT z w hz hw hne
  have hp := halfPlaneGreen_nonneg (h.imag_positive T z hz) (h.imag_positive T w hw)
  linarith

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma lintegral_lower_interval_le (a : ℝ) (S : Set ℝ) (f : ℝ → ℝ≥0∞)
    (C : ℝ≥0∞) (hS : S ⊆ Ici a)
    (hdown : ∀ T ∈ S, Icc a T ⊆ S)
    (hbound : ∀ T ∈ S, (∫⁻ t in Icc a T, f t) ≤ C) :
    (∫⁻ t in S, f t) ≤ C := by
  classical
  by_cases hmax : ∃ T ∈ S, ∀ t ∈ S, t ≤ T
  · obtain ⟨T, hT, hmax⟩ := hmax
    exact (lintegral_mono_set (show S ⊆ Icc a T from fun t ht => ⟨hS ht, hmax t ht⟩)).trans (hbound T hT)
  · let Q := {q : ℚ | (q : ℝ) ∈ S}
    have hcover : S = ⋃ q : Q, Icc a (q : ℝ) := by
      ext t
      constructor
      · intro ht
        have hex : ∃ u ∈ S, t < u := by
          by_contra hh
          apply hmax
          refine ⟨t, ht, ?_⟩
          intro u hu
          exact le_of_not_gt (fun h => hh ⟨u, hu, h⟩)
        obtain ⟨u, hu, htu⟩ := hex
        obtain ⟨q, htq, hqu⟩ := exists_rat_btwn htu
        have hq : q ∈ Q := hdown u hu ⟨(hS ht).trans htq.le, hqu.le⟩
        exact mem_iUnion.mpr ⟨⟨q, hq⟩, ⟨hS ht, htq.le⟩⟩
      · intro ht
        obtain ⟨q, hq⟩ := mem_iUnion.mp ht
        exact hdown (q : ℝ) q.property hq
    have hd : Directed (· ⊆ ·) (fun q : Q => Icc a (q : ℝ)) := by
      intro q r
      rcases le_total (q : ℝ) (r : ℝ) with hqr | hrq
      · exact ⟨r, Icc_subset_Icc le_rfl hqr, Subset.rfl⟩
      · exact ⟨q, Subset.rfl, Icc_subset_Icc le_rfl hrq⟩
    rw [hcover, setLIntegral_iUnion_of_directed f hd]
    exact iSup_le (fun q => hbound _ q.property)

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

 

theorem IsCapacityTwoWitness.live_green_pair_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (s : ℝ≥0) (z w : ℂ) (hne : z ≠ w) :
    (∫⁻ t in {t : ℝ | (s : ℝ) ≤ t ∧ z ∈ survivingDomain γ t.toNNReal ∧
      w ∈ survivingDomain γ t.toNNReal},
      ENNReal.ofReal (chartPoissonRate U G t.toNNReal z *
        chartPoissonRate U G t.toNNReal w)) ≤
      ENNReal.ofReal (halfPlaneGreen (G s z) (G s w) / 4) := by
  apply lintegral_lower_interval_le
  · exact fun _ ht => ht.1
  · intro T hT t ht
    have hle : t.toNNReal ≤ T.toNNReal := Real.toNNReal_mono ht.2
    exact ⟨ht.1, survivingDomain_antitone γ hle hT.2.1,
      survivingDomain_antitone γ hle hT.2.2⟩
  · intro T hT
    have hT0 : 0 ≤ T := s.coe_nonneg.trans hT.1
    have hsT : s ≤ T.toNNReal := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hT0]
      exact hT.1
    let R : ℝ → ℝ := fun t => chartPoissonRate U G t.toNNReal z *
      chartPoissonRate U G t.toNNReal w
    have hc : ContinuousOn R (Icc (s : ℝ) T) := by
      have hh := (h.poissonRate_continuousOn hU T.toNNReal z hT.2.1).mul
        (h.poissonRate_continuousOn hU T.toNNReal w hT.2.2)
      rw [Real.coe_toNNReal _ hT0] at hh
      exact hh.mono (Icc_subset_Icc s.coe_nonneg le_rfl)
    have hn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc (s : ℝ) T)] R := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hle := Real.toNNReal_mono ht.2
      exact mul_nonneg
        (h.poissonRate_nonneg _ z (survivingDomain_antitone γ hle hT.2.1))
        (h.poissonRate_nonneg _ w (survivingDomain_antitone γ hle hT.2.2))
    change (∫⁻ t in Icc (s : ℝ) T, ENNReal.ofReal (R t)) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc) hn]
    apply ENNReal.ofReal_le_ofReal
    have hb := h.green_pair_bound hU s T.toNNReal hsT z w hT.2.1 hT.2.2 hne
    rw [Real.coe_toNNReal _ hT0, intervalIntegral.integral_of_le hT.1,
      ← integral_Icc_eq_integral_Ioc] at hb
    exact hb

end SLEExactGauge

end

 
section

open Set Filter Metric MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma greenExponent_ge_one {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    1 ≤ greenExponent κ := by
  unfold greenExponent
  have : (2 : ℝ) ≤ 8 / κ := (le_div_iff₀ hκ).mpr (by linarith)
  linarith

 

lemma IsCapacityTwoWitness.green_coefficient_le_poisson
    (h : IsCapacityTwoWitness U γ G F) (_hU : Continuous U)
    {κ r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hr : 0 < r)
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ t)
    (hR : r ≤ fullRadius G t z) :
    |greenBrownianCoefficient κ U γ G t z| ≤
      (Real.sqrt κ * greenExponent κ * r ^ (-codimension κ)) *
        chartPoissonRate U G t z := by
  let Z := G t z - (U t : ℂ)
  have hn : 0 < ‖Z‖ := norm_pos_iff.mpr (h.centered_ne_zero t z hz)
  have hi : 0 < Z.im := by
    simpa only [Z, Complex.sub_im, Complex.ofReal_im, sub_zero] using h.imag_positive t z hz
  have hs : 0 ≤ Real.sin Z.arg := by rw [Complex.sin_arg]; positivity
  have hs1 : Real.sin Z.arg ≤ 1 := Real.sin_le_one _
  have hp : 0 ≤ codimension κ := by unfold codimension dimension; linarith
  have ha := greenExponent_ge_one hκ hκ4
  have hM : greenDensity κ U γ G t z ≤
      r ^ (-codimension κ) * (Z.im / ‖Z‖) := by
    rw [greenDensity, ite_eq_left hz]
    change fullRadius G t z ^ (-codimension κ) * (Real.sin Z.arg) ^ greenExponent κ ≤ _
    calc
      _ ≤ r ^ (-codimension κ) * Real.sin Z.arg :=
        mul_le_mul (Real.rpow_le_rpow_of_nonpos hr hR (neg_nonpos.mpr hp))
          (Real.rpow_le_self_of_le_one hs hs1 ha) (Real.rpow_nonneg hs _)
          (Real.rpow_nonneg hr.le _)
      _ = _ := by rw [Complex.sin_arg]
  have hMn : 0 ≤ greenDensity κ U γ G t z := greenDensity_nonneg h κ t z
  have hX : |Z.re| ≤ ‖Z‖ := Complex.abs_re_le_norm Z
  have hC : 0 ≤ Real.sqrt κ * greenExponent κ := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  change |Real.sqrt κ * greenExponent κ * Z.re / ‖Z‖ ^ 2 *
    greenDensity κ U γ G t z| ≤ _
  rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hC, show |‖Z‖ ^ 2| = ‖Z‖ ^ 2 from abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg hMn]
  calc
    _ ≤ (Real.sqrt κ * greenExponent κ * ‖Z‖ / ‖Z‖ ^ 2) *
        (r ^ (-codimension κ) * (Z.im / ‖Z‖)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hX hC) (sq_nonneg _)
      · exact hM
      · exact hMn
      · positivity
    _ = (Real.sqrt κ * greenExponent κ * r ^ (-codimension κ)) *
        chartPoissonRate U G t z := by
      have hZi : Z.im = (G t z).im := by simp [Z]
      unfold chartPoissonRate
      change _ = (Real.sqrt κ * greenExponent κ * r ^ (-codimension κ)) *
        ((G t z).im / ‖Z‖ ^ 2)
      rw [hZi]
      field_simp

 

lemma surviving_frontier_distance_le_past
    (t a : ℝ≥0) (hat : a ≤ t) (z : ℂ) (hz : z ∈ survivingDomain γ t) :
    infDist z (frontier (survivingDomain γ t)) ≤ dist (γ a) z := by
  have hn : γ a ∉ survivingDomain γ t := by
    intro ha
    exact ha.1.2 ⟨a, ⟨bot_le, hat⟩, rfl⟩
  have hDne : survivingDomain γ t ≠ univ := by
    intro he
    exact hn (he ▸ mem_univ _)
  obtain ⟨w, hw, he⟩ := exists_mem_frontier_infDist_compl_eq_dist hz hDne
  calc
    _ ≤ dist z w := infDist_le_dist_of_mem hw
    _ = infDist z (survivingDomain γ t)ᶜ := he.symm
    _ ≤ dist z (γ a) := infDist_le_dist_of_mem hn
    _ = _ := dist_comm _ _

 

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

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

lemma chartApprox_measurable (n : ℕ) : Measurable (c.chartApprox n) := by
  have hQ := (c.measurable n).comp
    ((NNReal.continuous_coe.measurable.comp measurable_fst).prodMk measurable_snd)
  have hre := Complex.measurable_ofReal.comp (Complex.measurable_re.comp hQ.fst)
  have him := Complex.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp (Complex.measurable_im.comp hQ.fst))
  exact Measurable.ite (c.valid_measurable n) (hre.add (him.mul_const _)) measurable_const

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
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)

lemma jointChart_measurable : Measurable c.jointChart :=
  (StronglyMeasurable.limUnder (fun n => (c.chartApprox_measurable n).stronglyMeasurable)).measurable

lemma jointChart_eq {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hUc : Continuous (fun t => U t ω))
    (hw : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (t : ℝ≥0) (z : ℂ) :
    c.jointChart (t, z, ω) = if z ∈ survivingDomain γ t then G t z else 0 := by
  classical
  unfold jointChart
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_nhds_of_eventually_eq
  by_cases hz : z ∈ survivingDomain γ t
  · filter_upwards [c.eventually_valid_agrees ω hUc hw t z hz] with n hn
    rw [ite_eq_left hz, chartApprox, ite_eq_left hn.1, hn.2, logCoordinates_re, logCoordinates_im,
      Real.exp_log (hw.imag_positive t z hz)]
    exact Complex.re_add_im _
  · filter_upwards [] with n
    have hn : ¬ c.valid n t z ω := fun hv => hz (c.live_of_valid ω hUc hw n t z hv)
    simp only [chartApprox, ite_eq_right hn, ite_eq_right hz]

include c

 

lemma live_measurable
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hUc : ∀ ω, Continuous (fun t => U t ω))
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => U t ω) (γ ω) (G ω) (F ω)) :
    MeasurableSet {p : ℝ≥0 × (ℂ × Ω) | p.2.1 ∈ survivingDomain (γ p.2.2) p.1} := by
  have he : {p : ℝ≥0 × (ℂ × Ω) | p.2.1 ∈ survivingDomain (γ p.2.2) p.1} =
      ⋃ n : ℕ, {p | c.valid n p.1 p.2.1 p.2.2} := by
    ext p
    constructor
    · intro hp
      obtain ⟨n, hn⟩ := (c.eventually_valid_agrees p.2.2 (hUc _) (hw _) p.1 p.2.1 hp).exists
      exact mem_iUnion.mpr ⟨n, hn.1⟩
    · intro hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact c.live_of_valid p.2.2 (hUc _) (hw _) n p.1 p.2.1 hn
  rw [he]
  exact MeasurableSet.iUnion (c.valid_measurable)

end SpatialClippedFamily
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

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

lemma IsCapacityTwoWitness.slab_coefficient_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε)
    (r : ℝ) (z : ℂ) (hy : ε ≤ z.im) (t : ℝ≥0) :
    |spatialSlabCoefficient κ U γ G r ε t z| ≤
      if z ∈ survivingDomain γ t then
        (Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) * chartPoissonRate U G t z
      else 0 := by
  by_cases ha : spatialHitTime γ z r ≤ t ∧ (t : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧
      z ∈ survivingDomain γ t
  · rw [spatialSlabCoefficient, ite_eq_left ha, ite_eq_left ha.2.2]
    exact h.green_coefficient_le_poisson hU hκ hκ4 hε t z ha.2.2
      (h.radius_before_spatial_hit hU z ε hε hy t ha.2.2 ha.2.1)
  · rw [spatialSlabCoefficient, ite_eq_right ha, abs_zero]
    split_ifs with hz
    · exact mul_nonneg (by
        have hg := greenExponent_ge_one hκ hκ4
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
          (Real.rpow_nonneg hε.le _)) (h.poissonRate_nonneg t z hz)
    · exact le_rfl

 

theorem IsCapacityTwoWitness.slab_pair_later_start
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε)
    (r : ℝ) (z w : ℂ) (hzy : ε ≤ z.im) (hwy : ε ≤ w.im) (hne : z ≠ w)
    (s : ℝ≥0) (hs : spatialHitTime γ z r = s) :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
      spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2) *
        ENNReal.ofReal (halfPlaneGreen (G s z) (G s w) / 4) := by
  let C := Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)
  let S := {t : ℝ | (s : ℝ) ≤ t ∧ z ∈ survivingDomain γ t.toNNReal ∧
    w ∈ survivingDomain γ t.toNNReal}
  let f := fun t : ℝ => ENNReal.ofReal (chartPoissonRate U G t.toNNReal z *
    chartPoissonRate U G t.toNNReal w)
  have hC : 0 ≤ C := by
    have hg := greenExponent_ge_one hκ hκ4
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (Real.rpow_nonneg hε.le _)
  have hpoint (t : ℝ) (ht0 : 0 ≤ t) : ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
      spatialSlabCoefficient κ U γ G r ε t.toNNReal w| ≤
      S.indicator (fun t => ENNReal.ofReal (C ^ 2) * f t) t := by
    by_cases ha : spatialHitTime γ z r ≤ t.toNNReal ∧
        (t.toNNReal : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧ z ∈ survivingDomain γ t.toNNReal
    · by_cases hb : spatialHitTime γ w r ≤ t.toNNReal ∧
          (t.toNNReal : WithTop ℝ≥0) ≤ spatialHitTime γ w ε ∧ w ∈ survivingDomain γ t.toNNReal
      · have hst : (s : ℝ) ≤ t := by
          have hst' : s ≤ t.toNNReal := WithTop.coe_le_coe.mp (hs ▸ ha.1)
          rw [← Real.coe_toNNReal t ht0]
          exact hst'
        rw [Set.indicator_of_mem (show t ∈ S from ⟨hst, ha.2.2, hb.2.2⟩),
          ← ENNReal.ofReal_mul (sq_nonneg C)]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_mul]
        have hz := h.slab_coefficient_bound hU hκ hκ4 hε r z hzy t.toNNReal
        have hw := h.slab_coefficient_bound hU hκ hκ4 hε r w hwy t.toNNReal
        rw [ite_eq_left ha.2.2] at hz
        rw [ite_eq_left hb.2.2] at hw
        calc
          _ ≤ (C * chartPoissonRate U G t.toNNReal z) *
              (C * chartPoissonRate U G t.toNNReal w) :=
            mul_le_mul hz hw (abs_nonneg _) (mul_nonneg hC (h.poissonRate_nonneg _ z ha.2.2))
          _ = _ := by ring
      · simp only [spatialSlabCoefficient, ite_eq_right hb, mul_zero, abs_zero, ENNReal.ofReal_zero, zero_le]
    · simp only [spatialSlabCoefficient, ite_eq_right ha, zero_mul, abs_zero, ENNReal.ofReal_zero, zero_le]
  calc
    _ ≤ ∫⁻ t in Ici (0 : ℝ), S.indicator (fun t => ENNReal.ofReal (C ^ 2) * f t) t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact hpoint t ht
    _ ≤ ∫⁻ t, S.indicator (fun t => ENNReal.ofReal (C ^ 2) * f t) t :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ ∫⁻ t in S, ENNReal.ofReal (C ^ 2) * f t := lintegral_indicator_le _ _
    _ = ENNReal.ofReal (C ^ 2) * ∫⁻ t in S, f t := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul le_rfl (h.live_green_pair_bound hU s z w hne) (by positivity) (by positivity)

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

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal

end


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StochasticIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stochastic Integrals for chordal SLE. -/

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
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.spatial_later_kernel_integral
    (h : IsCapacityTwoWitness U γ G F) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (∫⁻ w, spatialLaterKernel γ G r z w) ≤ ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
  classical
  by_cases ht : spatialHitTime γ z r = ⊤
  · simp only [spatialLaterKernel, ite_eq_left ht, lintegral_zero, zero_le]
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp ht
  by_cases hz : z ∈ survivingDomain γ s
  · let L := {w | w ∈ survivingDomain γ s ∧ infDist w (frontier (survivingDomain γ s)) ≤ r}
    have hp (w : ℂ) : spatialLaterKernel γ G r z w ≤
        L.indicator (fun w => ENNReal.ofReal (halfPlaneGreen (G s z) (G s w))) w := by
      rw [spatialLaterKernel, ite_eq_right ht, ← hs, WithTop.untopD_coe]
      by_cases ha : z ∈ survivingDomain γ s ∧ w ∈ survivingDomain γ s ∧ spatialHitTime γ w r ≤ s
      · rw [ite_eq_left ha]
        obtain ⟨v, hv, he⟩ := (spatialHitTime_le_iff h.1 w r s).mp ha.2.2
        have hw : w ∈ L := ⟨ha.2.1, (surviving_frontier_distance_le_past s v hv.2 w ha.2.1).trans_eq he⟩
        rw [Set.indicator_of_mem hw]
      · rw [ite_eq_right ha]
        exact zero_le
    calc
      _ ≤ ∫⁻ w, L.indicator (fun w => ENNReal.ofReal (halfPlaneGreen (G s z) (G s w))) w :=
        lintegral_mono hp
      _ ≤ ∫⁻ w in L, ENNReal.ofReal (halfPlaneGreen (G s z) (G s w)) := lintegral_indicator_le _ _
      _ ≤ _ := h.boundary_layer_green s hr hz
  · have he (w : ℂ) : spatialLaterKernel γ G r z w = 0 := by
      rw [spatialLaterKernel, ite_eq_right ht, ← hs, WithTop.untopD_coe]
      simp only [hz, false_and, ite_false]
    simp only [he, lintegral_zero, zero_le]

lemma slab_product_zero_of_not_live_at_start
    (κ r ε : ℝ) (z w : ℂ) (s : ℝ≥0) (hs : spatialHitTime γ z r = s)
    (hn : ¬ (z ∈ survivingDomain γ s ∧ w ∈ survivingDomain γ s)) (t : ℝ≥0) :
    spatialSlabCoefficient κ U γ G r ε t z * spatialSlabCoefficient κ U γ G r ε t w = 0 := by
  by_cases ha : spatialHitTime γ z r ≤ t ∧ (t : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧
      z ∈ survivingDomain γ t
  · by_cases hb : spatialHitTime γ w r ≤ t ∧ (t : WithTop ℝ≥0) ≤ spatialHitTime γ w ε ∧
        w ∈ survivingDomain γ t
    · have hst : s ≤ t := WithTop.coe_le_coe.mp (hs ▸ ha.1)
      exact (hn ⟨survivingDomain_antitone γ hst ha.2.2, survivingDomain_antitone γ hst hb.2.2⟩).elim
    · simp only [spatialSlabCoefficient, ite_eq_right hb, mul_zero]
  · simp only [spatialSlabCoefficient, ite_eq_right ha, zero_mul]

lemma IsCapacityTwoWitness.slab_pair_ordered
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε)
    (r : ℝ) (z w : ℂ) (hzy : ε ≤ z.im) (hwy : ε ≤ w.im) (hne : z ≠ w)
    (horder : spatialHitTime γ w r ≤ spatialHitTime γ z r) :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
      spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        spatialLaterKernel γ G r z w := by
  classical
  by_cases ht : spatialHitTime γ z r = ⊤
  · have he (t : ℝ) : spatialSlabCoefficient κ U γ G r ε t.toNNReal z = 0 := by
      have hn : ¬ (spatialHitTime γ z r ≤ t.toNNReal ∧
          (t.toNNReal : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧ z ∈ survivingDomain γ t.toNNReal) := by
        intro hh
        rw [ht] at hh
        exact WithTop.coe_ne_top (top_le_iff.mp hh.1)
      exact ite_eq_right hn
    simp only [he, zero_mul, abs_zero, ENNReal.ofReal_zero, lintegral_zero, zero_le]
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp ht
  by_cases hl : z ∈ survivingDomain γ s ∧ w ∈ survivingDomain γ s
  · have hord : spatialHitTime γ w r ≤ s := hs ▸ horder
    have he : spatialLaterKernel γ G r z w = ENNReal.ofReal (halfPlaneGreen (G s z) (G s w)) := by
      rw [spatialLaterKernel, ite_eq_right ht, ← hs, WithTop.untopD_coe, ite_eq_left ⟨hl.1, hl.2, hord⟩]
    rw [he]
    have hb := h.slab_pair_later_start hU hκ hκ4 hε r z w hzy hwy hne s hs.symm
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (by norm_num))]
    congr 1
    ring
  · simp only [slab_product_zero_of_not_live_at_start κ r ε z w s hs.symm hl,
      abs_zero, ENNReal.ofReal_zero, lintegral_zero, zero_le]

 

lemma IsCapacityTwoWitness.slab_pair_kernel_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε)
    (r : ℝ) (z w : ℂ) (hzy : ε ≤ z.im) (hwy : ε ≤ w.im) (hne : z ≠ w) :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
      spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (spatialLaterKernel γ G r z w + spatialLaterKernel γ G r w z) := by
  rcases le_total (spatialHitTime γ w r) (spatialHitTime γ z r) with ho | ho
  · exact (h.slab_pair_ordered hU hκ hκ4 hε r z w hzy hwy hne ho).trans
      (mul_le_mul le_rfl (le_add_right le_rfl) bot_le bot_le)
  · have hb := h.slab_pair_ordered hU hκ hκ4 hε r w z hwy hzy hne.symm ho
    simp only [mul_comm (spatialSlabCoefficient κ U γ G r ε _ w)] at hb
    exact hb.trans (mul_le_mul le_rfl (le_add_left le_rfl) bot_le bot_le)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal ComplexConjugate
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma spatialHitTime_measurable_point (hc : Continuous γ) (r : ℝ) :
    Measurable (fun z => spatialHitTime γ z r) := by
  have hm := spatialHitTime_measurable (fun _ : Unit => γ) (fun _ => hc)
    (fun _ => measurable_const) r
  exact hm.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma IsCapacityTwoWitness.joint_live_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) :
    MeasurableSet {p : ℝ≥0 × ℂ | p.2 ∈ survivingDomain γ p.1} := by
  let c := spatialClippedFamily (fun t (_ : Unit) => U t)
    (hU.measurable.comp measurable_fst) (fun _ => hU)
  have hm := c.live_measurable (fun _ => γ) (fun _ => G) (fun _ => F) (fun _ => hU) (fun _ => h)
  exact hm.preimage (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const (a := ()))))

lemma IsCapacityTwoWitness.killed_chart_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) :
    Measurable (fun p : ℝ≥0 × ℂ => if p.2 ∈ survivingDomain γ p.1 then G p.1 p.2 else 0) := by
  let c := spatialClippedFamily (fun t (_ : Unit) => U t)
    (hU.measurable.comp measurable_fst) (fun _ => hU)
  convert c.jointChart_measurable.comp
    (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const (a := ())))) using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact (c.jointChart_eq () hU h p.1 p.2).symm

lemma IsCapacityTwoWitness.spatial_later_kernel_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (r : ℝ) :
    Measurable (fun p : ℂ × ℂ => spatialLaterKernel γ G r p.1 p.2) := by
  classical
  let H (p : ℝ≥0 × ℂ) := if p.2 ∈ survivingDomain γ p.1 then G p.1 p.2 else 0
  let s (z : ℂ) := (spatialHitTime γ z r).untopD 0
  have hm := spatialHitTime_measurable_point h.1 r
  have hs : Measurable s := hm.untopD 0
  have hH : Measurable H := h.killed_chart_measurable hU
  have hz : Measurable (fun p : ℂ × ℂ => H (s p.1, p.1)) := hH.comp ((hs.comp measurable_fst).prodMk measurable_fst)
  have hw : Measurable (fun p : ℂ × ℂ => H (s p.1, p.2)) := hH.comp ((hs.comp measurable_fst).prodMk measurable_snd)
  have hK : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (halfPlaneGreen (H (s p.1, p.1)) (H (s p.1, p.2)))) := by
    exact (Real.measurable_log.comp ((hz.sub (Complex.continuous_conj.measurable.comp hw)).div (hz.sub hw)).norm).ennreal_ofReal
  have hzl : MeasurableSet {p : ℂ × ℂ | p.1 ∈ survivingDomain γ (s p.1)} :=
    (h.joint_live_measurable hU).preimage ((hs.comp measurable_fst).prodMk measurable_fst)
  have hwl : MeasurableSet {p : ℂ × ℂ | p.2 ∈ survivingDomain γ (s p.1)} :=
    (h.joint_live_measurable hU).preimage ((hs.comp measurable_fst).prodMk measurable_snd)
  have ho : MeasurableSet {p : ℂ × ℂ | spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0)} :=
    measurableSet_le (hm.comp measurable_snd) ((hs.comp measurable_fst).withTop_coe)
  have hnf : MeasurableSet {p : ℂ × ℂ | spatialHitTime γ p.1 r = ⊤} :=
    measurableSet_eq_fun (hm.comp measurable_fst) measurable_const
  have hk : Measurable (fun p : ℂ × ℂ =>
      if p.1 ∈ survivingDomain γ (s p.1) ∧ p.2 ∈ survivingDomain γ (s p.1) ∧
        spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0) then
        ENNReal.ofReal (halfPlaneGreen (H (s p.1, p.1)) (H (s p.1, p.2))) else 0) := by
    exact @Measurable.ite _ _ _ _ _ _
      (fun p : ℂ × ℂ => p.1 ∈ survivingDomain γ (s p.1) ∧ p.2 ∈ survivingDomain γ (s p.1) ∧
        spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0)) (fun _ => inferInstance)
      (hzl.inter (hwl.inter ho)) hK (measurable_const (a := (0 : ℝ≥0∞)))
  have hh : Measurable (fun p : ℂ × ℂ => if spatialHitTime γ p.1 r = ⊤ then 0 else
      if p.1 ∈ survivingDomain γ (s p.1) ∧ p.2 ∈ survivingDomain γ (s p.1) ∧
        spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0) then
        ENNReal.ofReal (halfPlaneGreen (H (s p.1, p.1)) (H (s p.1, p.2))) else 0) := by
    exact @Measurable.ite _ _ _ _ _ _ (fun p : ℂ × ℂ => spatialHitTime γ p.1 r = ⊤)
      (fun _ => inferInstance) hnf
      (measurable_const (a := (0 : ℝ≥0∞))) hk
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  dsimp only [spatialLaterKernel]
  by_cases hn : spatialHitTime γ p.1 r = ⊤
  · simp only [hn, ite_eq_left]
  · rw [ite_eq_right hn, ite_eq_right hn]
    change (if p.1 ∈ survivingDomain γ (s p.1) ∧ p.2 ∈ survivingDomain γ (s p.1) ∧
        spatialHitTime γ p.2 r ≤ (s p.1 : WithTop ℝ≥0) then _ else _) = _
    split_ifs with hl
    · simp only [H, ite_eq_left hl.1, ite_eq_left hl.2.1]
      rfl
    · rfl

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.spatial_later_kernel_double
    (h : IsCapacityTwoWitness U γ G F) {r : ℝ} (hr : 0 < r) (A : Set ℂ) :
    (∫⁻ z in A, ∫⁻ w in A, spatialLaterKernel γ G r z w) ≤
      ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A := by
  calc
    _ ≤ ∫⁻ _z in A, ENNReal.ofReal (layerGreenConstant * r ^ 2) := by
      apply lintegral_mono
      intro z
      exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans (h.spatial_later_kernel_integral hr z)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

lemma sym_pair_lintegral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SFinite μ] (K : α → α → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (C : ℝ≥0∞) (hC : C ≠ ∞) :
    (∫⁻ z, ∫⁻ w, C * (K z w + K w z) ∂μ ∂μ) =
      C * (2 * (∫⁻ z, ∫⁻ w, K z w ∂μ ∂μ)) := by
  have hi (z : α) : (∫⁻ w, C * (K z w + K w z) ∂μ) =
      C * ((∫⁻ w, K z w ∂μ) + (∫⁻ w, K w z ∂μ)) := by
    rw [lintegral_const_mul' C _ hC]
    have hm : Measurable (fun w => K z w) := hK.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_add_left hm]
  rw [lintegral_congr hi, lintegral_const_mul' C _ hC]
  have ho : Measurable (fun z => ∫⁻ w, K z w ∂μ) := hK.lintegral_prod_right'
  rw [lintegral_add_left ho]
  have hs : (∫⁻ z, ∫⁻ w, K w z ∂μ ∂μ) = (∫⁻ z, ∫⁻ w, K z w ∂μ ∂μ) :=
    lintegral_lintegral_swap (hK.comp measurable_swap).aemeasurable
  rw [hs, two_mul]

lemma IsCapacityTwoWitness.spatial_pair_lintegral_le
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε) (r : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, ε ≤ z.im) :
    (∫⁻ z in A, ∫⁻ w in A, ∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
        spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
    (∫⁻ z in A, ∫⁻ w in A,
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (spatialLaterKernel γ G r z w + spatialLaterKernel γ G r w z)) := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hA] with z hz
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae ((volume : Measure ℂ).ae_ne z)] with w hw hne
  exact h.slab_pair_kernel_bound hU hκ hκ4 hε r z w (hheight z hz) (hheight w hw) hne.symm

 

theorem IsCapacityTwoWitness.spatial_slab_pair_area_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, ε ≤ z.im) :
    (∫⁻ z in A, ∫⁻ w in A, ∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
        spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A)) := by
  refine (h.spatial_pair_lintegral_le hU hκ hκ4 hε r A hA hheight).trans ?_
  rw [sym_pair_lintegral (volume.restrict A) (spatialLaterKernel γ G r) (h.spatial_later_kernel_measurable hU r)
    _ ENNReal.ofReal_ne_top]
  exact mul_le_mul le_rfl
    (mul_le_mul le_rfl (h.spatial_later_kernel_double hr A) bot_le bot_le) bot_le bot_le

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal ComplexConjugate
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.killed_green_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) {κ : ℝ} (hκ : 0 < κ) :
    Measurable (fun p : ℝ≥0 × ℂ => greenDensity κ U γ G p.1 p.2) := by
  let c := spatialClippedFamily (fun t (_ : Unit) => U t)
    (hU.measurable.comp measurable_fst) (fun _ => hU)
  let B (t : ℝ≥0) (_ : Unit) := U t / Real.sqrt κ
  have hBm : Measurable (fun p : ℝ≥0 × Unit => B p.1 p.2) :=
    (hU.measurable.comp measurable_fst).div_const _
  have hm := (c.jointGreen_measurable κ B hBm).comp
    (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const (a := ()))))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  apply (c.jointGreen_eq κ B () hU _ h p.1 p.2).symm
  intro t
  dsimp only [B]
  field_simp [(Real.sqrt_pos.mpr hκ).ne']

lemma IsCapacityTwoWitness.green_coefficient_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) {κ : ℝ} (hκ : 0 < κ) :
    Measurable (fun p : ℝ≥0 × ℂ => greenBrownianCoefficient κ U γ G p.1 p.2) := by
  classical
  let H (p : ℝ≥0 × ℂ) := if p.2 ∈ survivingDomain γ p.1 then G p.1 p.2 else 0
  have hZ : Measurable (fun p : ℝ≥0 × ℂ => H p - (U p.1 : ℂ)) :=
    (h.killed_chart_measurable hU).sub (Complex.measurable_ofReal.comp (hU.measurable.comp measurable_fst))
  have hb := (((Complex.measurable_re.comp hZ).const_mul (Real.sqrt κ * greenExponent κ)).div
    (hZ.norm.pow_const 2)).mul (h.killed_green_measurable hU hκ)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  by_cases hl : p.2 ∈ survivingDomain γ p.1
  · simp only [Pi.mul_apply, Pi.div_apply, Function.comp_apply, H, ite_eq_left hl, greenBrownianCoefficient]
  · simp only [Pi.mul_apply, Pi.div_apply, Function.comp_apply, greenBrownianCoefficient, greenDensity, ite_eq_right hl, mul_zero]

lemma IsCapacityTwoWitness.spatial_slab_coefficient_measurable
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U) {κ : ℝ} (hκ : 0 < κ)
    (r ε : ℝ) :
    Measurable (fun p : ℝ≥0 × ℂ => spatialSlabCoefficient κ U γ G r ε p.1 p.2) := by
  classical
  have ht : Measurable (fun p : ℝ≥0 × ℂ => (p.1 : WithTop ℝ≥0)) := measurable_fst.withTop_coe
  have hr : Measurable (fun p : ℝ≥0 × ℂ => spatialHitTime γ p.2 r) :=
    (spatialHitTime_measurable_point h.1 r).comp measurable_snd
  have he : Measurable (fun p : ℝ≥0 × ℂ => spatialHitTime γ p.2 ε) :=
    (spatialHitTime_measurable_point h.1 ε).comp measurable_snd
  have hm : MeasurableSet {p : ℝ≥0 × ℂ | spatialHitTime γ p.2 r ≤ p.1 ∧
      (p.1 : WithTop ℝ≥0) ≤ spatialHitTime γ p.2 ε ∧ p.2 ∈ survivingDomain γ p.1} :=
    (measurableSet_le hr ht).inter ((measurableSet_le ht he).inter (h.joint_live_measurable hU))
  exact @Measurable.ite _ _ _ _ _ _ (fun p : ℝ≥0 × ℂ => spatialHitTime γ p.2 r ≤ p.1 ∧
      (p.1 : WithTop ℝ≥0) ≤ spatialHitTime γ p.2 ε ∧ p.2 ∈ survivingDomain γ p.1)
    (fun _ => inferInstance) hm
    (h.green_coefficient_measurable hU hκ) measurable_const

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped ENNReal NNReal

namespace SLEExactGauge

 

lemma area_square_tonelli {T Z : Type*} [MeasurableSpace T] [MeasurableSpace Z]
    {μ : Measure T} {ν : Measure Z} [SFinite μ] [SFinite ν]
    {f : T × Z → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t, (∫⁻ z, f (t, z) ∂ν) ^ 2 ∂μ) =
      ∫⁻ z, ∫⁻ w, ∫⁻ t, f (t, z) * f (t, w) ∂μ ∂ν ∂ν := by
  have hft (t : T) : Measurable (fun z => f (t, z)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  have h3 : Measurable (fun p : (T × Z) × Z => f (p.1.1, p.1.2) * f (p.1.1, p.2)) :=
    (hf.comp measurable_fst).mul
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hinner : Measurable (fun p : T × Z => ∫⁻ w, f (p.1, p.2) * f (p.1, w) ∂ν) :=
    h3.lintegral_prod_right'
  calc
    _ = ∫⁻ t, ∫⁻ z, ∫⁻ w, f (t, z) * f (t, w) ∂ν ∂ν ∂μ := by
      apply lintegral_congr
      intro t
      simp_rw [lintegral_const_mul _ (hft t)]
      rw [lintegral_mul_const _ (hft t), pow_two]
    _ = ∫⁻ z, ∫⁻ t, ∫⁻ w, f (t, z) * f (t, w) ∂ν ∂μ ∂ν :=
      lintegral_lintegral_swap hinner.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      apply lintegral_lintegral_swap
      exact ((hf.comp (measurable_fst.prodMk measurable_const)).mul hf).aemeasurable

lemma spatial_integral_square_le {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    (f : Z → ℝ) :
    ENNReal.ofReal ((∫ z, f z ∂ν) ^ 2) ≤ (∫⁻ z, ENNReal.ofReal |f z| ∂ν) ^ 2 := by
  have he (x : ℝ) : ‖x‖ₑ = ENNReal.ofReal |x| := by
    rw [← ofReal_norm, Real.norm_eq_abs]
  have hb := pow_le_pow_left₀ bot_le (enorm_integral_le_lintegral_enorm (μ := ν) f) 2
  rw [← enorm_pow, Real.enorm_eq_ofReal (sq_nonneg _)] at hb
  simpa only [he] using hb

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

 

theorem IsCapacityTwoWitness.spatial_slab_absolute_bracket_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, ε ≤ z.im) :
    (∫⁻ t in Ici (0 : ℝ), (∫⁻ z in A,
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z|) ^ 2) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A)) := by
  have hb : Measurable (fun p : ℝ × ℂ => spatialSlabCoefficient κ U γ G r ε p.1.toNNReal p.2) := by
    have hm : Measurable (fun p : ℝ × ℂ => (p.1.toNNReal, p.2)) :=
      (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
    exact (h.spatial_slab_coefficient_measurable hU hκ r ε).comp
      (f := fun p : ℝ × ℂ => (p.1.toNNReal, p.2)) hm
  rw [area_square_tonelli hb.abs.ennreal_ofReal]
  have he (t : ℝ) (z w : ℂ) :
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z| *
        ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal w| =
      ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
        spatialSlabCoefficient κ U γ G r ε t.toNNReal w| := by
    rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  simp_rw [he]
  exact h.spatial_slab_pair_area_bound hU hκ hκ4 hε hr A hA hheight



end SLEExactGauge

 

 

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.BrownianPredictable

 

lemma gaussian_fourth_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  let f : ℝ → ℝ := fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)
  have hf (t : ℝ) : HasDerivAt f ((v : ℝ) * t * f t) t := by
    apply (((hasDerivAt_id t).pow 2 |>.const_mul (v : ℝ)).div_const 2).exp.congr_deriv
    dsimp [f]
    ring
  have hd : deriv f = fun t => (v : ℝ) * t * f t := funext fun t => (hf t).deriv
  have hd1 : deriv (fun t => (v : ℝ) * t * f t) =
      fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t := by
    funext t
    apply HasDerivAt.deriv
    apply (((hasDerivAt_id t).const_mul (v : ℝ)).mul (hf t)).congr_deriv
    simp only [id_eq]
    ring
  have hd2 : deriv (fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t) =
      fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t := by
    funext t
    apply HasDerivAt.deriv
    apply (((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ) ^ 2)).const_add
      (v : ℝ)).mul (hf t)).congr_deriv
    simp only [id_eq, Pi.pow_apply]
    ring
  have hd3 : deriv (fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t) =
      fun t => (3 * (v : ℝ) ^ 2 + 6 * (v : ℝ) ^ 3 * t ^ 2 +
        (v : ℝ) ^ 4 * t ^ 4) * f t := by
    funext t
    apply HasDerivAt.deriv
    apply ((((hasDerivAt_id t).const_mul (3 * (v : ℝ) ^ 2)).add
      (((hasDerivAt_id t).pow 3).const_mul ((v : ℝ) ^ 3))).mul (hf t)).congr_deriv
    simp only [id_eq, Pi.pow_apply, Pi.add_apply]
    ring
  change (∫ x, ((fun x : ℝ => x) ^ 4) x ∂gaussianReal 0 v) = _
  rw [← iteratedDeriv_mgf_zero (by simp), mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  change iteratedDeriv 4 f 0 = _
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, hd, hd1, hd2, hd3]
  simp [f]

lemma gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have hv := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
  simpa [integral_id_gaussianReal] using hv.symm

lemma gaussian_square_memLp (v : ℝ≥0) :
    MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  have h4 := (memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_pow
    (p := 4) (by norm_num)
  convert h4 using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [id_eq, Real.norm_eq_abs]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]

lemma gaussian_square_variance (v : ℝ≥0) :
    variance (fun x : ℝ => x ^ 2) (gaussianReal 0 v) = 2 * (v : ℝ) ^ 2 := by
  rw [variance_eq_sub (gaussian_square_memLp v), gaussian_second_moment]
  have heq : (fun x : ℝ => ((fun x : ℝ => x ^ 2) ^ 2) x) = fun x : ℝ => x ^ 4 := by
    funext x
    simp only [Pi.pow_apply]
    ring
  rw [show (fun x : ℝ => x ^ 2) ^ 2 = (fun x : ℝ => x ^ 4) from heq,
    gaussian_fourth_moment]
  ring

lemma increment_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t-s)) P := by
  simpa only [add_tsub_cancel_of_le hst] using
    (hB.toIsPreBrownianReal.shift s).hasLaw_eval (t-s)

lemma brownian_indep_of_past_measurable {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (s v : ℝ≥0)
    {X : Ω → α} (hX : Measurable[pastSigma B s] X) :
    IndepFun X (fun ω => B (s+v) ω - B s ω) P := by
  have hh := (hB.toIsPreBrownianReal.indepFun_shift s).symm.comp
    measurable_id (measurable_pi_apply v)
  change Indep (MeasurableSpace.comap X inferInstance)
    (MeasurableSpace.comap (fun ω => B (s+v) ω - B s ω) inferInstance) P
  exact indep_of_indep_of_le_left hh hX.comap_le

lemma pastSigma_mono {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) : pastSigma B s ≤ pastSigma B t := by
  let : MeasurableSpace Ω := pastSigma B t
  have hm : Measurable (fun ω (u : Set.Iic s) => B u ω) := by
    apply Measurable.of_eval
    intro u
    exact (measurable_pi_apply (⟨u, u.2.trans hst⟩ : Set.Iic t)).comp
      (comap_measurable (fun ω (v : Set.Iic t) => B v ω))
  exact hm.comap_le

lemma past_measurable_eval {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) : Measurable[pastSigma B t] (B s) :=
  (measurable_pi_apply (⟨s, hst⟩ : Set.Iic t)).comp
    (comap_measurable (fun ω (v : Set.Iic t) => B v ω))

lemma past_mul_feature_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) {X : Ω → ℝ}
    (hX : Measurable[pastSigma B s] X) (hXa : AEMeasurable X P)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ ω, X ω * φ (B t ω - B s ω) ∂P) =
      (∫ ω, X ω ∂P) * (∫ x, φ x ∂gaussianReal 0 (t-s)) := by
  have hi := (brownian_indep_of_past_measurable hB s (t-s) hX).comp
    measurable_id hφ
  rw [add_tsub_cancel_of_le hst] at hi
  have hl := increment_hasLaw hB hst
  change IndepFun X (fun ω => φ (B t ω - B s ω)) P at hi
  rw [hi.integral_fun_mul_eq_mul_integral hXa.aestronglyMeasurable
      (hφ.comp_aemeasurable hl.aemeasurable).aestronglyMeasurable]
  rw [show (∫ ω, φ (B t ω - B s ω) ∂P) = ∫ x, φ x ∂gaussianReal 0 (t-s) from
    hl.integral_comp hφ.aestronglyMeasurable]

lemma independent_product_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hXY : IndepFun X Y P) : MemLp (fun ω => X ω * Y ω) 2 P := by
  apply (memLp_two_iff_integrable_sq (hX.aestronglyMeasurable.mul hY.aestronglyMeasurable)).2
  have hi := (hXY.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integrable_mul
    hX.integrable_sq hY.integrable_sq
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext ω
  simp only [Function.comp_apply, Pi.mul_apply, mul_pow, id_eq]


lemma predictableTerm_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφ2 : ∀ i, MemLp (φ i) 2 (gaussianReal 0 (t (i+1)-t i))) (i : ℕ) :
    MemLp (fun ω => C i ω * φ i (B (t (i+1)) ω - B (t i) ω)) 2 P := by
  have ht' := ht (Nat.le_succ i)
  have hl := increment_hasLaw hB ht'
  have hY := (hl.map_eq ▸ hφ2 i).comp_of_map hl.aemeasurable
  have hi := (brownian_indep_of_past_measurable hB (t i) (t (i+1)-t i) (hC i)).comp
    measurable_id (hφ i)
  rw [add_tsub_cancel_of_le ht'] at hi
  exact independent_product_memLp_two (hC2 i) hY hi

lemma predictableTerm_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hCa : ∀ i, AEMeasurable (C i) P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφ0 : ∀ i, (∫ x, φ i x ∂gaussianReal 0 (t (i+1)-t i)) = 0) (i : ℕ) :
    (∫ ω, C i ω * φ i (B (t (i+1)) ω - B (t i) ω) ∂P) = 0 := by
  rw [past_mul_feature_integral hB (ht (Nat.le_succ i)) (hC i) (hCa i) (φ i) (hφ i),
    hφ0, mul_zero]

lemma predictableTerm_past_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i))
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i)) {i j : ℕ} (hij : i+1 ≤ j) :
    Measurable[pastSigma B (t j)]
      (fun ω => C i ω * φ i (B (t (i+1)) ω - B (t i) ω)) := by
  have hi : t i ≤ t j := ht (le_trans (Nat.le_succ i) hij)
  exact ((hC i).mono (pastSigma_mono B hi) le_rfl).mul
    ((hφ i).comp ((past_measurable_eval B (ht hij)).sub
      (past_measurable_eval B hi)))

lemma predictableTerm_covariance_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφ2 : ∀ i, MemLp (φ i) 2 (gaussianReal 0 (t (i+1)-t i)))
    (hφ0 : ∀ i, (∫ x, φ i x ∂gaussianReal 0 (t (i+1)-t i)) = 0)
    {i j : ℕ} (hij : i ≠ j) :
    covariance (fun ω => C i ω * φ i (B (t (i+1)) ω - B (t i) ω))
      (fun ω => C j ω * φ j (B (t (j+1)) ω - B (t j) ω)) P = 0 := by
  wlog hlt : i < j generalizing i j
  · rw [covariance_comm]
    exact this hij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  have hAi := predictableTerm_memLp_two hB t ht C hC hC2 φ hφ hφ2 i
  have hAj := predictableTerm_memLp_two hB t ht C hC hC2 φ hφ hφ2 j
  rw [covariance_eq_sub hAi hAj,
    predictableTerm_integral hB t ht C hC (fun i => (hC2 i).aemeasurable) φ hφ hφ0 i,
    zero_mul, sub_zero]
  have hp := (predictableTerm_past_measurable B t ht C hC φ hφ hlt).mul (hC j)
  have hh := past_mul_feature_integral hB (ht (Nat.le_succ j)) hp
    (hAi.aemeasurable.mul (hC2 j).aemeasurable) (φ j) (hφ j)
  rw [hφ0, mul_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext ω
  simp only [Pi.mul_apply]
  ring

end SLEExactGauge.BrownianPredictable
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_IntegralLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral Limits for chordal SLE. -/

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
namespace SLEExactGauge.BrownianPredictable
lemma predictableTerm_square_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hCa : ∀ i, AEMeasurable (C i) P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i)) (i : ℕ) :
    (∫ ω, (C i ω * φ i (B (t (i+1)) ω - B (t i) ω)) ^ 2 ∂P) =
      (∫ ω, C i ω ^ 2 ∂P) * (∫ x, φ i x ^ 2 ∂gaussianReal 0 (t (i+1)-t i)) := by
  simpa only [mul_pow] using past_mul_feature_integral hB (ht (Nat.le_succ i))
    ((hC i).pow_const 2) ((hCa i).pow_const 2) (fun x => φ i x ^ 2) ((hφ i).pow_const 2)

 

theorem predictableFeatureSum_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (φ : ℕ → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφ2 : ∀ i, MemLp (φ i) 2 (gaussianReal 0 (t (i+1)-t i)))
    (hφ0 : ∀ i, (∫ x, φ i x ∂gaussianReal 0 (t (i+1)-t i)) = 0) (n : ℕ) :
    (∫ ω, predictableFeatureSum B t C φ n ω ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, (∫ ω, C i ω ^ 2 ∂P) *
        (∫ x, φ i x ^ 2 ∂gaussianReal 0 (t (i+1)-t i)) := by
  let Y : ℕ → Ω → ℝ := fun i ω => C i ω * φ i (B (t (i+1)) ω - B (t i) ω)
  have hY (i : ℕ) : MemLp (Y i) 2 P :=
    predictableTerm_memLp_two hB t ht C hC hC2 φ hφ hφ2 i
  have hY0 (i : ℕ) : (∫ ω, Y i ω ∂P) = 0 :=
    predictableTerm_integral hB t ht C hC (fun i => (hC2 i).aemeasurable) φ hφ hφ0 i
  have hsum : MemLp (predictableFeatureSum B t C φ n) 2 P :=
    memLp_finsetSum _ (fun i _ => hY i)
  have hsum0 : (∫ ω, predictableFeatureSum B t C φ n ω ∂P) = 0 := by
    unfold predictableFeatureSum
    rw [integral_finsetSum _ (fun i _ => (hY i).integrable (by norm_num))]
    exact Finset.sum_eq_zero (fun i _ => hY0 i)
  have hv : (∫ ω, predictableFeatureSum B t C φ n ω ^ 2 ∂P) =
      variance (predictableFeatureSum B t C φ n) P := by
    rw [variance_eq_sub hsum, hsum0]
    simp
  rw [hv]
  change variance (fun ω => ∑ i ∈ Finset.range n, Y i ω) P = _
  rw [variance_fun_sum' (fun i _ => hY i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single_of_mem i hi (fun j _ hji => ?_)]
  · rw [covariance_self (hY i).aemeasurable, variance_eq_sub (hY i), hY0]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
    exact predictableTerm_square_integral hB t ht C hC
      (fun i => (hC2 i).aemeasurable) φ hφ i
  · exact predictableTerm_covariance_zero hB t ht C hC hC2 φ hφ hφ2 hφ0 hji.symm

lemma centeredSquare_gaussian_memLp (v : ℝ≥0) :
    MemLp (fun x : ℝ => x^2 - (v : ℝ)) 2 (gaussianReal 0 v) :=
  (gaussian_square_memLp v).sub (memLp_const _)

lemma centeredSquare_gaussian_mean (v : ℝ≥0) :
    (∫ x : ℝ, x^2 - (v : ℝ) ∂gaussianReal 0 v) = 0 := by
  rw [integral_sub ((gaussian_square_memLp v).integrable (by norm_num)) (integrable_const _),
    gaussian_second_moment]
  simp

lemma centeredSquare_gaussian_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, (x^2 - (v : ℝ))^2 ∂gaussianReal 0 v) = 2 * (v : ℝ)^2 := by
  have hv := variance_eq_integral (gaussian_square_memLp v).aemeasurable
  rw [gaussian_second_moment, gaussian_square_variance] at hv
  exact hv.symm

 
theorem brownian_predictableSum_isometry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, C i ω * (B (t (i+1)) ω - B (t i) ω))^2 ∂P) =
      ∑ i ∈ Finset.range n, (∫ ω, C i ω ^ 2 ∂P) * ((t (i+1) : ℝ) - t i) := by
  have hi := predictableFeatureSum_second_moment hB t ht C hC hC2
    (fun _ x => x) (fun _ => measurable_id)
    (fun _ => memLp_id_gaussianReal' 2 (by norm_num))
    (fun _ => by simp) n
  simpa only [predictableFeatureSum, gaussian_second_moment,
    NNReal.coe_sub (ht (Nat.le_succ _))] using hi

 

theorem brownian_predictableQuadraticError_isometry {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[pastSigma B (t i)] (C i)) (hC2 : ∀ i, MemLp (C i) 2 P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, C i ω *
      ((B (t (i+1)) ω - B (t i) ω)^2 - ((t (i+1) : ℝ) - t i)))^2 ∂P) =
      ∑ i ∈ Finset.range n, (∫ ω, C i ω ^ 2 ∂P) *
        (2 * ((t (i+1) : ℝ) - t i)^2) := by
  have hi := predictableFeatureSum_second_moment hB t ht C hC hC2
    (fun i x => x^2 - (t (i+1)-t i : ℝ≥0)) (fun _ => by fun_prop)
    (fun _ => centeredSquare_gaussian_memLp _)
    (fun _ => centeredSquare_gaussian_mean _) n
  simp only [predictableFeatureSum] at hi
  simp_rw [centeredSquare_gaussian_second_moment] at hi
  simpa only [NNReal.coe_sub (ht (Nat.le_succ _))] using hi


lemma dyadicTime_mono (T : ℝ≥0) (n : ℕ) : Monotone (dyadicTime T n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)

lemma dyadicTime_step (T : ℝ≥0) (n i : ℕ) :
    (dyadicTime T n (i+1) : ℝ) - dyadicTime T n i = (T : ℝ) / (2 : ℝ)^n := by
  simp only [dyadicTime]
  push_cast
  ring



lemma dyadicQuadraticError_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (n : ℕ) :
    MemLp (dyadicQuadraticError B T C n) 2 P := by
  apply memLp_finsetSum
  intro i hi
  have hh := predictableTerm_memLp_two hB (dyadicTime T n) (dyadicTime_mono T n)
    (C n) (hC n) (hC2 n)
    (fun i x => x^2 - (dyadicTime T n (i+1) - dyadicTime T n i : ℝ≥0))
    (fun _ => by fun_prop) (fun _ => centeredSquare_gaussian_memLp _) i
  simpa only [NNReal.coe_sub (dyadicTime_mono T n (Nat.le_succ _)),
    dyadicTime_step] using hh

lemma dyadicQuadraticError_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (n : ℕ) :
    (∫ ω, dyadicQuadraticError B T C n ω ∂P) = 0 := by
  have hterm (i : ℕ) := predictableTerm_memLp_two hB (dyadicTime T n)
    (dyadicTime_mono T n) (C n) (hC n) (hC2 n)
    (fun i x => x^2 - (dyadicTime T n (i+1) - dyadicTime T n i : ℝ≥0))
    (fun _ => by fun_prop) (fun _ => centeredSquare_gaussian_memLp _) i
  simp only [NNReal.coe_sub (dyadicTime_mono T n (Nat.le_succ _)),
    dyadicTime_step] at hterm
  unfold dyadicQuadraticError
  rw [integral_finsetSum _ (fun i _ => (hterm i).integrable (by norm_num))]
  apply Finset.sum_eq_zero
  intro i hi
  have hh := predictableTerm_integral hB (dyadicTime T n) (dyadicTime_mono T n)
    (C n) (hC n) (fun i => (hC2 n i).aemeasurable)
    (fun i x => x^2 - (dyadicTime T n (i+1) - dyadicTime T n i : ℝ≥0))
    (fun _ => by fun_prop) (fun _ => centeredSquare_gaussian_mean _) i
  simpa only [NNReal.coe_sub (dyadicTime_mono T n (Nat.le_succ _)),
    dyadicTime_step] using hh

lemma dyadicQuadraticError_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (K : ℝ) (hK : 0 ≤ K)
    (hCK : ∀ n i, ∀ᵐ ω ∂P, |C n i ω| ≤ K) (n : ℕ) :
    (∫ ω, dyadicQuadraticError B T C n ω ^ 2 ∂P) ≤
      2 * K^2 * (T : ℝ)^2 * (1/2 : ℝ)^n := by
  have hi := brownian_predictableQuadraticError_isometry hB (dyadicTime T n)
    (dyadicTime_mono T n) (C n) (hC n) (hC2 n) (2^n)
  simp only [dyadicTime_step] at hi
  change (∫ ω, dyadicQuadraticError B T C n ω ^ 2 ∂P) = _ at hi
  rw [hi]
  calc
    _ ≤ ∑ i ∈ Finset.range (2^n), K^2 * (2 * ((T : ℝ) / (2 : ℝ)^n)^2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        (∫ ω, C n i ω ^ 2 ∂P) ≤ ∫ _ : Ω, K^2 ∂P := by
          apply integral_mono_ae (hC2 n i).integrable_sq (integrable_const _)
          filter_upwards [hCK n i] with ω hω
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 hω
        _ = K^2 := by simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      rw [one_div_pow]
      field_simp

 

theorem brownian_dyadic_weighted_quadraticError_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (K : ℝ) (hK : 0 ≤ K)
    (hCK : ∀ n i, ∀ᵐ ω ∂P, |C n i ω| ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun n => dyadicQuadraticError B T C n ω) atTop (𝓝 0) := by
  have hv (n : ℕ) : variance (dyadicQuadraticError B T C n) P ≤
      2 * K^2 * (T : ℝ)^2 * (1/2 : ℝ)^n := by
    rw [variance_eq_sub (dyadicQuadraticError_memLp hB T C hC hC2 n),
      dyadicQuadraticError_integral hB T C hC hC2 n]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero]
    exact dyadicQuadraticError_second_moment_le hB T C hC hC2 K hK hCK n
  have htail (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
      P {ω | ε ≤ |dyadicQuadraticError B T C n ω|} ≤
        ENNReal.ofReal ((2 * K^2 * (T : ℝ)^2 / ε^2) * (1/2 : ℝ)^n) := by
    have hh := meas_ge_le_variance_div_sq (dyadicQuadraticError_memLp hB T C hC hC2 n) hε
    rw [dyadicQuadraticError_integral hB T C hC hC2 n] at hh
    simp only [sub_zero] at hh
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (2 * K^2 * (T : ℝ)^2 * (1/2 : ℝ)^n) / ε^2 := by gcongr; exact hv n
      _ = _ := by ring
  have hevent (k : ℕ) : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      |dyadicQuadraticError B T C n ω| < 1 / ((k : ℝ) + 1) := by
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hs : (∑' n, P {ω | ε ≤ |dyadicQuadraticError B T C n ω|}) ≠ ∞ := by
      exact ne_top_of_le_ne_top
        ((summable_geometric_two.mul_left (2 * K^2 * (T : ℝ)^2 / ε^2)).tsum_ofReal_ne_top)
        (ENNReal.tsum_le_tsum (htail ε hε))
    simpa only [Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hs
  filter_upwards [ae_all_iff.2 hevent] with ω hω
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω k)
  exact ⟨N, fun n hn => by simpa only [Real.dist_eq, sub_zero] using (hN n hn).trans hk⟩

end SLEExactGauge.BrownianPredictable

 

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.L2Limit

lemma eLpNorm_two_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 P) :
    eLpNorm X 2 P = (ENNReal.ofReal (∫ ω, X ω ^ 2 ∂P)) ^ (1/2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  have heq (ω : Ω) : ‖X ω‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (X ω ^ 2) := by
    rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hX.integrable_sq
    (Eventually.of_forall fun ω => sq_nonneg _)]

end SLEExactGauge.L2Limit

namespace SLEExactGauge.PredictableLimit
open BrownianPredictable L2Limit

lemma dyadicDriverSum_memLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (T : ℝ≥0) (C : ℕ → ℕ → Ω → ℝ)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P) (n : ℕ) :
    MemLp (dyadicDriverSum B T C n) 2 P := by
  apply memLp_finsetSum
  intro i hi
  exact predictableTerm_memLp_two hB (dyadicTime T n) (dyadicTime_mono T n)
    (C n) (hC n) (hC2 n) (fun _ x => x) (fun _ => measurable_id)
    (fun _ => memLp_id_gaussianReal' 2 (by norm_num)) i

end SLEExactGauge.PredictableLimit

 

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.TaylorMeshes


lemma quadratic_taylor_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (x y K : ℝ) (_hK : 0 ≤ K)
    (h3 : ∀ z ∈ uIcc x y, |iteratedDeriv 3 f z| ≤ K) :
    |remainder₂ f x y| ≤ K * |y-x|^3 / 6 := by
  by_cases hxy : x = y
  · subst y
    simp [remainder₂]
  have ht (k : ℕ) (hk : k ≤ 2) :
      iteratedDerivWithin k f (uIcc x y) x = iteratedDeriv k f x := by
    apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
    · exact (hf.of_le (by exact_mod_cast (le_trans hk (by decide : 2 ≤ 3)))).contDiffAt
    · exact left_mem_uIcc
  have hpoly : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y-x) + deriv (deriv f) x / 2 * (y-x)^2 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, ht, iteratedDeriv_succ, iteratedDeriv_zero]
    ring
  obtain ⟨z, hz, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hxy hf.contDiffOn
  rw [hpoly] at heq
  have hr : remainder₂ f x y = iteratedDeriv 3 f z * (y-x)^3 / 6 := by
    dsimp [remainder₂]
    norm_num at heq
    linarith
  rw [hr, abs_div, abs_mul, abs_pow]
  norm_num
  gcongr
  exact h3 z (Ioo_subset_Icc_self hz)



lemma mesh_zero (T : ℝ) (n : ℕ) : mesh T n 0 = 0 := by simp [mesh]
lemma mesh_end (T : ℝ) (n : ℕ) : mesh T n (2^n) = T := by
  simp only [mesh, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
lemma mesh_step (T : ℝ) (n i : ℕ) : mesh T n (i+1) - mesh T n i = T / (2 : ℝ)^n := by
  simp only [mesh, Nat.cast_add, Nat.cast_one]
  ring
lemma mesh_mono (T : ℝ) (hT : 0 ≤ T) (n : ℕ) : Monotone (mesh T n) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
lemma mesh_mem (T : ℝ) (hT : 0 ≤ T) (n i : ℕ) (hi : i ≤ 2^n) : mesh T n i ∈ Icc 0 T := by
  constructor
  · exact (mesh_zero T n) ▸ mesh_mono T hT n (Nat.zero_le i)
  · exact (mesh_mono T hT n hi).trans_eq (mesh_end T n)

lemma mesh_step_tendsto (T : ℝ) :
    Tendsto (fun n : ℕ => T / (2 : ℝ)^n) atTop (𝓝 0) := by
  simpa only [mul_zero, div_eq_mul_inv, inv_pow] using
    (tendsto_const_nhds (x := T)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num))

 

lemma mesh_increments_small {b : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hb : ContinuousOn b (Icc 0 T)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ i < 2^n, |b (mesh T n (i+1)) - b (mesh T n i)| < δ := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hb
  obtain ⟨ε, hε, huε⟩ := Metric.uniformContinuousOn_iff.1 hu δ hδ
  have hn := (mesh_step_tendsto T).eventually (gt_mem_nhds hε)
  filter_upwards [hn] with n hn
  intro i hi
  apply huε (mesh T n (i+1)) (mesh_mem T hT n (i+1) hi)
    (mesh T n i) (mesh_mem T hT n i (Nat.le_of_lt hi))
  rw [Real.dist_eq, mesh_step, abs_of_nonneg (div_nonneg hT (by positivity))]
  exact hn



end SLEExactGauge.TaylorMeshes

namespace SLEExactGauge.TimeField
open TaylorMeshes

lemma sum_family_remainder₂_bound {f : ℕ → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ 3 (f i))
    (x : ℕ → ℝ) (n : ℕ) (K δ : ℝ) (hK : 0 ≤ K) (_hδ : 0 ≤ δ)
    (h3 : ∀ i < n, ∀ z ∈ uIcc (x i) (x (i+1)), |iteratedDeriv 3 (f i) z| ≤ K)
    (hstep : ∀ i < n, |x (i+1)-x i| ≤ δ) :
    |∑ i ∈ Finset.range n, remainder₂ (f i) (x i) (x (i+1))| ≤
      K * δ / 6 * ∑ i ∈ Finset.range n, (x (i+1)-x i)^2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |remainder₂ (f i) (x i) (x (i+1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, K * δ / 6 * (x (i+1)-x i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.1 hi
      calc
        _ ≤ K * |x (i+1)-x i|^3 / 6 := quadratic_taylor_bound (hf i) _ _ K hK (h3 i hi')
        _ = K / 6 * |x (i+1)-x i| * (x (i+1)-x i)^2 := by
          rw [show |x (i+1)-x i|^3 = |x (i+1)-x i| * |x (i+1)-x i|^2 by ring,
            sq_abs]
          ring
        _ ≤ K / 6 * δ * (x (i+1)-x i)^2 := by gcongr; exact hstep i hi'
        _ = _ := by ring
    _ = _ := (Finset.mul_sum _ _ _).symm

end SLEExactGauge.TimeField
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ItoIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ito Isometry for chordal SLE. -/

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

namespace SLEExactGauge.BrownianIto
open BrownianPredictable TaylorMeshes

lemma coe_dyadicTime (T : ℝ≥0) (n i : ℕ) :
    (dyadicTime T n i : ℝ) = mesh T n i := by
  simp only [dyadicTime, mesh]
  push_cast
  rfl

lemma mesh_toNNReal (T : ℝ≥0) (n i : ℕ) :
    (mesh T n i).toNNReal = dyadicTime T n i := by
  rw [← coe_dyadicTime]
  exact Real.toNNReal_coe


lemma error_one_eq {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) :
    dyadicQuadraticError B T (fun _ _ _ => 1) n ω = quadraticSum B T n ω - T := by
  simp only [dyadicQuadraticError, one_mul, Finset.sum_sub_distrib, quadraticSum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  congr 1
  field_simp

lemma quadraticSum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => quadraticSum B T n ω) atTop (𝓝 (T : ℝ)) := by
  have he := brownian_dyadic_weighted_quadraticError_tendsto hB T (fun _ _ _ => 1)
    (fun _ _ => measurable_const) (fun _ _ => memLp_const _) 1 (by norm_num)
    (fun _ _ => Eventually.of_forall fun _ => by norm_num)
  simp only [error_one_eq] at he
  filter_upwards [he] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add_const (T : ℝ)

end SLEExactGauge.BrownianIto



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

lemma ClippedLogSolution.velocity_continuous
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    Continuous (fun t : ℝ => c.velocity t ω) := by
  have hb : Continuous (fun t : ℝ => Real.sqrt κ * B t.toNNReal ω) :=
    ((hBc ω).comp continuous_real_toNNReal).const_mul _
  have hc : Continuous (fun t => (Real.sqrt κ * B t.toNNReal ω, c.Q t ω)) :=
    hb.prodMk (c.lipschitz ω).continuous
  exact (continuous_clippedLogLoewnerField lo hi hle).comp
    (f := fun t : ℝ => (Real.sqrt κ * B t.toNNReal ω, c.Q t ω)) hc

lemma ClippedLogSolution.compact_field_regular
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (φ : (ℂ × ℝ) × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (T : ℝ≥0) (ω : Ω) :
    FieldRegular (fun t x => φ (c.Q t ω, x))
      (fun t x => fderiv ℝ φ (c.Q t ω, x) (c.velocity t ω, 0))
      (fun t => B t.toNNReal ω) T := by
  have hQc := (c.lipschitz ω).continuous
  have hVc := c.velocity_continuous hBc ω
  have hBb := (hBc ω).comp continuous_real_toNNReal
  have hDp := hφ.continuous_fderiv (by simp)
  obtain ⟨K, hK, _⟩ := compact_smooth_bounded_lipschitz (spatialPartial φ 3)
    (spatialPartial_smooth φ hφ 3) (spatialPartial_compact φ hφc 3)
  refine ⟨?_, ⟨K, K.coe_nonneg, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (hφ.comp (contDiff_const.prodMk contDiff_id)).of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))
  · intro t x
    simpa only [← spatialPartial_eq_iteratedDeriv φ hφ, Real.norm_eq_abs] using hK (c.Q t ω, x)
  · intro x
    exact (hφ.continuous.comp (hQc.prodMk continuous_const)).continuousOn
  · intro t ht x
    have hd := (c.derivative ω t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
    exact ((hφ.differentiable (by simp)) (c.Q t ω, x)).hasFDerivAt.comp_hasDerivAt t
      (hd.prodMk (hasDerivAt_const t x))
  · exact ((hDp.comp ((hQc.comp continuous_fst).prodMk (hBb.comp continuous_snd))).clm_apply
      ((hVc.comp continuous_fst).prodMk continuous_const)).continuousOn
  · have hc := (spatialPartial_smooth φ hφ 2).continuous.comp (hQc.prodMk hBb)
    simpa only [Function.comp_def, spatialPartial_eq_iteratedDeriv φ hφ] using hc.continuousOn

lemma natural_eq_pastSigma (t : ℝ≥0) :
    Filtration.natural B (fun s => (hm s).stronglyMeasurable) t = pastSigma B t := by
  exact Filtration.natural_eq_comap B (fun s => (hm s).stronglyMeasurable) t

lemma mesh_eq_dyadicTime (T : ℝ≥0) (n i : ℕ) :
    mesh T n i = (dyadicTime T n i : ℝ) := by
  simp [mesh, dyadicTime]

lemma ClippedLogSolution.partial_adapted
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (φ : (ℂ × ℝ) × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (j : ℕ) (t : ℝ≥0) :
    Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) t]
      (fun ω => iteratedDeriv j (fun x => φ (c.Q t ω, x)) (B t ω)) := by
  simp_rw [← spatialPartial_eq_iteratedDeriv φ hφ]
  have hBa := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted
  exact (spatialPartial_smooth φ hφ j).continuous.measurable.comp
    ((c.adapted t).prodMk (hBa t))



end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes TimeField

lemma prefix_const_sum_le {T ζ : ℝ} (hT : 0 ≤ T) (hζ : 0 ≤ ζ)
    (k n : ℕ) (hk : k ≤ 2^n) :
    (∑ _i ∈ Finset.range k, ζ * (T / (2 : ℝ)^n)) ≤ ζ * T := by
  calc
    _ ≤ ∑ _i ∈ Finset.range (2^n), ζ * (T / (2 : ℝ)^n) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun _ _ _ => by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

lemma mesh_prefix_riemann_error {h : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hh : ContinuousOn h (Icc 0 T)) (k : ℕ → ℕ) (hk : ∀ n, k n ≤ 2^n) :
    Tendsto (fun n => (∑ i ∈ Finset.range (k n),
      h (mesh T n i) * (T / (2 : ℝ)^n)) - ∫ t in (0 : ℝ)..mesh T n (k n), h t) atTop (𝓝 0) := by
  have hint (n i : ℕ) (hi : i < 2^n) :
      IntervalIntegrable h volume (mesh T n i) (mesh T n (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (mesh_mono T hT n (Nat.le_succ i))]
    apply hh.mono
    exact Icc_subset_Icc (mesh_mem T hT n i hi.le).1
      (mesh_mem T hT n (i+1) hi).2
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hh
  apply Metric.tendsto_atTop.2
  intro ε hε
  let ζ : ℝ := ε / (T+1)
  have hζ : 0 < ζ := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 hu ζ hζ
  have hn := (mesh_step_tendsto T).eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hn
  refine ⟨N, fun n hn => ?_⟩
  have hnδ := hN n hn
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (fun i hi => hint n i (hi.trans_le (hk n)))
  rw [mesh_zero] at hsum
  have heach (i : ℕ) (hi : i < 2^n) :
      |h (mesh T n i) * (T / (2 : ℝ)^n) -
        ∫ t in mesh T n i..mesh T n (i+1), h t| ≤ ζ * (T / (2 : ℝ)^n) := by
    have heq : h (mesh T n i) * (T / (2 : ℝ)^n) =
        ∫ _ : ℝ in mesh T n i..mesh T n (i+1), h (mesh T n i) := by
      rw [intervalIntegral.integral_const, mesh_step, smul_eq_mul, mul_comm]
    rw [heq, ← intervalIntegral.integral_sub intervalIntegrable_const (hint n i hi)]
    have hbound : ∀ t ∈ uIoc (mesh T n i) (mesh T n (i+1)),
        ‖h (mesh T n i) - h t‖ ≤ ζ := by
      intro t ht
      rw [uIoc_of_le (mesh_mono T hT n (Nat.le_succ i))] at ht
      have htT : t ∈ Icc 0 T := ⟨(mesh_mem T hT n i hi.le).1.trans ht.1.le,
        ht.2.trans (mesh_mem T hT n (i+1) hi).2⟩
      have hdist : dist (mesh T n i) t < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 ht.1.le)]
        have hstep := mesh_step T n i
        have ht' : t ≤ mesh T n (i+1) := ht.2
        linarith
      simpa only [Real.norm_eq_abs, Real.dist_eq] using
        (hmod _ (mesh_mem T hT n i hi.le) _ htT hdist).le
    have hbound' := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, mesh_step, abs_of_nonneg (div_nonneg hT (by positivity))] at hbound'
    exact hbound'
  rw [Real.dist_eq, sub_zero, ← hsum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range (k n),
        |h (mesh T n i) * (T / (2 : ℝ)^n) -
          ∫ t in mesh T n i..mesh T n (i+1), h t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (k n), ζ * (T / (2 : ℝ)^n) :=
      Finset.sum_le_sum (fun i hi => heach i ((Finset.mem_range.1 hi).trans_le (hk n)))
    _ ≤ ζ * T := prefix_const_sum_le hT hζ.le (k n) n (hk n)
    _ < ε := by
      dsimp [ζ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < T+1)]
      nlinarith

lemma mesh_prefix_riemann_tendsto {h : ℝ → ℝ} {T S : ℝ}
    (hT : 0 ≤ T) (hh : ContinuousOn h (Icc 0 T))
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ 2^n) (hS : S ∈ Icc 0 T)
    (hlim : Tendsto (fun n => mesh T n (k n)) atTop (𝓝 S)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (k n),
      h (mesh T n i) * (T / (2 : ℝ)^n)) atTop (𝓝 (∫ t in (0 : ℝ)..S, h t)) := by
  have hint : IntegrableOn h (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    exact hh.integrableOn_Icc
  have hc := intervalIntegral.continuousOn_primitive_interval hint
  rw [uIcc_of_le hT] at hc
  have hi := (hc S hS).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Eventually.of_forall fun n => mesh_mem T hT n (k n) (hk n)⟩)
  have he := (mesh_prefix_riemann_error hT hh k hk).add hi
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using he

lemma mesh_prefix_remainder_tendsto {f : ℕ → ℕ → ℝ → ℝ} {b : ℝ → ℝ}
    (hf : ∀ n i, ContDiff ℝ 3 (f n i))
    {T V K : ℝ} (hT : 0 ≤ T) (hb : ContinuousOn b (Icc 0 T)) (hK : 0 ≤ K)
    (h3 : ∀ n i x, |iteratedDeriv 3 (f n i) x| ≤ K)
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ 2^n)
    (hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1)) - b (mesh T n i))^2) atTop (𝓝 V)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (k n),
      remainder₂ (f n i) (b (mesh T n i)) (b (mesh T n (i+1)))) atTop (𝓝 0) := by
  have hV : 0 ≤ V := ge_of_tendsto hQ (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε / ((K+1)*(V+1))
  have hδ : 0 < δ := div_pos hε (mul_pos (by linarith) (by linarith))
  have hs := mesh_increments_small hT hb hδ
  have hq := hQ.eventually (gt_mem_nhds (show V < V+1 by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.and hq)
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨hs, hq⟩
  have hr := sum_family_remainder₂_bound (hf n) (fun i => b (mesh T n i)) (k n) K δ hK hδ.le
    (fun i _ z _ => h3 n i z) (fun i hi => (hs i (hi.trans_le (hk n))).le)
  simp only [Real.dist_eq, sub_zero]
  calc
    _ ≤ K * δ / 6 * ∑ i ∈ Finset.range (k n),
        (b (mesh T n (i+1)) - b (mesh T n i))^2 := hr
    _ ≤ K * δ / 6 * ∑ i ∈ Finset.range (2^n),
        (b (mesh T n (i+1)) - b (mesh T n i))^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (hk n))
        (fun i _ _ => sq_nonneg _)
    _ ≤ K * δ / 6 * (V+1) := mul_le_mul_of_nonneg_left hq.le (by positivity)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < (K+1)*(V+1) := mul_pos (by linarith) (by linarith)
      have hid : K * (ε / ((K+1)*(V+1))) / 6 * (V+1) = ε * (K / (6*(K+1))) := by
        field_simp
      rw [hid]
      have hk : K / (6*(K+1)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      simpa using mul_lt_mul_of_pos_left hk hε

lemma mesh_prefix_time_increment_tendsto {F V : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {T S : ℝ}
    (hT : 0 ≤ T)
    (hF : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T))
    (hD : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun u => F u x) (V t x) t)
    (hV : ContinuousOn (fun p : ℝ × ℝ => V p.1 (b p.2)) ((Icc 0 T) ×ˢ (Icc 0 T)))
    (k : ℕ → ℕ) (hk : ∀ n, k n ≤ 2^n) (hS : S ∈ Icc 0 T)
    (hlim : Tendsto (fun n => mesh T n (k n)) atTop (𝓝 S)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (k n),
      (F (mesh T n (i+1)) (b (mesh T n (i+1))) -
        F (mesh T n i) (b (mesh T n (i+1))))) atTop
      (𝓝 (∫ t in (0 : ℝ)..S, V t (b t))) := by
  rcases hT.eq_or_lt with hT | hT
  · subst T
    have : S = 0 := le_antisymm hS.2 hS.1
    subst S
    simp [mesh]
  have hVc : ContinuousOn (fun t => V t (b t)) (Icc 0 T) :=
    hV.comp (continuousOn_id.prodMk continuousOn_id) (fun t ht => ⟨ht, ht⟩)
  have hriem := mesh_prefix_riemann_tendsto hT.le hVc k hk hS hlim
  have herror : Tendsto (fun n => ∑ i ∈ Finset.range (k n),
      (F (mesh T n (i+1)) (b (mesh T n (i+1))) -
        F (mesh T n i) (b (mesh T n (i+1))) -
          V (mesh T n i) (b (mesh T n i)) * (T / (2 : ℝ)^n))) atTop (𝓝 0) := by
    have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hV
    apply Metric.tendsto_atTop.2
    intro ε hε
    let ζ : ℝ := ε / (T+1)
    have hζ : 0 < ζ := div_pos hε (by linarith)
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 hu ζ hζ
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((mesh_step_tendsto T).eventually (gt_mem_nhds hδ))
    refine ⟨N, fun n hn => ?_⟩
    have hnδ := hN n hn
    have heach (i : ℕ) (hi : i < 2^n) :
        |F (mesh T n (i+1)) (b (mesh T n (i+1))) -
          F (mesh T n i) (b (mesh T n (i+1))) -
            V (mesh T n i) (b (mesh T n i)) * (T / (2 : ℝ)^n)| ≤
        ζ * (T / (2 : ℝ)^n) := by
      have hstep_pos : mesh T n i < mesh T n (i+1) := by
        have : 0 < mesh T n (i+1) - mesh T n i := by rw [mesh_step]; positivity
        linarith
      have hleft := mesh_mem T hT.le n i hi.le
      have hright := mesh_mem T hT.le n (i+1) hi
      obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
        (fun t => F t (b (mesh T n (i+1)))) (fun t => V t (b (mesh T n (i+1))))
        hstep_pos ((hF _).mono (Icc_subset_Icc hleft.1 hright.2))
        (fun t ht => hD t ⟨hleft.1.trans_lt ht.1, ht.2.trans_le hright.2⟩ _)
      have hcT : c ∈ Icc 0 T := ⟨hleft.1.trans hc.1.le, hc.2.le.trans hright.2⟩
      have hdist : dist (c, mesh T n (i+1)) (mesh T n i, mesh T n i) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        constructor
        · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hc.1.le)]
          have hcs := hc.2
          have hstep := mesh_step T n i
          linarith
        · rw [Real.dist_eq, mesh_step, abs_of_nonneg (by positivity)]
          exact hnδ
      have hvmod := (hmod (c, mesh T n (i+1)) ⟨hcT, hright⟩
        (mesh T n i, mesh T n i) ⟨hleft, hleft⟩ hdist).le
      simp only [Real.dist_eq] at hvmod
      have hid : F (mesh T n (i+1)) (b (mesh T n (i+1))) -
          F (mesh T n i) (b (mesh T n (i+1))) =
          V c (b (mesh T n (i+1))) * (T / (2 : ℝ)^n) := by
        rw [mesh_step] at heq
        exact (eq_div_iff (ne_of_gt (div_pos hT (by positivity)))).1 heq |>.symm
      rw [hid, ← sub_mul, abs_mul, abs_of_nonneg (show 0 ≤ T / (2 : ℝ)^n by positivity)]
      exact mul_le_mul_of_nonneg_right hvmod (by positivity)
    rw [Real.dist_eq, sub_zero]
    calc
      _ ≤ ∑ i ∈ Finset.range (k n),
          |F (mesh T n (i+1)) (b (mesh T n (i+1))) -
            F (mesh T n i) (b (mesh T n (i+1))) -
              V (mesh T n i) (b (mesh T n i)) * (T / (2 : ℝ)^n)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range (k n), ζ * (T / (2 : ℝ)^n) :=
        Finset.sum_le_sum (fun i hi => heach i ((Finset.mem_range.1 hi).trans_le (hk n)))
      _ ≤ ζ * T := prefix_const_sum_le hT.le hζ.le (k n) n (hk n)
      _ < ε := by
        dsimp [ζ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < T+1)]
        nlinarith
  have hadd := herror.add hriem
  simp only [Finset.sum_sub_distrib, sub_add_cancel, zero_add] at hadd
  simpa only [Finset.sum_sub_distrib] using hadd

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianIto TaylorMeshes

lemma lt_stoppedDyadicIndex {T : ℝ≥0} (hT : 0 < T) (n i : ℕ) (t : ℝ≥0) :
    i < stoppedDyadicIndex T n t ↔ dyadicTime T n i < t := by
  have hd : 0 < T / (2 : ℝ≥0)^n := by positivity
  simp only [stoppedDyadicIndex, Nat.lt_ceil, lt_div_iff₀ hd, dyadicTime]

lemma stoppedDyadicIndex_le {T : ℝ≥0} (hT : 0 < T) (n : ℕ)
    {t : ℝ≥0} (ht : t ≤ T) : stoppedDyadicIndex T n t ≤ 2^n := by
  rw [stoppedDyadicIndex, Nat.ceil_le, div_le_iff₀ (by positivity : 0 < T / (2 : ℝ≥0)^n)]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel₀ _ (pow_ne_zero n (by norm_num : (2 : ℝ≥0) ≠ 0))] using ht

end SLEExactGauge
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_SimpleFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simple Fields for chordal SLE. -/

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
namespace SLEExactGauge
open BrownianPredictable BrownianIto TaylorMeshes
lemma stoppedDyadicIndex_bounds {T : ℝ≥0} (hT : 0 < T) (n : ℕ) (t : ℝ≥0) :
    t ≤ dyadicTime T n (stoppedDyadicIndex T n t) ∧
    dyadicTime T n (stoppedDyadicIndex T n t) ≤ t + T / (2 : ℝ≥0)^n := by
  have hd : 0 < T / (2 : ℝ≥0)^n := by positivity
  constructor
  · apply (div_le_iff₀ hd).mp
    exact Nat.le_ceil _
  · change (Nat.ceil (t / (T / (2 : ℝ≥0)^n)) : ℝ≥0) * (T / (2 : ℝ≥0)^n) ≤ _
    calc
      _ ≤ (t / (T / (2 : ℝ≥0)^n) + 1) * (T / (2 : ℝ≥0)^n) :=
        mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ _ from zero_le)).le hd.le
      _ = _ := by rw [add_mul, div_mul_cancel₀ _ hd.ne', one_mul]

lemma stoppedDyadicIndex_tendsto {T : ℝ≥0} (hT : 0 < T) (t : ℝ≥0) :
    Tendsto (fun n => mesh T n (stoppedDyadicIndex T n t)) atTop (𝓝 (t : ℝ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using (tendsto_const_nhds (x := (t : ℝ))).add (mesh_step_tendsto T))
  · intro n
    simpa only [← coe_dyadicTime] using
      (show (t : ℝ) ≤ (dyadicTime T n (stoppedDyadicIndex T n t) : ℝ) by
        exact_mod_cast (stoppedDyadicIndex_bounds hT n t).1)
  · intro n
    have hh := (stoppedDyadicIndex_bounds hT n t).2
    simpa only [← coe_dyadicTime, NNReal.coe_add, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
      using (show (dyadicTime T n (stoppedDyadicIndex T n t) : ℝ) ≤
        ((t + T / (2 : ℝ≥0)^n : ℝ≥0) : ℝ) by exact_mod_cast hh)

lemma stopping_before_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime f (fun ω => (τ ω : WithTop ℝ≥0))) (t : ℝ≥0) :
    MeasurableSet[f t] {ω | t < τ ω} := by
  simpa only [Set.compl_ofPred, WithTop.coe_le_coe, not_le] using (hτ.measurableSet_le t).compl

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes TimeField

lemma prefix_mask_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α) {k N : ℕ} (hk : k ≤ N) :
    (∑ i ∈ Finset.range N, if i < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
  classical
  calc
    _ = ∑ i ∈ Finset.range k, if i < k then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro i hi hni
      simp only [Finset.mem_range] at hni
      simp [hni]
    _ = _ := Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.mp hi)

lemma stoppedFieldSum_eq_prefix {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ≥0}
    (hT : 0 < T) (F : Ω → ℝ → ℝ → ℝ) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (n : ℕ) (ω : Ω) :
    stoppedFieldSum B T F τ n ω =
      ∑ i ∈ Finset.range (stoppedDyadicIndex T n (τ ω)),
        deriv (F ω (mesh T n i)) (B (dyadicTime T n i) ω) *
          (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω) := by
  unfold stoppedFieldSum
  simp_rw [← lt_stoppedDyadicIndex hT, ite_mul, zero_mul]
  exact prefix_mask_sum _ (stoppedDyadicIndex_le hT n (hτ ω))

 

theorem stopped_fieldSum_tendsto {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ s, Measurable (B s))
    (T : ℝ≥0) (F V : Ω → ℝ → ℝ → ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbτ : ∀ ω, τ ω ≤ T)
    (hreg : ∀ᵐ ω ∂P, FieldRegular (F ω) (V ω) (fun t => B t.toNNReal ω) T)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => F ω t (B t.toNNReal ω)) (Icc 0 T))
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)]
      (fun ω => iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)))
    (hC2 : ∀ n i, MemLp
      (fun ω => iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ ω ∂P,
      |iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω)| ≤ K₂) :
    ∀ᵐ ω ∂P, Tendsto (fun n => stoppedFieldSum B T F τ n ω) atTop
      (𝓝 (F ω (τ ω) (B (τ ω) ω) - F ω 0 (B 0 ω) -
        (∫ t in (0 : ℝ)..(τ ω : ℝ), V ω t (B t.toNNReal ω)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω : ℝ),
          iteratedDeriv 2 (F ω t) (B t.toNNReal ω))) := by
  classical
  rcases eq_or_lt_of_le (zero_le : 0 ≤ T) with hT | hT
  · subst T
    have hτ0 (ω : Ω) : τ ω = 0 := le_antisymm (hbτ ω) zero_le
    simp [stoppedFieldSum, dyadicTime, hτ0]
  let C (n i : ℕ) (ω : Ω) := if dyadicTime T n i < τ ω then
    iteratedDeriv 2 (F ω (mesh T n i)) (B (dyadicTime T n i) ω) else 0
  have hs (n i : ℕ) : MeasurableSet[pastSigma B (dyadicTime T n i)]
      {ω | dyadicTime T n i < τ ω} := by
    have he := stopping_before_measurable hτ (dyadicTime T n i)
    exact (le_of_eq (Filtration.natural_eq_comap B (fun t => (hm t).stronglyMeasurable) _)) _ he
  have hCp (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (C n i) :=
    (hC n i).ite (hs n i) measurable_const
  have hC2p (n i : ℕ) : MemLp (C n i) 2 P := by
    have hma := (hCp n i).mono
      (le_trans (le_of_eq (Filtration.natural_eq_comap B
        (fun t => (hm t).stronglyMeasurable) _).symm) (Filtration.le _ _)) le_rfl
    apply MemLp.of_bound hma.aestronglyMeasurable K₂
    filter_upwards [hbound n i] with ω hω
    dsimp only [C]
    split_ifs <;> simpa only [Real.norm_eq_abs, abs_zero] using (by assumption : _ ≤ K₂)
  have hbp (n i : ℕ) : ∀ᵐ ω ∂P, |C n i ω| ≤ K₂ := by
    filter_upwards [hbound n i] with ω hω
    dsimp only [C]
    split_ifs <;> simp_all
  have he := brownian_dyadic_weighted_quadraticError_tendsto hB T C hCp hC2p K₂ hK₂ hbp
  filter_upwards [hB.cont, quadraticSum_tendsto hB T, he, hreg, hcont] with ω hcω hQω heω hrω hfω
  let b : ℝ → ℝ := fun t => B t.toNNReal ω
  let k : ℕ → ℕ := fun n => stoppedDyadicIndex T n (τ ω)
  have hk (n : ℕ) : k n ≤ 2^n := stoppedDyadicIndex_le hT n (hbτ ω)
  have hS : (τ ω : ℝ) ∈ Icc (0 : ℝ) T := ⟨(τ ω).coe_nonneg, by exact_mod_cast hbτ ω⟩
  have hlim : Tendsto (fun n => mesh T n (k n)) atTop (𝓝 (τ ω : ℝ)) := stoppedDyadicIndex_tendsto hT _
  have hb : Continuous b := hcω.comp continuous_real_toNNReal
  have hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1))-b (mesh T n i))^2) atTop (𝓝 (T : ℝ)) := by
    simpa only [b, mesh_toNNReal, quadraticSum] using hQω
  obtain ⟨K₃, hK₃, h₃⟩ := hrω.third_bound
  have hr := mesh_prefix_remainder_tendsto
    (f := fun n i => F ω (mesh T n i)) (fun _ _ => hrω.smooth _) T.coe_nonneg
    hb.continuousOn hK₃ (fun _ _ x => h₃ _ x) k hk hQ
  have hriem := mesh_prefix_riemann_tendsto T.coe_nonneg hrω.second_cont k hk hS hlim
  have htime := mesh_prefix_time_increment_tendsto (b := b) T.coe_nonneg hrω.time_cont
    hrω.time_deriv hrω.drift_cont k hk hS hlim
  let Q (n : ℕ) := ∑ i ∈ Finset.range (k n),
    iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
      (b (mesh T n (i+1))-b (mesh T n i))^2
  have hQweighted : Tendsto Q atTop
      (𝓝 (∫ t in (0 : ℝ)..(τ ω : ℝ), iteratedDeriv 2 (F ω t) (b t))) := by
    have heq (n : ℕ) : Q n = dyadicQuadraticError B T C n ω +
        ∑ i ∈ Finset.range (k n), iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
          ((T : ℝ) / (2 : ℝ)^n) := by
      have hmask : dyadicQuadraticError B T C n ω =
          ∑ i ∈ Finset.range (k n),
          iteratedDeriv 2 (F ω (mesh T n i)) (b (mesh T n i)) *
            ((b (mesh T n (i+1))-b (mesh T n i))^2 - (T : ℝ) / (2 : ℝ)^n) := by
        simp only [dyadicQuadraticError, C, b, mesh_toNNReal]
        simp_rw [← lt_stoppedDyadicIndex hT, ite_mul, zero_mul]
        exact prefix_mask_sum _ (hk n)
      rw [hmask, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simpa only [b, ← heq, zero_add] using heω.add hriem
  have hTel (n : ℕ) : ∑ i ∈ Finset.range (k n),
      (F ω (mesh T n (i+1)) (b (mesh T n (i+1))) - F ω (mesh T n i) (b (mesh T n i))) =
        F ω (mesh T n (k n)) (b (mesh T n (k n))) - F ω 0 (B 0 ω) := by
    rw [Finset.sum_range_sub (fun i => F ω (mesh T n i) (b (mesh T n i))) (k n), mesh_zero]
    simp only [b, Real.toNNReal_zero]
  have hIdentity (n : ℕ) : stoppedFieldSum B T F τ n ω =
      F ω (mesh T n (k n)) (b (mesh T n (k n))) - F ω 0 (B 0 ω) -
        (∑ i ∈ Finset.range (k n),
          (F ω (mesh T n (i+1)) (b (mesh T n (i+1))) -
            F ω (mesh T n i) (b (mesh T n (i+1))))) - (1/2 : ℝ) * Q n -
        ∑ i ∈ Finset.range (k n), remainder₂ (F ω (mesh T n i))
          (b (mesh T n i)) (b (mesh T n (i+1))) := by
    rw [← hTel n]
    simp only [Q, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [stoppedFieldSum_eq_prefix B hT F τ hbτ]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [remainder₂, iteratedDeriv_succ, iteratedDeriv_zero, b, mesh_toNNReal]
    ring
  have hend := (hfω _ hS).tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Eventually.of_forall fun n => mesh_mem T T.coe_nonneg n (k n) (hk n)⟩)
  have ht := (((hend.sub_const (F ω 0 (B 0 ω))).sub htime).sub
    (hQweighted.const_mul (1/2 : ℝ))).sub hr
  simpa only [Function.comp_apply, b, Real.toNNReal_coe, ← hIdentity, sub_zero] using ht

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}

theorem ClippedLogSolution.compact_stopped_field_ito
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (φ : (ℂ × ℝ) × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbτ : ∀ ω, τ ω ≤ T) :
    ∀ᵐ ω ∂P, Tendsto (fun n => stoppedFieldSum B T (fun ω t x => φ (c.Q t ω, x)) τ n ω) atTop
      (𝓝 (φ (c.Q (τ ω) ω, B (τ ω) ω) - φ (c.Q 0 ω, B 0 ω) -
        (∫ t in (0 : ℝ)..(τ ω : ℝ), fderiv ℝ φ (c.Q t ω, B t.toNNReal ω) (c.velocity t ω, 0)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω : ℝ),
          iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t.toNNReal ω))) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨K, hK, _⟩ := compact_smooth_bounded_lipschitz (spatialPartial φ 2)
    (spatialPartial_smooth φ hφ 2) (spatialPartial_compact φ hφc 2)
  have hb (t : ℝ≥0) (ω : Ω) :
      |iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t ω)| ≤ K := by
    simpa only [← spatialPartial_eq_iteratedDeriv φ hφ, Real.norm_eq_abs] using hK (c.Q t ω, B t ω)
  have hma (t : ℝ≥0) := c.partial_adapted φ hφ 2 t
  have hp (t : ℝ≥0) : MemLp
      (fun ω => iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t ω)) 2 P := by
    exact MemLp.of_bound ((hma t).mono (Filtration.le _ _) le_rfl).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb t ω)
  apply stopped_fieldSum_tendsto hB hm T (fun ω t x => φ (c.Q t ω, x))
    (fun ω t x => fderiv ℝ φ (c.Q t ω, x) (c.velocity t ω, 0)) τ hτ hbτ
    (Eventually.of_forall (c.compact_field_regular hBc φ hφ hφc T))
    (Eventually.of_forall fun ω =>
      (hφ.continuous.comp ((c.lipschitz ω).continuous.prodMk
        ((hBc ω).comp continuous_real_toNNReal))).continuousOn)
    (fun n i => ?_) (fun n i => ?_) K K.coe_nonneg (fun n i => ?_)
  · have hx := (hma (dyadicTime T n i)).mono
      (le_of_eq (natural_eq_pastSigma (B := B) (hm := hm) (dyadicTime T n i))) le_rfl
    simpa only [mesh_eq_dyadicTime] using hx
  · simpa only [mesh_eq_dyadicTime] using hp (dyadicTime T n i)
  · exact Eventually.of_forall fun ω => by
      simpa only [mesh_eq_dyadicTime] using hb (dyadicTime T n i) ω

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

lemma deriv_fiber_fderiv (φ : (ℂ × ℝ) × ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (q : ℂ × ℝ) (x : ℝ) :
    deriv (fun y => φ (q, y)) x = fderiv ℝ φ (q, x) (0, 1) := by
  exact ((hφ (q, x)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_const x q).prodMk (hasDerivAt_id x))).deriv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi} {q₀ : ℂ × ℝ}



theorem ClippedLogSolution.stopped_green_ito
    (c : ClippedLogSolution B hm κ lo hi hle q₀)
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (R : ℝ) (hR : 0 ≤ R)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (hbτ : ∀ ω, τ ω ≤ T)
    (hinside : ∀ ω t, t ≤ τ ω →
      ‖(c.Q t ω, B t ω)‖ ≤ R ∧ lo ≤ (c.Q t ω).1.im ∧ (c.Q t ω).1.im ≤ hi) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (if dyadicTime T n i < τ ω then
        greenLogCoefficient κ (c.Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω)
      else 0) * (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)) atTop
      (𝓝 (greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) - greenLogDensity κ q₀ 0)) := by
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_green_field κ R hR
  have hφ1 (q : ℂ × ℝ) (x : ℝ) (hq : ‖(q, x)‖ ≤ R) :
      deriv (fun y => φ (q, y)) x = greenLogCoefficient κ q x := by
    rw [deriv_fiber_fderiv φ (hφ.differentiable (by simp)), hφD q x hq,
      ← deriv_fiber_fderiv _ ((greenLogDensity_contDiff κ).differentiable (by simp))]
    exact (greenLogDensity_spatial_derivative κ q x).deriv
  have hrep := c.compact_stopped_field_ito hB hBc φ hφ hφc T τ hτ hbτ
  filter_upwards [hrep, hB.eval_zero_ae_eq_zero] with ω hrepω hB0
  have heq (n : ℕ) : stoppedFieldSum B T (fun ω t x => φ (c.Q t ω, x)) τ n ω =
      ∑ i ∈ Finset.range (2^n),
        (if dyadicTime T n i < τ ω then
          greenLogCoefficient κ (c.Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω)
        else 0) * (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mesh_eq_dyadicTime]
    split_ifs with ht
    · rw [hφ1 _ _ (hinside ω _ ht.le).1]
    · rfl
  let V (t : ℝ) := fderiv ℝ φ (c.Q t ω, B t.toNNReal ω) (c.velocity t ω, 0)
  let D (t : ℝ) := iteratedDeriv 2 (fun x => φ (c.Q t ω, x)) (B t.toNNReal ω)
  have hpair : Continuous (fun t : ℝ => (c.Q t ω, B t.toNNReal ω)) :=
    (c.lipschitz ω).continuous.prodMk ((hBc ω).comp continuous_real_toNNReal)
  have hVc : Continuous V := ((hφ.continuous_fderiv (by simp)).comp hpair).clm_apply
    ((c.velocity_continuous hBc ω).prodMk continuous_const)
  have hDc : Continuous D := by
    simpa only [Function.comp_def, spatialPartial_eq_iteratedDeriv φ hφ] using
      (spatialPartial_smooth φ hφ 2).continuous.comp hpair
  have hz : (∫ t in (0 : ℝ)..(τ ω : ℝ), V t) +
      (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω : ℝ), D t = 0 := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hVc.intervalIntegrable _ _) ((hDc.const_mul _).intervalIntegrable _ _)]
    calc
      _ = ∫ t in (0 : ℝ)..(τ ω : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (τ ω).coe_nonneg] at ht
        have htn : t.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.mpr ht.2
        obtain ⟨hball, hlo, hhi⟩ := hinside ω t.toNNReal htn
        rw [Real.coe_toNNReal _ ht.1] at hball hlo hhi
        exact compact_green_drift_zero κ hκ hκ8 lo hi hle φ _ _
          (hφD _ _ hball) (hφ2 _ _ hball) ⟨hlo, hhi⟩
      _ = 0 := by simp
  have hend := hφeq _ _ (hinside ω (τ ω) le_rfl).1
  have hstart := hφeq _ _ (hinside ω 0 zero_le).1
  simp only [NNReal.coe_zero, c.initial ω, hB0] at hstart
  have hval : φ (c.Q (τ ω) ω, B (τ ω) ω) - φ (c.Q 0 ω, B 0 ω) -
      (∫ t in (0 : ℝ)..(τ ω : ℝ), V t) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ ω : ℝ), D t =
        greenLogDensity κ (c.Q (τ ω) ω) (B (τ ω) ω) - greenLogDensity κ q₀ 0 := by
    rw [hend, c.initial ω, hB0, hstart]
    linarith
  simpa only [heq, ← hval, V, D] using hrepω

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField BrownianIto TaylorMeshes

lemma stopped_energy_tendsto {T : ℝ≥0} {S : ℝ≥0} (hS : S ≤ T)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (if dyadicTime T n i < S then f (dyadicTime T n i) else 0) *
        ((dyadicTime T n (i+1) : ℝ) - dyadicTime T n i)) atTop
      (𝓝 (∫ t in (0 : ℝ)..(S : ℝ), f t)) := by
  classical
  rcases eq_or_lt_of_le (zero_le : 0 ≤ T) with hT | hT
  · subst T
    have hS0 : S = 0 := le_antisymm hS zero_le
    simp [hS0, dyadicTime]
  · have hh := mesh_prefix_riemann_tendsto T.coe_nonneg hf
      (fun n => stoppedDyadicIndex T n S)
      (fun n => stoppedDyadicIndex_le hT n hS)
      (show (S : ℝ) ∈ Icc (0 : ℝ) T from ⟨S.coe_nonneg, by exact_mod_cast hS⟩)
      (stoppedDyadicIndex_tendsto hT S)
    have heq (n : ℕ) : (∑ i ∈ Finset.range (2^n),
        (if dyadicTime T n i < S then f (dyadicTime T n i) else 0) *
          ((dyadicTime T n (i+1) : ℝ) - dyadicTime T n i)) =
        ∑ i ∈ Finset.range (stoppedDyadicIndex T n S), f (mesh T n i) *
          ((T : ℝ) / (2 : ℝ)^n) := by
      simp_rw [dyadicTime_step, ← lt_stoppedDyadicIndex hT, ite_mul, zero_mul]
      rw [SLEExactGauge.prefix_mask_sum _ (stoppedDyadicIndex_le hT n hS)]
      simp only [mesh_eq_dyadicTime]
    simpa only [heq] using hh

end SLEExactGauge

 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge

lemma gaussian_exponential_lintegral (v : ℝ≥0) (c : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (c * x)) ∂gaussianReal 0 v) =
      ENNReal.ofReal (Real.exp ((v : ℝ) * c ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal c)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  congr 1
  simpa only [mgf, zero_mul, zero_add] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) c

lemma gaussian_compensated_exponential (v : ℝ≥0) (a c : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (a + c * x - (v : ℝ) * c ^ 2 / 2)) ∂gaussianReal 0 v) =
      ENNReal.ofReal (Real.exp a) := by
  have he (x : ℝ) : Real.exp (a + c * x - (v : ℝ) * c ^ 2 / 2) =
      Real.exp (a - (v : ℝ) * c ^ 2 / 2) * Real.exp (c * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (by fun_prop), gaussian_exponential_lintegral,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

 

lemma independent_gaussian_exponential
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ × ℝ} {Y : Ω → ℝ} {v : ℝ≥0}
    (hX : Measurable X) (hY : HasLaw Y (gaussianReal 0 v) μ)
    (hi : IndepFun X Y μ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω).1 + (X ω).2 * Y ω -
      (v : ℝ) * (X ω).2 ^ 2 / 2)) ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (X ω).1) ∂μ := by
  let f (p : (ℝ × ℝ) × ℝ) := ENNReal.ofReal
    (Real.exp (p.1.1 + p.1.2 * p.2 - (v : ℝ) * p.1.2 ^ 2 / 2))
  have hf : Measurable f := by unfold f; fun_prop
  have hmap : μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (gaussianReal 0 v) := by
    rw [IndepFun.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable hi, hY.map_eq]
  calc
    _ = ∫⁻ p, f p ∂μ.map (fun ω => (X ω, Y ω)) :=
      (lintegral_map' hf.aemeasurable (hX.aemeasurable.prodMk hY.aemeasurable)).symm
    _ = ∫⁻ p, ∫⁻ x, f (p, x) ∂gaussianReal 0 v ∂μ.map X := by
      rw [hmap, lintegral_prod f hf.aemeasurable]
    _ = ∫⁻ p, ENNReal.ofReal (Real.exp p.1) ∂μ.map X :=
      lintegral_congr fun p => gaussian_compensated_exponential v p.1 p.2
    _ = _ := lintegral_map' (by fun_prop) hX.aemeasurable

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma driverPredictableSum_measurable_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ s, Measurable (B s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t i)] (C i))
    (n : ℕ) : Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t n)]
      (driverPredictableSum B t C n) := by
  have hB := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted
  apply Finset.measurable_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  exact ((hC i).mono (Filtration.mono _ (ht hin.le)) le_rfl).mul
    ((hB.measurable_le (ht (Nat.succ_le_iff.mpr hin))).sub (hB.measurable_le (ht hin.le)))

lemma driverPredictableEnergy_measurable_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ s, Measurable (B s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t i)] (C i))
    (n : ℕ) : Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t n)]
      (driverPredictableEnergy t C n) := by
  apply Finset.measurable_sum
  intro i hi
  exact (((hC i).mono (Filtration.mono _ (ht (Finset.mem_range.mp hi).le)) le_rfl).pow_const 2).mul_const _

 

theorem driverPredictable_exponential
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ s, Measurable (B s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (C : ℕ → Ω → ℝ)
    (hC : ∀ i, Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t i)] (C i))
    (θ : ℝ) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * driverPredictableSum B t C n ω -
      θ ^ 2 * driverPredictableEnergy t C n ω / 2)) ∂P) = 1 := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  induction n with
  | zero => simp [driverPredictableSum, driverPredictableEnergy]
  | succ n hprev =>
    let a (ω : Ω) := θ * driverPredictableSum B t C n ω -
      θ ^ 2 * driverPredictableEnergy t C n ω / 2
    let X (ω : Ω) : ℝ × ℝ := (a ω, θ * C n ω)
    let Y (ω : Ω) := B (t (n+1)) ω - B (t n) ω
    let v := t (n+1) - t n
    have hXp : Measurable[Filtration.natural B (fun s => (hm s).stronglyMeasurable) (t n)] X :=
      (((driverPredictableSum_measurable_past B hm t ht C hC n).const_mul θ).sub
        (((driverPredictableEnergy_measurable_past B hm t ht C hC n).const_mul (θ^2)).div_const 2)).prodMk
          ((hC n).const_mul θ)
    have hX : Measurable X := hXp.mono (Filtration.le _ _) le_rfl
    have hY : HasLaw Y (gaussianReal 0 v) P := by
      simpa only [Y, v, add_tsub_cancel_of_le (ht (Nat.le_succ n))] using
        (hB.toIsPreBrownianReal.shift (t n)).hasLaw_eval v
    have hi : IndepFun X Y P := by
      rw [IndepFun_iff_Indep]
      have hb := brownian_increment_indep_natural hB hm (t n) v
      dsimp only [v] at hb
      rw [add_tsub_cancel_of_le (ht (Nat.le_succ n))] at hb
      exact indep_of_indep_of_le hb hXp.comap_le le_rfl
    have hvc : (v : ℝ) = (t (n+1) : ℝ) - t n :=
      NNReal.coe_sub (ht (Nat.le_succ n))
    have he (ω : Ω) : θ * driverPredictableSum B t C (n+1) ω -
        θ ^ 2 * driverPredictableEnergy t C (n+1) ω / 2 =
        (X ω).1 + (X ω).2 * Y ω - (v : ℝ) * (X ω).2 ^ 2 / 2 := by
      simp only [driverPredictableSum, driverPredictableEnergy, Finset.sum_range_succ,
        X, a, Y, hvc]
      ring
    simp_rw [he]
    rw [independent_gaussian_exponential hX hY hi]
    exact hprev

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi}

 

lemma clipped_family_initial_continuous
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (t : ℝ≥0) (ω : Ω) : Continuous (fun q => (c q).Q t ω) := by
  obtain ⟨L, K, hb, hl⟩ := clippedLogLoewnerField_bounds lo hi hle
  let D : ℝ≥0 := ⟨Real.exp ((K : ℝ) * (t : ℝ)), (Real.exp_pos _).le⟩
  apply (show LipschitzWith D (fun q => (c q).Q t ω) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro q q'
  have hd (x : ℂ × ℝ) (s : ℝ) (hs : s ∈ Ico (0 : ℝ) (t : ℝ)) :
      HasDerivWithinAt (fun v => (c x).Q v ω)
        (clippedLogLoewnerField lo hi hle (Real.sqrt κ * B s.toNNReal ω) ((c x).Q s ω)) (Ici s) s :=
    ((c x).derivative ω s hs.1).mono (Ici_subset_Ici.mpr hs.1)
  have hh := dist_le_of_trajectories_ODE
    (fun s => hl (Real.sqrt κ * B s.toNNReal ω))
    ((c q).lipschitz ω).continuous.continuousOn (hd q)
    ((c q').lipschitz ω).continuous.continuousOn (hd q')
    (show dist ((c q).Q 0 ω) ((c q').Q 0 ω) ≤ dist q q' by rw [(c q).initial, (c q').initial])
    (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  change dist ((c q).Q t ω) ((c q').Q t ω) ≤ Real.exp ((K : ℝ) * (t : ℝ)) * dist q q'
  simpa only [sub_zero, mul_comm] using hh

lemma clipped_family_past_measurable
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q) (t : ℝ≥0) :
    @Measurable ((ℂ × ℝ) × Ω) (ℂ × ℝ)
      ((inferInstance : MeasurableSpace (ℂ × ℝ)).prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) t))
      (inferInstance : MeasurableSpace (ℂ × ℝ)) (fun p => (c p.1).Q t p.2) := by
  have hc := clipped_family_initial_continuous c t
  have ha (q : ℂ × ℝ) := (c q).adapted t
  let : MeasurableSpace Ω := Filtration.natural B (fun s => (hm s).stronglyMeasurable) t
  exact measurable_uncurry_of_continuous_of_measurable hc ha

lemma clipped_family_joint_measurable
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q) :
    Measurable (fun p : ℝ≥0 × ((ℂ × ℝ) × Ω) => (c p.2.1).Q p.1 p.2.2) := by
  change Measurable (Function.uncurry (fun (t : ℝ≥0) (p : (ℂ × ℝ) × Ω) => (c p.1).Q t p.2))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro p
    exact ((c p.1).lipschitz p.2).continuous.comp NNReal.continuous_coe
  · intro t
    have h := clipped_family_past_measurable c t
    exact h.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (Filtration.le _ _))) le_rfl

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_ExponentialMartingales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential Martingales for chordal SLE. -/

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
namespace SLEExactGauge
open L2Limit
lemma finite_uniformIntegrable_one_of_eLpNorm_two_bounded {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ι → Ω → ℝ}
    (hXm : ∀ i, AEStronglyMeasurable (X i) P) (C : ℝ≥0)
    (hC : ∀ i, eLpNorm (X i) 2 P ≤ C) : UniformIntegrable X 1 P := by
  let D : ℝ≥0∞ := C * (P univ) ^ (1/2 : ℝ)
  have hDt : D ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top P univ))
  refine ⟨hXm, OAI.unifIntegrable_of_enn ?_, D.toNNReal, ?_⟩
  · intro bound hbound
    obtain ⟨small, hsmall, hsmall_bound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hbound
    let ε : ℝ := small
    have hε : 0 < ε := by exact_mod_cast hsmall
    let d : ℝ≥0 := ⟨ε / ((C : ℝ)+1), div_nonneg hε.le (by positivity)⟩
    have hd : 0 < (d : ℝ) := div_pos hε (by positivity)
    refine ⟨ENNReal.ofReal ((d : ℝ)^2), ENNReal.ofReal_pos.mpr (sq_pos_of_pos hd),
      fun i s hμs => ?_⟩
    have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := P.restrict s)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hXm i).restrict
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one] at hb
    rw [Measure.restrict_apply_univ] at hb
    have hp : (P s) ^ (1/2 : ℝ) ≤ (d : ℝ≥0∞) := by
      calc
        _ ≤ (ENNReal.ofReal ((d : ℝ)^2)) ^ (1/2 : ℝ) :=
          ENNReal.rpow_le_rpow hμs (by norm_num)
        _ = _ := by
          rw [ENNReal.ofReal_pow d.coe_nonneg]
          simp only [ENNReal.ofReal_coe_nnreal]
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
    calc
      _ ≤ eLpNorm (X i) 2 (P.restrict s) * (P s) ^ (1/2 : ℝ) := hb
      _ ≤ C * (d : ℝ≥0∞) := mul_le_mul
        ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i)) hp (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal]
        simp only [NNReal.coe_mul]
        apply ENNReal.ofReal_le_ofReal
        change (C : ℝ) * (ε / ((C : ℝ)+1)) ≤ ε
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith
      _ ≤ bound := by
        simpa only [ε, ENNReal.ofReal_coe_nnreal] using hsmall_bound.le
  · intro i
    have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hXm i)
    rw [ENNReal.coe_toNNReal hDt]
    norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one] at hb
    exact hb.trans (mul_le_mul (hC i) le_rfl bot_le bot_le)

theorem finite_L1_tendsto_of_square_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (A : ℝ)
    (hA : ∀ n, (∫ ω, X n ω ^ 2 ∂P) ≤ A)
    (hXY : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Integrable Y P ∧ Tendsto (fun n => eLpNorm (X n - Y) 1 P) atTop (𝓝 0) := by
  let C : ℝ≥0∞ := (ENNReal.ofReal A) ^ (1/2 : ℝ)
  have hCt : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hC (n : ℕ) : eLpNorm (X n) 2 P ≤ C.toNNReal := by
    rw [ENNReal.coe_toNNReal hCt, eLpNorm_two_eq_integral_sq (hX n)]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hA n)) (by norm_num)
  have hui := finite_uniformIntegrable_one_of_eLpNorm_two_bounded
    (fun n => (hX n).aestronglyMeasurable) C.toNNReal hC
  have hY := hui.memLp_of_ae_tendsto hXY
  exact ⟨memLp_one_iff_integrable.1 hY,
    tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ℝ≥0∞) ≤ 1)
      (by norm_num) (fun n => (hX n).aestronglyMeasurable) hY hui.unifIntegrable hXY⟩

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

lemma product_memLp_two_of_section_square_bound
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν] [SFinite P]
    {X : Z × Ω → ℝ} (hX : Measurable X)
    (hX2 : ∀ z, MemLp (fun ω => X (z, ω)) 2 P)
    (V : ℝ) (hV : ∀ z, (∫ ω, X (z, ω)^2 ∂P) ≤ V) :
    MemLp X 2 (ν.prod P) ∧
      (∫ p, X p ^ 2 ∂(ν.prod P)) ≤ V * (ν univ).toReal := by
  have hm : StronglyMeasurable (fun z => ∫ ω, X (z, ω)^2 ∂P) :=
    (hX.pow_const 2).stronglyMeasurable.integral_prod_right'
  have hn (z : Z) : 0 ≤ ∫ ω, X (z, ω)^2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hi : Integrable (fun z => ∫ ω, X (z, ω)^2 ∂P) ν := by
    apply Integrable.of_bound hm.aestronglyMeasurable V
    exact Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hn z)]; exact hV z
  have hisq : Integrable (fun p => X p ^ 2) (ν.prod P) := by
    apply (integrable_prod_iff (hX.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun z => (hX2 z).integrable_sq, ?_⟩
    simpa only [Real.norm_eq_abs, abs_sq] using hi
  refine ⟨(memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr hisq, ?_⟩
  rw [integral_prod _ hisq]
  calc
    _ ≤ ∫ _z, V ∂ν := integral_mono hi (integrable_const _) hV
    _ = _ := by simp [mul_comm, Measure.real]

lemma area_eLpNorm_one_le_product
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [SFinite ν] [SFinite P]
    {X Y : Z × Ω → ℝ} (hX : Integrable X (ν.prod P)) (hY : Integrable Y (ν.prod P)) :
    eLpNorm (fun ω => (∫ z, X (z, ω) ∂ν) - ∫ z, Y (z, ω) ∂ν) 1 P ≤
      eLpNorm (X - Y) 1 (ν.prod P) := by
  rw [eLpNorm_one_eq_lintegral_enorm
    (f := fun ω => (∫ z, X (z, ω) ∂ν) - ∫ z, Y (z, ω) ∂ν),
    eLpNorm_one_eq_lintegral_enorm]
  calc
    _ ≤ ∫⁻ ω, ∫⁻ z, ‖X (z, ω) - Y (z, ω)‖ₑ ∂ν ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hX.prod_left_ae, hY.prod_left_ae] with ω hx hy
      rw [← integral_sub hx hy]
      exact enorm_integral_le_lintegral_enorm _
    _ = _ := by
      rw [← lintegral_lintegral_swap (hX.sub hY).aestronglyMeasurable.enorm]
      exact (lintegral_prod _ (hX.sub hY).aestronglyMeasurable.enorm).symm

 

theorem area_L1_tendsto_of_square_bound
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν] [IsProbabilityMeasure P]
    {X : ℕ → Z × Ω → ℝ} {Y : Z × Ω → ℝ}
    (hXm : ∀ n, Measurable (X n)) (hYm : Measurable Y)
    (hX2 : ∀ n z, MemLp (fun ω => X n (z, ω)) 2 P)
    (V : ℝ) (hV : ∀ n z, (∫ ω, X n (z, ω)^2 ∂P) ≤ V)
    (hXY : ∀ z, ∀ᵐ ω ∂P, Tendsto (fun n => X n (z, ω)) atTop (𝓝 (Y (z, ω)))) :
    Integrable Y (ν.prod P) ∧ Tendsto (fun n =>
      eLpNorm (fun ω => (∫ z, X n (z, ω) ∂ν) - ∫ z, Y (z, ω) ∂ν) 1 P) atTop (𝓝 0) := by
  have hb (n : ℕ) := product_memLp_two_of_section_square_bound (ν := ν) (P := P) (hXm n) (hX2 n) V (hV n)
  have hc : ∀ᵐ p ∂(ν.prod P), Tendsto (fun n => X n p) atTop (𝓝 (Y p)) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hXm hYm)).mpr (Eventually.of_forall hXY)
  obtain ⟨hi, ht⟩ := finite_L1_tendsto_of_square_bound (fun n => (hb n).1)
    (V * (ν univ).toReal) (fun n => (hb n).2) hc
  refine ⟨hi, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => bot_le) (fun n => area_eLpNorm_one_le_product ((hb n).1.integrable (by norm_num)) hi)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
open BrownianPredictable PredictableLimit

lemma area_driver_sum {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} [IsFiniteMeasure ν]
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (C : ℕ → Z × Ω → ℝ)
    (hC : ∀ i, Measurable (C i)) (K : ℝ) (hb : ∀ i z ω, |C i (z, ω)| ≤ K)
    (n : ℕ) (ω : Ω) :
    (∫ z, driverPredictableSum B t (fun i ω => C i (z, ω)) n ω ∂ν) =
      driverPredictableSum B t (fun i ω => ∫ z, C i (z, ω) ∂ν) n ω := by
  have hi (i : ℕ) : Integrable (fun z => C i (z, ω)) ν :=
    Integrable.of_bound ((hC i).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable K
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb i z ω)
  simp only [driverPredictableSum]
  rw [integral_finsetSum _ (fun i _ => (hi i).mul_const _)]
  exact Finset.sum_congr rfl fun i hi => integral_mul_const _ _

 

theorem brownian_area_sum_L1_limit
    {Z Ω : Type*} [MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (T : ℝ≥0) (C : ℕ → ℕ → Z × Ω → ℝ)
    (hCm : ∀ n i, Measurable (C n i))
    (hCa : ∀ n i z, Measurable[Filtration.natural B
      (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)] (fun ω => C n i (z, ω)))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ n i z ω, |C n i (z, ω)| ≤ K)
    (Y : Z × Ω → ℝ) (hYm : Measurable Y)
    (hlim : ∀ z, ∀ᵐ ω ∂P, Tendsto
      (fun n => driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (z, ω)) (2^n) ω)
      atTop (𝓝 (Y (z, ω)))) :
    Integrable Y (ν.prod P) ∧ Tendsto (fun n =>
      eLpNorm (fun ω => driverPredictableSum B (dyadicTime T n)
        (fun i ω => ∫ z, C n i (z, ω) ∂ν) (2^n) ω - ∫ z, Y (z, ω) ∂ν) 1 P)
        atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let X (n : ℕ) (p : Z × Ω) :=
    driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (p.1, ω)) (2^n) p.2
  have hCp (n i : ℕ) (z : Z) : Measurable[pastSigma B (dyadicTime T n i)]
      (fun ω => C n i (z, ω)) := by
    exact (hCa n i z).mono
      (le_of_eq (Filtration.natural_eq_comap B (fun t => (hm t).stronglyMeasurable) _)) le_rfl
  have hC2 (n i : ℕ) (z : Z) : MemLp (fun ω => C n i (z, ω)) 2 P :=
    MemLp.of_bound ((hCm n i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb n i z ω)
  have hXm (n : ℕ) : Measurable (X n) := by
    apply Finset.measurable_sum
    intro i hi
    exact (hCm n i).mul (((hm _).comp measurable_snd).sub ((hm _).comp measurable_snd))
  have hX2 (n : ℕ) (z : Z) : MemLp (fun ω => X n (z, ω)) 2 P := by
    exact dyadicDriverSum_memLp hB T (fun n i ω => C n i (z, ω))
      (fun n i => hCp n i z) (fun n i => hC2 n i z) n
  have hV (n : ℕ) (z : Z) : (∫ ω, X n (z, ω)^2 ∂P) ≤ K^2 * (T : ℝ) := by
    change (∫ ω, (∑ i ∈ Finset.range (2^n), C n i (z, ω) *
      (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)) ^ 2 ∂P) ≤ _
    rw [brownian_predictableSum_isometry hB _ (dyadicTime_mono T n) _
      (fun i => hCp n i z) (fun i => hC2 n i z)]
    calc
      _ ≤ ∑ i ∈ Finset.range (2^n), K^2 * ((T : ℝ) / (2 : ℝ)^n) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [dyadicTime_step]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc
          _ ≤ ∫ _ω, K^2 ∂P := integral_mono (hC2 n i z).integrable_sq (integrable_const _) fun ω =>
            by
              have hh := (sq_le_sq₀ (abs_nonneg (C n i (z, ω))) hK).mpr (hb n i z ω)
              simpa only [sq_abs] using hh
          _ = K^2 := by simp
      _ = K^2 * (T : ℝ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
  obtain ⟨hi, ht⟩ := area_L1_tendsto_of_square_bound (ν := ν) hXm hYm hX2 _ hV hlim
  refine ⟨hi, ?_⟩
  have he (n : ℕ) (ω : Ω) : (∫ z, X n (z, ω) ∂ν) =
      driverPredictableSum B (dyadicTime T n) (fun i ω => ∫ z, C n i (z, ω) ∂ν) (2^n) ω :=
    area_driver_sum B _ _ (hCm n) K (hb n) _ ω
  simpa only [he] using ht

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
open BrownianPredictable PredictableLimit

 

theorem brownian_area_exponential_limit
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (T : ℝ≥0) (C : ℕ → ℕ → Z × Ω → ℝ)
    (hCm : ∀ n i, Measurable (C n i))
    (hCa : ∀ n i, @Measurable (Z × Ω) ℝ
      (mZ.prod (Filtration.natural B (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)))
      (borel ℝ) (C n i))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ n i z ω, |C n i (z, ω)| ≤ K)
    (Y : Z × Ω → ℝ) (hYm : Measurable Y)
    (hlim : ∀ z, ∀ᵐ ω ∂P, Tendsto
      (fun n => driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (z, ω)) (2^n) ω)
      atTop (𝓝 (Y (z, ω))))
    (Q : Ω → ℝ)
    (hE : ∀ᵐ ω ∂P, Tendsto (fun n => driverPredictableEnergy (dyadicTime T n)
      (fun i ω => ∫ z, C n i (z, ω) ∂ν) (2^n) ω) atTop (𝓝 (Q ω)))
    (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * (∫ z, Y (z, ω) ∂ν) - θ^2 * Q ω / 2)) ∂P) ≤ 1 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let D (n i : ℕ) (ω : Ω) := ∫ z, C n i (z, ω) ∂ν
  have hDa (n i : ℕ) : Measurable[Filtration.natural B
      (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)] (D n i) := by
    let : MeasurableSpace Ω := Filtration.natural B
      (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)
    exact (hCa n i).stronglyMeasurable.integral_prod_left'.measurable
  let X (n : ℕ) := driverPredictableSum B (dyadicTime T n) (D n) (2^n)
  let E (n : ℕ) := driverPredictableEnergy (dyadicTime T n) (D n) (2^n)
  have hXm (n : ℕ) : Measurable (X n) :=
    (driverPredictableSum_measurable_past B hm _ (dyadicTime_mono T n) _ (hDa n) _).mono
      (Filtration.le _ _) le_rfl
  have hEm (n : ℕ) : Measurable (E n) :=
    (driverPredictableEnergy_measurable_past B hm _ (dyadicTime_mono T n) _ (hDa n) _).mono
      (Filtration.le _ _) le_rfl
  have hca (n i : ℕ) (z : Z) : Measurable[Filtration.natural B
      (fun t => (hm t).stronglyMeasurable) (dyadicTime T n i)] (fun ω => C n i (z, ω)) :=
    (hCa n i).comp (measurable_const.prodMk measurable_id)
  obtain ⟨hi, ht⟩ := brownian_area_sum_L1_limit (ν := ν) (P := P) hB hm T C hCm hca K hK hb Y hYm hlim
  have hY : Measurable (fun ω => ∫ z, Y (z, ω) ∂ν) :=
    hYm.stronglyMeasurable.integral_prod_left'.measurable
  have hc : TendstoInMeasure P X atTop (fun ω => ∫ z, Y (z, ω) ∂ν) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) (fun n => (hXm n).aestronglyMeasurable) hY.aestronglyMeasurable ht
  obtain ⟨ns, hns, hs⟩ := hc.exists_seq_tendsto_ae
  apply compensated_exponential_limit_energy (fun n => X (ns n)) (fun n => E (ns n))
    (fun ω => ∫ z, Y (z, ω) ∂ν) Q θ
    (fun n => (((hXm _).const_mul θ).sub (((hEm _).const_mul (θ^2)).div_const 2)).exp.ennreal_ofReal.aemeasurable)
    hs
  · filter_upwards [hE] with ω he
    exact he.comp hns.tendsto_atTop
  · intro n
    exact (driverPredictable_exponential hB hm _ (dyadicTime_mono T (ns n)) _ (hDa _) θ _).le

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma interval_integral_prefix_lt {S T : ℝ≥0} (hST : S ≤ T) (f : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..(T : ℝ), if t < (S : ℝ) then f t else 0) =
      ∫ t in (0 : ℝ)..(S : ℝ), f t := by
  calc
    _ = ∫ t in (0 : ℝ)..(T : ℝ), indicator {t : ℝ | t ≤ S} f t := by
      apply intervalIntegral.integral_congr_ae
      have hn : ∀ᵐ t : ℝ, t ≠ (S : ℝ) := by simp [ae_iff]
      filter_upwards [hn] with t ht
      intro _
      simp only [Set.indicator, Set.mem_ofPred_eq, le_iff_lt_or_eq, ht, or_false]
    _ = _ := intervalIntegral.integral_indicator ⟨S.coe_nonneg, by exact_mod_cast hST⟩



end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable

lemma areaWindowSample_measurable {Z : Type*} [MeasurableSpace Z]
    {f : ℝ × Z → ℝ} (hf : Measurable f) {σ τ : Z → ℝ≥0}
    (hσ : Measurable σ) (hτ : Measurable τ) (T : ℝ≥0) (n i : ℕ) :
    Measurable (areaWindowSample f σ τ T n i) :=
  (hf.comp (measurable_const.prodMk measurable_id)).ite
    ((measurableSet_le hσ measurable_const).inter (measurableSet_lt measurable_const (NNReal.continuous_coe.measurable.comp hτ))) measurable_const

lemma areaWindowSample_bound {Z : Type*} {f : ℝ × Z → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K)
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (n i : ℕ) (z : Z) :
    |areaWindowSample f σ τ T n i z| ≤ K := by
  unfold areaWindowSample
  split_ifs
  · exact hb _ _
  · simpa using hK

lemma window_pair_eq_prefix_difference {Z : Type*} (f : ℝ × Z → ℝ)
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (n i : ℕ) (z w : Z) :
    areaWindowSample f σ τ T n i z * areaWindowSample f σ τ T n i w =
      (if dyadicTime T n i < min (τ z) (τ w) then
        f (dyadicTime T n i,z) * f (dyadicTime T n i,w) else 0) -
      (if dyadicTime T n i < min (min (τ z) (τ w)) (max (σ z) (σ w)) then
        f (dyadicTime T n i,z) * f (dyadicTime T n i,w) else 0) := by
  simp only [areaWindowSample, lt_min_iff, lt_max_iff]
  by_cases hz : σ z ≤ dyadicTime T n i
  · by_cases hw : σ w ≤ dyadicTime T n i
    · simp [hz, hw, not_lt.mpr hz, not_lt.mpr hw]
      split_ifs <;> simp_all
    · simp only [hw, false_and, ite_false, mul_zero]
      have ht := lt_of_not_ge hw
      simp [ht, sub_self]
  · simp only [hz, false_and, ite_false, zero_mul]
    have ht := lt_of_not_ge hz
    simp [ht, sub_self]

lemma window_pair_energy_tendsto {Z : Type*} (f : ℝ × Z → ℝ)
    (hf : ∀ z, Continuous (fun t => f (t,z)))
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (hτ : ∀ z, τ z ≤ T) (z w : Z) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (areaWindowSample f σ τ T n i z * areaWindowSample f σ τ T n i w) *
        ((T : ℝ) / (2 : ℝ)^n)) atTop
      (𝓝 ((∫ t in (0 : ℝ)..(min (τ z) (τ w) : ℝ≥0), f (t,z) * f (t,w)) -
        ∫ t in (0 : ℝ)..(min (min (τ z) (τ w)) (max (σ z) (σ w)) : ℝ≥0), f (t,z) * f (t,w))) := by
  have hH := stopped_energy_tendsto ((min_le_left (τ z) (τ w)).trans (hτ z))
    ((hf z).mul (hf w)).continuousOn
  have hL := stopped_energy_tendsto
    ((min_le_left (min (τ z) (τ w)) (max (σ z) (σ w))).trans ((min_le_left (τ z) (τ w)).trans (hτ z)))
    ((hf z).mul (hf w)).continuousOn
  simp only [Pi.mul_apply] at hH hL
  convert hH.sub hL using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [window_pair_eq_prefix_difference, dyadicTime_step, sub_mul]

lemma window_pair_energy_bound {Z : Type*} {f : ℝ × Z → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K)
    (σ τ : Z → ℝ≥0) (T : ℝ≥0) (n : ℕ) (z w : Z) :
    |∑ i ∈ Finset.range (2^n),
      (areaWindowSample f σ τ T n i z * areaWindowSample f σ τ T n i w) *
        ((T : ℝ) / (2 : ℝ)^n)| ≤ K^2 * (T : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (2^n),
        |(areaWindowSample f σ τ T n i z * areaWindowSample f σ τ T n i w) *
          ((T : ℝ) / (2 : ℝ)^n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (2^n), K^2 * ((T : ℝ) / (2 : ℝ)^n) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (T : ℝ) / (2 : ℝ)^n), abs_mul, pow_two]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (areaWindowSample_bound hK hb σ τ T n i z)
          (areaWindowSample_bound hK hb σ τ T n i w) (abs_nonneg _) hK) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

lemma area_window_pair_energy_tendsto {Z : Type*} [MeasurableSpace Z]
    {ν : Measure Z} [IsFiniteMeasure ν]
    {f : ℝ × Z → ℝ} (hfm : Measurable f) (hfc : ∀ z, Continuous (fun t => f (t,z)))
    {σ τ : Z → ℝ≥0} (hσm : Measurable σ) (hτm : Measurable τ) (T : ℝ≥0) (hτ : ∀ z, τ z ≤ T)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (∫ z, areaWindowSample f σ τ T n i z ∂ν)^2 * ((T : ℝ) / (2 : ℝ)^n)) atTop
      (𝓝 (∫ p : Z × Z, ((∫ t in (0 : ℝ)..(min (τ p.1) (τ p.2) : ℝ≥0),
        f (t,p.1) * f (t,p.2)) - ∫ t in (0 : ℝ)..
          (min (min (τ p.1) (τ p.2)) (max (σ p.1) (σ p.2)) : ℝ≥0), f (t,p.1) * f (t,p.2)) ∂(ν.prod ν))) := by
  let H (n : ℕ) (p : Z × Z) := ∑ i ∈ Finset.range (2^n),
    (areaWindowSample f σ τ T n i p.1 * areaWindowSample f σ τ T n i p.2) *
      ((T : ℝ) / (2 : ℝ)^n)
  have hC (n i : ℕ) := areaWindowSample_measurable hfm hσm hτm T n i
  have hH (n : ℕ) : Measurable (H n) := by
    apply Finset.measurable_sum
    intro i hi
    exact (((hC n i).comp measurable_fst).mul ((hC n i).comp measurable_snd)).mul_const _
  have hbH (n : ℕ) (p : Z × Z) : ‖H n p‖ ≤ K^2 * (T : ℝ) := by
    rw [Real.norm_eq_abs]
    exact window_pair_energy_bound hK hb σ τ T n p.1 p.2
  have ht := tendsto_integral_of_dominated_convergence
    (μ := ν.prod ν) (fun _ => K^2 * (T : ℝ))
    (fun n => (hH n).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall (hbH n))
    (Eventually.of_forall fun p : Z × Z => window_pair_energy_tendsto f hfc σ τ T hτ p.1 p.2)
  have he (n : ℕ) : (∫ p, H n p ∂(ν.prod ν)) =
      ∑ i ∈ Finset.range (2^n), (∫ z, areaWindowSample f σ τ T n i z ∂ν)^2 *
        ((T : ℝ) / (2 : ℝ)^n) := by
    have hi (i : ℕ) : Integrable (areaWindowSample f σ τ T n i) ν :=
      Integrable.of_bound (hC n i).aestronglyMeasurable K
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact areaWindowSample_bound hK hb σ τ T n i z)
    change (∫ p : Z × Z, ∑ i ∈ Finset.range (2^n),
      (areaWindowSample f σ τ T n i p.1 * areaWindowSample f σ τ T n i p.2) *
        ((T : ℝ) / (2 : ℝ)^n) ∂(ν.prod ν)) = _
    rw [integral_finsetSum _ (fun i _ => ((hi i).mul_prod (hi i)).mul_const _)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const, integral_prod_mul, pow_two]
  simpa only [he] using ht

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma real_window_pair_eq (f : ℝ → ℝ) (a b c d t : ℝ) :
    (if a ≤ t ∧ t < b ∧ c ≤ t ∧ t < d then f t else 0) =
      (if t < min b d then f t else 0) -
      (if t < min (min b d) (max a c) then f t else 0) := by
  simp only [lt_min_iff, lt_max_iff]
  by_cases ha : a ≤ t
  · by_cases hc : c ≤ t
    · simp [ha, hc, not_lt.mpr ha, not_lt.mpr hc]
    · simp only [hc, false_and, and_false, ite_false]
      have ht := lt_of_not_ge hc
      simp [ht]
  · simp only [ha, false_and, ite_false]
    have ht := lt_of_not_ge ha
    simp [ht]

 

theorem area_window_energy_identity {Z : Type*} [MeasurableSpace Z]
    {ν : Measure Z} [IsFiniteMeasure ν]
    {f : ℝ × Z → ℝ} (hfm : Measurable f)
    {σ τ : Z → ℝ≥0} (hσm : Measurable σ) (hτm : Measurable τ)
    (T : ℝ≥0) (hτ : ∀ z, τ z ≤ T)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ t z, |f (t,z)| ≤ K) :
    (∫ p : Z × Z, ((∫ t in (0 : ℝ)..(min (τ p.1) (τ p.2) : ℝ≥0),
        f (t,p.1) * f (t,p.2)) - ∫ t in (0 : ℝ)..
          (min (min (τ p.1) (τ p.2)) (max (σ p.1) (σ p.2)) : ℝ≥0), f (t,p.1) * f (t,p.2)) ∂(ν.prod ν)) =
      ∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if (σ z : ℝ) ≤ t ∧ t < (τ z : ℝ) then f (t,z) else 0 ∂ν)^2 := by
  let g (p : ℝ × (Z × Z)) := if (σ p.2.1 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2.1 : ℝ) ∧
      (σ p.2.2 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2.2 : ℝ) then f (p.1,p.2.1) * f (p.1,p.2.2) else 0
  have htm (v : Z → ℝ≥0) (hv : Measurable v) : Measurable (fun z => (v z : ℝ)) :=
    NNReal.continuous_coe.measurable.comp hv
  have hgm : Measurable g :=
    ((hfm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hfm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).ite
        ((measurableSet_le ((htm σ hσm).comp (measurable_fst.comp measurable_snd)) measurable_fst).inter
          ((measurableSet_lt measurable_fst ((htm τ hτm).comp (measurable_fst.comp measurable_snd))).inter
            ((measurableSet_le ((htm σ hσm).comp (measurable_snd.comp measurable_snd)) measurable_fst).inter
              (measurableSet_lt measurable_fst ((htm τ hτm).comp (measurable_snd.comp measurable_snd)))))) measurable_const
  have hgb (p : ℝ × (Z × Z)) : ‖g p‖ ≤ K^2 := by
    rw [Real.norm_eq_abs]
    dsimp only [g]
    split_ifs
    · rw [abs_mul, pow_two]
      exact mul_le_mul (hb _ _) (hb _ _) (abs_nonneg _) hK
    · simpa using sq_nonneg K
  have hgi : Integrable g ((volume.restrict (Ioc 0 (T : ℝ))).prod (ν.prod ν)) :=
    Integrable.of_bound hgm.aestronglyMeasurable (K^2) (Eventually.of_forall hgb)
  have hp (p : Z × Z) : ((∫ t in (0 : ℝ)..(min (τ p.1) (τ p.2) : ℝ≥0),
      f (t,p.1) * f (t,p.2)) - ∫ t in (0 : ℝ)..
        (min (min (τ p.1) (τ p.2)) (max (σ p.1) (σ p.2)) : ℝ≥0), f (t,p.1) * f (t,p.2)) =
        ∫ t in Ioc (0 : ℝ) T, g (t,p) := by
    let H := min (τ p.1) (τ p.2)
    let L := min H (max (σ p.1) (σ p.2))
    have hHT : H ≤ T := (min_le_left _ _).trans (hτ p.1)
    have hLT : L ≤ T := (min_le_left _ _).trans hHT
    have hi (S : ℝ≥0) : IntervalIntegrable
        (fun t : ℝ => if t < (S : ℝ) then f (t,p.1) * f (t,p.2) else 0) volume 0 T := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le T.coe_nonneg).mpr
      apply Integrable.of_bound (μ := volume.restrict (Icc (0 : ℝ) T)) ?_ (K^2) ?_
      · exact (((hfm.comp (measurable_id.prodMk measurable_const)).mul
          (hfm.comp (measurable_id.prodMk measurable_const))).ite
            (measurableSet_lt measurable_id measurable_const) measurable_const).aestronglyMeasurable
      · apply Eventually.of_forall
        intro t
        rw [Real.norm_eq_abs]
        split_ifs
        · rw [abs_mul, pow_two]
          exact mul_le_mul (hb _ _) (hb _ _) (abs_nonneg _) hK
        · simpa using sq_nonneg K
    rw [← interval_integral_prefix_lt hHT, ← interval_integral_prefix_lt hLT,
      ← intervalIntegral.integral_sub (hi H) (hi L), ← intervalIntegral.integral_of_le T.coe_nonneg]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [g, H, L]
    simpa only [NNReal.coe_min, NNReal.coe_max] using
      (real_window_pair_eq (fun t => f (t,p.1) * f (t,p.2)) (σ p.1) (τ p.1) (σ p.2) (τ p.2) t).symm
  have hg (t : ℝ) : (∫ p : Z × Z, g (t,p) ∂(ν.prod ν)) =
      (∫ z, if (σ z : ℝ) ≤ t ∧ t < (τ z : ℝ) then f (t,z) else 0 ∂ν)^2 := by
    calc
      _ = ∫ p : Z × Z,
          (if (σ p.1 : ℝ) ≤ t ∧ t < (τ p.1 : ℝ) then f (t,p.1) else 0) *
          (if (σ p.2 : ℝ) ≤ t ∧ t < (τ p.2 : ℝ) then f (t,p.2) else 0) ∂(ν.prod ν) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro p
        dsimp only [g]
        split_ifs <;> simp_all
      _ = _ := by
        simpa only [pow_two] using (integral_prod_mul (μ := ν) (ν := ν)
          (fun z => if (σ z : ℝ) ≤ t ∧ t < (τ z : ℝ) then f (t,z) else 0)
          (fun z => if (σ z : ℝ) ≤ t ∧ t < (τ z : ℝ) then f (t,z) else 0))
  simp_rw [hp]
  rw [← integral_integral_swap hgi]
  simp only [hg, intervalIntegral.integral_of_le T.coe_nonneg]

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StochasticFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stochastic Fubini for chordal SLE. -/

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
namespace SLEExactGauge
open BrownianPredictable BrownianField
theorem clipped_spatial_green_window_exponential
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ lo hi : ℝ) (hle : lo ≤ hi) (hκ : 0 < κ) (hκ8 : κ < 8)
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q)
    (R : ℝ) (hR : 0 ≤ R) (T : ℝ≥0)
    (σ τ : Z × Ω → ℝ≥0) (hσm : Measurable σ) (hτm : Measurable τ)
    (hστ : ∀ p, σ p ≤ τ p)
    (hσa : ∀ t : ℝ≥0, @MeasurableSet (Z × Ω)
      (mZ.prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) t))
      {p | t < σ p})
    (hσs : ∀ z, IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (σ (z, ω) : WithTop ℝ≥0)))
    (hτa : ∀ t : ℝ≥0, @MeasurableSet (Z × Ω)
      (mZ.prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) t))
      {p | t < τ p})
    (hτs : ∀ z, IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (τ (z, ω) : WithTop ℝ≥0)))
    (hτb : ∀ z ω, τ (z,ω) ≤ T)
    (hinside : ∀ z ω t, t ≤ τ (z,ω) →
      ‖((c (q z)).Q t ω, B t ω)‖ ≤ R ∧
        lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi)
    (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * (∫ z, greenLogDensity κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) -
        greenLogDensity κ ((c (q z)).Q (σ (z,ω)) ω) (B (σ (z,ω)) ω) ∂ν) -
      θ^2 * (∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
          greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2) / 2)) ∂P) ≤ 1 := by
  classical
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_green_field κ R hR
  let ψ := spatialPartial φ 1
  have hψc : Continuous ψ := (spatialPartial_smooth φ hφ 1).continuous
  obtain ⟨K, hK, _⟩ := compact_smooth_bounded_lipschitz ψ
    (spatialPartial_smooth φ hφ 1) (spatialPartial_compact φ hφc 1)
  have hψeq (q' : ℂ × ℝ) (x : ℝ) (hb : ‖(q',x)‖ ≤ R) :
      ψ (q',x) = greenLogCoefficient κ q' x := by
    rw [show ψ (q',x) = deriv (fun y => φ (q',y)) x by
      simp only [ψ, spatialPartial_eq_iteratedDeriv φ hφ, iteratedDeriv_one]]
    rw [deriv_fiber_fderiv φ (hφ.differentiable (by simp)), hφD q' x hb,
      ← deriv_fiber_fderiv _ ((greenLogDensity_contDiff κ).differentiable (by simp))]
    exact (greenLogDensity_spatial_derivative κ q' x).deriv
  let F (p : ℝ × (Z × Ω)) := ψ ((c (q p.2.1)).Q p.1.toNNReal p.2.2, B p.1.toNNReal p.2.2)
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hBc hm
  have hQm := clipped_family_joint_measurable c
  have hFm : Measurable F := hψc.measurable.comp
    ((hQm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      ((hq.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))).prodMk
    (hBm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))))
  have hFc (z : Z) (ω : Ω) : Continuous (fun t : ℝ => F (t,(z,ω))) :=
    hψc.comp ((((c (q z)).lipschitz ω).continuous.comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)).prodMk
      ((hBc ω).comp continuous_real_toNNReal))
  have hFb (t : ℝ) (z : Z) (ω : Ω) : |F (t,(z,ω))| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK ((c (q z)).Q t.toNNReal ω, B t.toNNReal ω)
  let C (n i : ℕ) (p : Z × Ω) := if σ p ≤ dyadicTime T n i ∧ dyadicTime T n i < τ p then
    F (dyadicTime T n i,p) else 0
  have hCa (n i : ℕ) : @Measurable (Z × Ω) ℝ
      (mZ.prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) (dyadicTime T n i)))
      (borel ℝ) (C n i) := by
    have hQ := clipped_family_past_measurable c (dyadicTime T n i)
    have hBa := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted (dyadicTime T n i)
    let : MeasurableSpace Ω := Filtration.natural B (fun s => (hm s).stronglyMeasurable) (dyadicTime T n i)
    have hh := hψc.measurable.comp
      ((hQ.comp ((hq.comp measurable_fst).prodMk measurable_snd)).prodMk (hBa.comp measurable_snd))
    change Measurable (C n i)
    dsimp only [C, F]
    simp only [Real.toNNReal_coe]
    have hsa : MeasurableSet {p : Z × Ω | σ p ≤ dyadicTime T n i} := by
      simpa only [Set.compl_ofPred, not_lt] using (hσa (dyadicTime T n i)).compl
    exact hh.ite (hsa.inter (hτa (dyadicTime T n i))) measurable_const
  have hCm (n i : ℕ) : Measurable (C n i) :=
    (hCa n i).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (Filtration.le _ _))) le_rfl
  have hCb (n i : ℕ) (z : Z) (ω : Ω) : |C n i (z,ω)| ≤ K := by
    dsimp only [C]
    split_ifs
    · exact hFb _ _ _
    · simp
  let Y (p : Z × Ω) := greenLogDensity κ ((c (q p.1)).Q (τ p) p.2) (B (τ p) p.2) -
    greenLogDensity κ ((c (q p.1)).Q (σ p) p.2) (B (σ p) p.2)
  have hYm : Measurable Y :=
    (((greenLogDensity_contDiff κ).continuous.measurable.comp
      ((hQm.comp (hτm.prodMk ((hq.comp measurable_fst).prodMk measurable_snd))).prodMk
        (hBm.comp (hτm.prodMk measurable_snd))))).sub
      ((greenLogDensity_contDiff κ).continuous.measurable.comp
        ((hQm.comp (hσm.prodMk ((hq.comp measurable_fst).prodMk measurable_snd))).prodMk
          (hBm.comp (hσm.prodMk measurable_snd))))
  have hlim (z : Z) : ∀ᵐ ω ∂P, Tendsto
      (fun n => driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (z,ω)) (2^n) ω)
      atTop (𝓝 (Y (z,ω))) := by
    have hτlim := (c (q z)).stopped_green_ito hB hBc hκ hκ8 R hR T
      (fun ω => τ (z,ω)) (hτs z) (hτb z) (hinside z)
    have hσlim := (c (q z)).stopped_green_ito hB hBc hκ hκ8 R hR T
      (fun ω => σ (z,ω)) (hσs z) (fun ω => (hστ (z,ω)).trans (hτb z ω))
      (fun ω t ht => hinside z ω t (ht.trans (hστ (z,ω))))
    filter_upwards [hτlim, hσlim] with ω hτl hσl
    have he (n i : ℕ) : C n i (z,ω) =
        (if dyadicTime T n i < τ (z,ω) then
          greenLogCoefficient κ ((c (q z)).Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0) -
        (if dyadicTime T n i < σ (z,ω) then
          greenLogCoefficient κ ((c (q z)).Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0) := by
      dsimp only [C, F]
      rw [Real.toNNReal_coe]
      by_cases ht : dyadicTime T n i < τ (z,ω)
      · rw [hψeq _ _ (hinside z ω _ ht.le).1]
        by_cases hs : σ (z,ω) ≤ dyadicTime T n i
        · simp [ht, hs, not_lt.mpr hs]
        · simp [ht, hs, lt_of_not_ge hs]
      · have hs : ¬ dyadicTime T n i < σ (z,ω) := fun h => ht (h.trans_le (hστ (z,ω)))
        simp [ht, hs]
    have hs (n : ℕ) : driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (z,ω)) (2^n) ω =
        (∑ i ∈ Finset.range (2^n),
          (if dyadicTime T n i < τ (z,ω) then
            greenLogCoefficient κ ((c (q z)).Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0) *
            (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)) -
        (∑ i ∈ Finset.range (2^n),
          (if dyadicTime T n i < σ (z,ω) then
            greenLogCoefficient κ ((c (q z)).Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0) *
            (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)) := by
      simp only [driverPredictableSum, he, sub_mul, Finset.sum_sub_distrib]
    simpa only [hs, Y, sub_sub_sub_cancel_right] using hτl.sub hσl
  let Q (ω : Ω) := ∫ t in (0 : ℝ)..(T : ℝ),
    (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then F (t,(z,ω)) else 0 ∂ν)^2
  have hE : ∀ᵐ ω ∂P, Tendsto (fun n => driverPredictableEnergy (dyadicTime T n)
      (fun i ω => ∫ z, C n i (z,ω) ∂ν) (2^n) ω) atTop (𝓝 (Q ω)) := by
    apply Eventually.of_forall
    intro ω
    have hfm : Measurable (fun p : ℝ × Z => F (p.1,(p.2,ω))) :=
      hFm.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
    have hsm := hσm.comp (measurable_id.prodMk (measurable_const (a := ω)))
    have htm := hτm.comp (measurable_id.prodMk (measurable_const (a := ω)))
    have hh := area_window_pair_energy_tendsto (ν := ν) hfm (fun z => hFc z ω) hsm htm T
      (fun z => hτb z ω) K K.coe_nonneg (fun t z => hFb t z ω)
    rw [area_window_energy_identity hfm hsm htm T (fun z => hτb z ω) K K.coe_nonneg
      (fun t z => hFb t z ω)] at hh
    simpa only [driverPredictableEnergy, dyadicTime_step, C, areaWindowSample, Q, Function.comp_def, id_eq] using hh
  have hh := brownian_area_exponential_limit hB hm T C hCm hCa K K.coe_nonneg hCb Y hYm hlim Q hE θ
  have hQeq (ω : Ω) : Q ω = ∫ t in (0 : ℝ)..(T : ℝ),
      (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
        greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le T.coe_nonneg] at ht
    dsimp only []
    apply congrArg (fun x : ℝ => x^2)
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only []
    split_ifs with htτ
    · have htn : t.toNNReal ≤ τ (z,ω) := Real.toNNReal_le_iff_le_coe.mpr htτ.2.le
      dsimp only [F]
      have he := hψeq _ _ (hinside z ω _ htn).1
      simpa only [Real.coe_toNNReal _ ht.1] using he
    · rfl
  simpa only [Y, hQeq] using hh

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma greenLogCoefficient_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (κ b : ℝ) (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t)
    (hUb : U t = Real.sqrt κ * b) :
    greenLogCoefficient κ (logLoewnerCoordinates G z t) b =
      greenBrownianCoefficient κ U γ G t z := by
  rw [greenLogCoefficient, greenLogDensity_logCoordinates hU h κ b z t hz hUb,
    greenLogNormSq_logCoordinates κ b G z t (h.imag_positive t z hz),
    logCoordinates_re, Complex.normSq_eq_norm_sq, greenBrownianCoefficient, hUb]
  simp only [Complex.sub_re, Complex.ofReal_re]
  ring

lemma clipped_chart_identification
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (ω : Ω) (τ : ℝ≥0)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (hin : ∀ t : ℝ≥0, t ≤ τ →
      lo ≤ ((c (initialLogCoordinates z)).Q t ω).1.im ∧
        ((c (initialLogCoordinates z)).Q t ω).1.im ≤ hi) :
    z ∈ survivingDomain γ τ ∧ ∀ t : ℝ≥0, t ≤ τ →
      (c (initialLogCoordinates z)).Q t ω = logLoewnerCoordinates G z t := by
  let d := c (initialLogCoordinates z)
  have hd (s : ℝ) (hs : s ∈ Icc 0 (τ : ℝ)) := (d.derivative ω s hs.1).mono
    (show Icc (0 : ℝ) (τ : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
  have hb (s : ℝ) (hs : s ∈ Icc 0 (τ : ℝ)) : (d.Q s ω).1.im ∈ Icc lo hi := by
    have hh := hin s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)
    simpa only [Set.mem_Icc, Real.coe_toNNReal _ hs.1] using hh
  obtain ⟨hl, he⟩ := clipped_log_identification ((hBc ω).const_mul _) hw z hz τ
    lo hi hle (fun s => d.Q s ω) (d.initial ω) hd hb
  exact ⟨hl, fun t ht => by simpa only [Real.toNNReal_coe] using he ⟨t.coe_nonneg, ht⟩⟩

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
end
end
end
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


end

end OAI
end

section
-- module Solutions.OAIQ27_SLE.SLE_StoppedFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopped Fields for chordal SLE. -/

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
namespace SLEExactGauge
lemma boundedSpatialHit_antitone_radius {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) {ε r : ℝ} (hεr : ε ≤ r) (hs : r ≤ dist (γ 0) z) (T : ℝ≥0) :
    boundedSpatialHit γ z r T ≤ boundedSpatialHit γ z ε T := by
  apply WithTop.coe_le_coe.mp
  rw [boundedSpatialHit_coe, boundedSpatialHit_coe]
  exact min_le_min (spatialHitTime_antitone_radius hc z hεr hs) le_rfl

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

lemma joint_spatialHit_stopping {Z : Type*} [mZ : MeasurableSpace Z]
    (z : Z → ℂ) (hz : Measurable z) (r : ℝ) :
    IsStoppingTime (spatialFiltration (Z := Z) a.filtration)
      (fun p : Z × a.samples => spatialHitTime (γ p.2) (z p.1) r) := by
  let H (t : ℝ≥0) (p : Z × a.samples) := dist (γ p.2 t) (z p.1) - r
  have ha : Adapted (spatialFiltration (Z := Z) a.filtration) H := by
    intro t
    have hm := a.trace_adapted t
    let : MeasurableSpace a.samples := a.filtration t
    exact ((hm.comp measurable_snd).dist (hz.comp measurable_fst)).sub_const r
  have hc (p : Z × a.samples) : Continuous (fun t => H t p) :=
    ((a.trace_continuous p.2).dist continuous_const).sub continuous_const
  exact continuous_zero_hit_stopping (spatialFiltration (Z := Z) a.filtration) H ha hc 0

lemma joint_boundedSpatialHit_stopping {Z : Type*} [mZ : MeasurableSpace Z]
    (z : Z → ℂ) (hz : Measurable z) (r : ℝ) (T : ℝ≥0) :
    IsStoppingTime (spatialFiltration (Z := Z) a.filtration)
      (fun p : Z × a.samples => (boundedSpatialHit (γ p.2) (z p.1) r T : WithTop ℝ≥0)) := by
  simpa only [boundedSpatialHit_coe] using (a.joint_spatialHit_stopping z hz r).min_const T

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma clipped_spatial_window_coefficient_le
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (ω : Ω) (α S : ℝ≥0)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (hin : ∀ t : ℝ≥0, t ≤ α → lo ≤ ((c (initialLogCoordinates z)).Q t ω).1.im ∧
        ((c (initialLogCoordinates z)).Q t ω).1.im ≤ hi)
    (r ε : ℝ) (t : ℝ≥0) :
    |(if min (boundedSpatialHit γ z r S) α ≤ t ∧
        t < min (boundedSpatialHit γ z ε S) α then
      greenLogCoefficient κ ((c (initialLogCoordinates z)).Q t ω) (B t ω) else 0)| ≤
    |spatialSlabCoefficient κ (fun s => Real.sqrt κ * B s ω) γ G r ε t z| := by
  split_ifs with ht
  · have hta : t < α := ht.2.trans_le (min_le_right _ _)
    have hte : t < boundedSpatialHit γ z ε S := ht.2.trans_le (min_le_left _ _)
    have htS : t < S := by
      apply WithTop.coe_lt_coe.mp
      exact (WithTop.coe_lt_coe.mpr hte).trans_le
        (by rw [boundedSpatialHit_coe]; exact min_le_right _ _)
    have hsr : boundedSpatialHit γ z r S ≤ t := (min_le_iff.mp ht.1).resolve_right (not_le_of_gt hta)
    have hr : spatialHitTime γ z r ≤ t := by
      have hh := WithTop.coe_le_coe.mpr hsr
      rw [boundedSpatialHit_coe] at hh
      exact (min_le_iff.mp hh).resolve_right (not_le_of_gt (WithTop.coe_lt_coe.mpr htS))
    have he : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z ε :=
      (WithTop.coe_le_coe.mpr hte.le).trans (boundedSpatialHit_le γ z ε S)
    obtain ⟨hl, hq⟩ := clipped_chart_identification c hBc z hz ω α γ G F hw hin
    have hlive := survivingDomain_antitone γ hta.le hl
    rw [hq t hta.le, greenLogCoefficient_logCoordinates ((hBc ω).const_mul _) hw κ _ z t hlive rfl,
      spatialSlabCoefficient, ite_eq_left ⟨hr, he, hlive⟩]
  · simpa only [abs_zero] using abs_nonneg (spatialSlabCoefficient κ (fun s => Real.sqrt κ * B s ω) γ G r ε t z)

 

theorem IsCapacityTwoWitness.spatial_masked_bracket_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hheight : ∀ z ∈ A, ε ≤ z.im)
    (b : ℝ → A → ℝ)
    (hb : ∀ t, 0 ≤ t → ∀ z, |b t z| ≤
      |spatialSlabCoefficient κ U γ G r ε t.toNNReal z|) :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal
      ((∫ z, b t z ∂(volume.comap (Subtype.val : A → ℂ))) ^ 2)) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A)) := by
  apply le_trans _ (h.spatial_slab_absolute_bracket_bound hU hκ hκ4 hε hr A hA hheight)
  apply setLIntegral_mono' measurableSet_Ici
  intro t ht
  apply (spatial_integral_square_le (volume.comap (Subtype.val : A → ℂ)) (b t)).trans
  apply pow_le_pow_left₀ bot_le
  calc
    _ ≤ ∫⁻ z : A, ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z|
        ∂(volume.comap (Subtype.val : A → ℂ)) := lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hb t ht z)
    _ = _ := lintegral_subtype_comap (μ := (volume : Measure ℂ)) hA (fun z : ℂ => ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z|)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

lemma clipped_family_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q) :
    ∃ L : ℝ≥0, ∀ (q : ℂ × ℝ) (ω : Ω) (t : ℝ≥0),
      ‖(c q).Q t ω‖ ≤ ‖q‖ + L * t := by
  obtain ⟨L, K, hb, hK⟩ := clippedLogLoewnerField_bounds lo hi hle
  refine ⟨L, fun q ω t => ?_⟩
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => (c q).Q s ω) (a := (0 : ℝ)) (b := (t : ℝ))
    (f' := fun s => clippedLogLoewnerField lo hi hle (Real.sqrt κ * B s.toNNReal ω) ((c q).Q s ω))
    (fun s hs => ((c q).derivative ω s hs.1).mono (fun _ hx => hx.1))
    (fun s hs => hb _ _) (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
  rw [(c q).initial, sub_zero] at hh
  calc
    _ ≤ ‖q‖ + ‖(c q).Q t ω - q‖ := by
      simpa only [add_comm] using norm_le_insert' ((c q).Q t ω) q
    _ ≤ _ := by linarith

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem spatial_angular_cutoff
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ lo hi : ℝ) (hle : lo ≤ hi)
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q) (hq0 : ∀ z, (q z).2 = 0)
    (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε)
    (hε0 : ∀ z, ε ≤ logAngleSq κ (q z) 0)
    (hlo : ∀ z, lo < (q z).1.im - u / (2 * ε)) (hhi : ∀ z, (q z).1.im < hi)
    (T : ℝ≥0) (hT : ∀ z, u < (4 * ε ^ 2 / Real.exp (2 * (q z).1.im)) * T) :
    ∃ τ : Z × Ω → ℝ≥0,
      IsStoppingTime (spatialFiltration (Z := Z)
        (Filtration.natural B (fun t => (hm t).stronglyMeasurable)))
        (fun p => (τ p : WithTop ℝ≥0)) ∧
      (∀ z ω, τ (z,ω) < T) ∧
      (∀ z ω t, t ≤ τ (z,ω) →
        logRadiusClock (q z).1.im ((c (q z)).Q t ω) ≤ u ∧
        ε ≤ logAngleSq κ ((c (q z)).Q t ω) (B t ω) ∧
        lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi) ∧
      (∀ z ω t, t < τ (z,ω) →
        logRadiusClock (q z).1.im ((c (q z)).Q t ω) < u ∧
        ε < logAngleSq κ ((c (q z)).Q t ω) (B t ω) ∧
        lo < ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im < hi) ∧
      (∀ z ω, logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) = u ∨
        logAngleSq κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) = ε) := by
  let f := spatialFiltration (Z := Z) (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
  let D (t : ℝ≥0) (p : Z × Ω) :=
    min (u - logRadiusClock (q p.1).1.im ((c (q p.1)).Q t p.2))
      (min (logAngleSq κ ((c (q p.1)).Q t p.2) (B t p.2) - ε)
        (min (((c (q p.1)).Q t p.2).1.im - lo) (hi - ((c (q p.1)).Q t p.2).1.im)))
  have hDa : Adapted f D := by
    intro t
    have hQ := clipped_family_past_measurable c t
    have hBa := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted t
    let : MeasurableSpace Ω := Filtration.natural B (fun s => (hm s).stronglyMeasurable) t
    have hc := hQ.comp ((hq.comp measurable_fst).prodMk measurable_snd)
    have hBb := hBa.comp (@measurable_snd Z Ω mZ _)
    have hη := Complex.continuous_im.measurable.comp (hq.comp (@measurable_fst Z Ω mZ (Filtration.natural B (fun s => (hm s).stronglyMeasurable) t))).fst
    have hclock := (hη.sub (Complex.continuous_im.measurable.comp hc.fst)).add hc.snd
    exact (measurable_const.sub hclock).min
      ((((continuous_logAngleSq κ).measurable.comp (hc.prodMk hBb)).sub_const ε).min
        (((Complex.continuous_im.measurable.comp hc.fst).sub_const lo).min
          (measurable_const.sub (Complex.continuous_im.measurable.comp hc.fst))))
  have hDc (p : Z × Ω) : Continuous (fun t => D t p) := by
    have hc := ((c (q p.1)).lipschitz p.2).continuous.comp NNReal.continuous_coe
    exact (continuous_const.sub ((continuous_const.sub (Complex.continuous_im.comp hc.fst)).add hc.snd)).min
      ((((continuous_logAngleSq κ).comp (hc.prodMk (hBc p.2))).sub continuous_const).min
        (((Complex.continuous_im.comp hc.fst).sub continuous_const).min
          (continuous_const.sub (Complex.continuous_im.comp hc.fst))))
  have hD0 (p : Z × Ω) : 0 ≤ D 0 p := by
    dsimp only [D]
    rw [NNReal.coe_zero, (c (q p.1)).initial, hB0]
    simp only [le_min_iff, sub_nonneg]
    refine ⟨?_, hε0 p.1, ?_, (hhi p.1).le⟩
    · simpa only [logRadiusClock, sub_self, zero_add, hq0] using hu
    · have hd : 0 ≤ u / (2 * ε) := div_nonneg hu (by positivity)
      linarith [hlo p.1]
  obtain ⟨τ, hτ, hb, hleD, hltD, hzero⟩ := first_margin_stopping f D hDa hDc hD0 T
  have hin (z : Z) (ω : Ω) (t : ℝ≥0) (ht : t ≤ τ (z,ω)) :
      logRadiusClock (q z).1.im ((c (q z)).Q t ω) ≤ u ∧
      ε ≤ logAngleSq κ ((c (q z)).Q t ω) (B t ω) ∧
      lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi :=
    by simpa only [D, le_min_iff, sub_nonneg] using hleD (z,ω) t ht
  have hg (z : Z) (ω : Ω) :
      ((c (q z)).Q (τ (z,ω)) ω).1.im ≤ (q z).1.im ∧
      (q z).1.im - logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) / (2 * ε) ≤ ((c (q z)).Q (τ (z,ω)) ω).1.im ∧
      (4 * ε ^ 2 / Real.exp (2 * (q z).1.im)) * τ (z,ω) ≤ logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) := by
    have hd (s : ℝ) (hs : s ∈ Icc 0 (τ (z,ω) : ℝ)) :
        HasDerivWithinAt (fun t => (c (q z)).Q t ω)
          (physicalLogLoewnerField (Real.sqrt κ * B s.toNNReal ω) ((c (q z)).Q s ω))
          (Icc 0 (τ (z,ω) : ℝ)) s := by
      have hst : s.toNNReal ≤ τ (z,ω) := Real.toNNReal_le_iff_le_coe.mpr hs.2
      have hbounds := (hin z ω s.toNNReal hst).2.2
      rw [Real.coe_toNNReal _ hs.1] at hbounds
      have hh := ((c (q z)).derivative ω s hs.1).mono (show Icc (0 : ℝ) (τ (z,ω) : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
      rwa [clippedLogLoewnerField_eq_physical lo hi hle _ _ ⟨hbounds.1, hbounds.2⟩] at hh
    have ha (s : ℝ) (hs : s ∈ Icc 0 (τ (z,ω) : ℝ)) :
        ε ≤ logAngleSq κ ((c (q z)).Q s ω) (B s.toNNReal ω) := by
      have hh := (hin z ω s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)).2.1
      simpa only [Real.coe_toNNReal _ hs.1] using hh
    have hq : ((c (q z)).Q 0 ω).2 = 0 := by rw [(c (q z)).initial ω, hq0 z]
    have hh := log_loewner_height_clock_bounds (τ (z,ω)).coe_nonneg hε hq hd ha
    simpa only [(c (q z)).initial ω] using hh
  have hτlt (z : Z) (ω : Ω) : τ (z,ω) < T := by
    by_contra hn
    have he : τ (z,ω) = T := le_antisymm (hb (z,ω)) (not_lt.mp hn)
    have hh := (hg z ω).2.2.trans (hin z ω (τ (z,ω)) le_rfl).1
    rw [he] at hh
    exact (not_le_of_gt (hT z)) hh
  have he (z : Z) (ω : Ω) :
      logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) = u ∨
      logAngleSq κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) = ε := by
    obtain ⟨hr, ha, hl, hh⟩ := hin z ω (τ (z,ω)) le_rfl
    have hstrictlo : lo < ((c (q z)).Q (τ (z,ω)) ω).1.im := by
      have hdiv := div_le_div_of_nonneg_right hr (show 0 ≤ 2 * ε by positivity)
      linarith [(hg z ω).2.1, hlo z]
    have hstricthi : ((c (q z)).Q (τ (z,ω)) ω).1.im < hi := (hg z ω).1.trans_lt (hhi z)
    by_contra hn
    push Not at hn
    have hp : 0 < D (τ (z,ω)) (z,ω) :=
      by simpa only [D, lt_min_iff, sub_pos] using
        (show logRadiusClock (q z).1.im ((c (q z)).Q (τ (z,ω)) ω) < u ∧
          ε < logAngleSq κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) ∧
          lo < ((c (q z)).Q (τ (z,ω)) ω).1.im ∧
          ((c (q z)).Q (τ (z,ω)) ω).1.im < hi from
          ⟨lt_of_le_of_ne hr hn.1, lt_of_le_of_ne ha (Ne.symm hn.2), hstrictlo, hstricthi⟩)
    rw [hzero (z,ω) (hτlt z ω)] at hp
    exact lt_irrefl 0 hp
  refine ⟨τ, hτ, hτlt, hin, ?_, he⟩
  intro z ω t ht
  simpa only [D, lt_min_iff, sub_pos] using hltD (z,ω) t ht

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge



lemma exists_spatial_angular_family
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (z : Z → ℂ) (hz : Measurable z)
    (l h : ℝ) (hlh : l ≤ h)
    (hη : ∀ x, l ≤ Real.log (z x).im ∧ Real.log (z x).im ≤ h)
    (u ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε)
    (hangle : ∀ x, ε ≤ logAngleSq κ (initialLogCoordinates (z x)) 0) :
    Nonempty (SpatialAngularFamily B hm κ z u ε) := by
  classical
  let lo := l - u / (2 * ε) - 1
  let hi := h + 1
  have hud : 0 ≤ u / (2 * ε) := div_nonneg hu (by positivity)
  have hle : lo ≤ hi := by dsimp [lo, hi]; linarith
  let c (q : ℂ × ℝ) : ClippedLogSolution B hm κ lo hi hle q :=
    (exists_clippedLogSolution B hm hBm hBc κ lo hi hle q).some
  let v := 4 * ε ^ 2 / Real.exp (2 * h)
  have hv : 0 < v := by dsimp [v]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (u / v)
  have hT : ∀ x, u < (4 * ε ^ 2 / Real.exp (2 * (initialLogCoordinates (z x)).1.im)) * ((N : ℝ≥0) : ℝ) := by
    intro x
    have huv := (div_lt_iff₀ hv).mp hN
    have he : Real.exp (2 * Real.log (z x).im) ≤ Real.exp (2 * h) :=
      Real.exp_le_exp.mpr (by linarith [(hη x).2])
    have hd : v ≤ 4 * ε ^ 2 / Real.exp (2 * Real.log (z x).im) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) he
    rw [initialLogCoordinates_im, NNReal.coe_natCast]
    have huv' : u < v * (N : ℝ) := by simpa only [mul_comm (N : ℝ) v] using huv
    exact huv'.trans_le (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg N))
  have hq : Measurable (fun x => initialLogCoordinates (z x)) :=
    measurable_initialLogCoordinates.comp hz
  obtain ⟨τ, hτ, hb, hin, hbefore, hboundary⟩ := spatial_angular_cutoff hm hBc hB0 κ lo hi hle c
    (fun x => initialLogCoordinates (z x)) hq (fun x => rfl) u ε hu hε hangle
    (fun x => by rw [initialLogCoordinates_im]; dsimp [lo]; linarith [(hη x).1])
    (fun x => by rw [initialLogCoordinates_im]; dsimp [hi]; linarith [(hη x).2]) (N : ℝ≥0) hT
  refine ⟨⟨lo, hi, hle, c, N, τ, hτ, fun p => (hb p.1 p.2).le, ?_, ?_, ?_⟩⟩
  · simpa only [initialLogCoordinates_im] using hin
  · intro x ω t ht
    constructor
    · simpa only [initialLogCoordinates_im] using (hbefore x ω t ht).1
    · exact (hbefore x ω t ht).2.1
  · simpa only [initialLogCoordinates_im] using hboundary

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma clipped_area_window_measurable
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (ν : Measure Z) [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q)
    (σ τ : Z × Ω → ℝ≥0) (hσ : Measurable σ) (hτ : Measurable τ) (T : ℝ≥0) :
    Measurable (fun ω => ∫ z, greenLogDensity κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) -
        greenLogDensity κ ((c (q z)).Q (σ (z,ω)) ω) (B (σ (z,ω)) ω) ∂ν) ∧
    Measurable (fun ω => ∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
          greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2) := by
  classical
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hBc hm
  have hQm := clipped_family_joint_measurable c
  have hD (η : Z × Ω → ℝ≥0) (hη : Measurable η) : Measurable (fun p : Z × Ω =>
      greenLogDensity κ ((c (q p.1)).Q (η p) p.2) (B (η p) p.2)) :=
    (greenLogDensity_contDiff κ).continuous.measurable.comp
      ((hQm.comp (hη.prodMk ((hq.comp measurable_fst).prodMk measurable_snd))).prodMk
        (hBm.comp (hη.prodMk measurable_snd)))
  refine ⟨((hD τ hτ).sub (hD σ hσ)).stronglyMeasurable.integral_prod_left'.measurable, ?_⟩
  let f (p : ℝ × (Z × Ω)) := if (σ p.2 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2 : ℝ) then
    greenLogCoefficient κ ((c (q p.2.1)).Q p.1 p.2.2) (B p.1.toNNReal p.2.2) else 0
  have hgood : MeasurableSet {p : ℝ × (Z × Ω) | (σ p.2 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2 : ℝ)} :=
    (measurableSet_le (NNReal.continuous_coe.measurable.comp (hσ.comp measurable_snd)) measurable_fst).inter
      (measurableSet_lt measurable_fst (NNReal.continuous_coe.measurable.comp (hτ.comp measurable_snd)))
  have hQreal : Measurable (fun p : ℝ × (Z × Ω) => (c (q p.2.1)).Q p.1.toNNReal p.2.2) :=
    hQm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      ((hq.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))
  have hcoef : Measurable (fun p : (ℂ × ℝ) × ℝ => greenLogCoefficient κ p.1 p.2) := by
    unfold greenLogCoefficient greenLogNormSq
    apply (greenLogDensity_contDiff κ).continuous.measurable.mul
    fun_prop
  have hfm' : Measurable (fun p : ℝ × (Z × Ω) =>
      if (σ p.2 : ℝ) ≤ p.1 ∧ p.1 < (τ p.2 : ℝ) then
        greenLogCoefficient κ ((c (q p.2.1)).Q p.1.toNNReal p.2.2) (B p.1.toNNReal p.2.2) else 0) := (hcoef.comp
    (hQreal.prodMk (hBm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))))).ite hgood (measurable_const (a := (0 : ℝ)))
  have hfm : Measurable f := by
    convert hfm' using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    dsimp only [f]
    split_ifs with hp
    · rw [Real.coe_toNNReal _ ((σ p.2).coe_nonneg.trans hp.1)]
    · rfl
  have hswap : Measurable (fun p : Z × (ℝ × Ω) => f (p.2.1,(p.1,p.2.2))) := hfm.comp
    ((measurable_fst.comp measurable_snd).prodMk (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have harea : Measurable (fun p : ℝ × Ω => ∫ z, f (p.1,(z,p.2)) ∂ν) :=
    hswap.stronglyMeasurable.integral_prod_left'.measurable
  have hh := (harea.pow_const 2).stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Ioc (0 : ℝ) T))
  simpa only [intervalIntegral.integral_of_le T.coe_nonneg, f] using hh.measurable

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma spatial_stopping_lift {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime f τ) :
    IsStoppingTime (spatialFiltration (Z := Z) f) (fun p => τ p.2) := by
  intro t
  let : MeasurableSpace Ω := f t
  exact (hτ t).preimage (measurable_snd : @Measurable (Z × Ω) Ω (mZ.prod (f t)) (f t) Prod.snd)

 

theorem exists_common_brownian_compact_stops
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) (T : ℝ≥0) :
    ∃ π : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
        (fun ω => (π n ω : WithTop ℝ≥0))) ∧
      (∀ n ω, π n ω ≤ T) ∧
      (∀ n ω t, t ≤ π n ω → |B t ω| ≤ (n : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ n in atTop, π n ω = T) := by
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hDa (n : ℕ) : Adapted f (fun t ω => (n : ℝ) + 1 - |B t ω|) := by
    intro t
    have ha := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted t
    let : MeasurableSpace Ω := f t
    exact measurable_const.sub ha.abs
  have hb (n : ℕ) := first_margin_stopping f (fun t ω => (n : ℝ) + 1 - |B t ω|)
    (hDa n) (fun ω => continuous_const.sub (hBc ω).abs)
    (fun ω => by rw [hB0 ω, abs_zero, sub_zero]; positivity) T
  choose π hπ hb hin hpre hat using hb
  refine ⟨π, hπ, hb, fun n ω t ht => (sub_nonneg.mp (hin n ω t ht)), ?_⟩
  intro ω
  obtain ⟨N, hN⟩ := continuous_path_bounded_by_nat (fun t => B t ω) (hBc ω) T
  filter_upwards [eventually_ge_atTop N] with n hn
  apply le_antisymm (hb n ω)
  by_contra h
  have he := hat n ω (not_le.mp h)
  have hh := hN (π n ω) (hb n ω)
  have hn' : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  linarith

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem clipped_spatial_green_window_unbounded_driver
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0)
    (κ lo hi : ℝ) (hle : lo ≤ hi) (hκ : 0 < κ) (hκ8 : κ < 8)
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q)
    (M : ℝ) (hqbound : ∀ z, ‖q z‖ ≤ M) (T : ℝ≥0)
    (σ τ : Z × Ω → ℝ≥0)
    (hσ : IsStoppingTime (spatialFiltration (Z := Z)
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)))
      (fun p => (σ p : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (spatialFiltration (Z := Z)
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)))
      (fun p => (τ p : WithTop ℝ≥0)))
    (hστ : ∀ p, σ p ≤ τ p) (hτb : ∀ p, τ p ≤ T)
    (hinside : ∀ z ω t, t ≤ τ (z,ω) →
      lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi)
    (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * (∫ z, greenLogDensity κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) -
        greenLogDensity κ ((c (q z)).Q (σ (z,ω)) ω) (B (σ (z,ω)) ω) ∂ν) -
      θ^2 * (∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
          greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2) / 2)) ∂P) ≤ 1 := by
  classical
  obtain ⟨π, hπ, hπb, hπin, hπlim⟩ := exists_common_brownian_compact_stops hm hBc hB0 T
  obtain ⟨L, hL⟩ := clipped_family_uniform_bound c
  let σn (n : ℕ) (p : Z × Ω) := min (σ p) (π n p.2)
  let τn (n : ℕ) (p : Z × Ω) := min (τ p) (π n p.2)
  have hσn (n : ℕ) : IsStoppingTime (spatialFiltration (Z := Z)
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)))
      (fun p => (σn n p : WithTop ℝ≥0)) := by
    simpa only [σn, WithTop.coe_min] using hσ.min (spatial_stopping_lift (Z := Z) (hπ n))
  have hτn (n : ℕ) : IsStoppingTime (spatialFiltration (Z := Z)
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)))
      (fun p => (τn n p : WithTop ℝ≥0)) := by
    simpa only [τn, WithTop.coe_min] using hτ.min (spatial_stopping_lift (Z := Z) (hπ n))
  have hstn (n : ℕ) (p : Z × Ω) : σn n p ≤ τn n p := min_le_min (hστ p) le_rfl
  have htn (n : ℕ) (p : Z × Ω) : τn n p ≤ T := (min_le_left _ _).trans (hτb p)
  let R (n : ℕ) := max M 0 + (L : ℝ) * T + ((n : ℝ) + 1)
  have hR (n : ℕ) : 0 ≤ R n := by dsimp [R]; positivity
  have hin (n : ℕ) (z : Z) (ω : Ω) (t : ℝ≥0) (ht : t ≤ τn n (z,ω)) :
      ‖((c (q z)).Q t ω, B t ω)‖ ≤ R n ∧
        lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi := by
    have htτ := ht.trans (min_le_left _ _)
    have htb := ht.trans (htn n (z,ω))
    refine ⟨?_, hinside z ω t htτ⟩
    rw [Prod.norm_def, max_le_iff]
    have hqt := hL (q z) ω t
    have hmul : (L : ℝ) * t ≤ (L : ℝ) * T := mul_le_mul_of_nonneg_left
      (NNReal.coe_le_coe.mpr htb) L.coe_nonneg
    have hbm := hπin n ω t (ht.trans (min_le_right _ _))
    have hml : M ≤ max M 0 := le_max_left _ _
    have hmn : 0 ≤ max M 0 := le_max_right _ _
    have hlt : 0 ≤ (L : ℝ) * T := mul_nonneg L.coe_nonneg T.coe_nonneg
    dsimp only [R]
    exact ⟨by linarith [hqbound z, Nat.cast_nonneg (α := ℝ) n], by simpa only [Real.norm_eq_abs] using
      (show |B t ω| ≤ max M 0 + (L : ℝ) * T + ((n : ℝ) + 1) by linarith)⟩
  let X (η ξ : Z × Ω → ℝ≥0) (ω : Ω) :=
    ∫ z, greenLogDensity κ ((c (q z)).Q (ξ (z,ω)) ω) (B (ξ (z,ω)) ω) -
      greenLogDensity κ ((c (q z)).Q (η (z,ω)) ω) (B (η (z,ω)) ω) ∂ν
  let E (η ξ : Z × Ω → ℝ≥0) (ω : Ω) := ∫ t in (0 : ℝ)..(T : ℝ),
    (∫ z, if (η (z,ω) : ℝ) ≤ t ∧ t < (ξ (z,ω) : ℝ) then
      greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2
  have hxm (n : ℕ) := clipped_area_window_measurable ν hBc c q hq (σn n) (τn n)
    (stopping_time_measurable_nnreal (hσn n)) (stopping_time_measurable_nnreal (hτn n)) T
  have hexp (n : ℕ) := clipped_spatial_green_window_exponential (ν := ν) hm hB hBc
    κ lo hi hle hκ hκ8 c q hq (R n) (hR n) T (σn n) (τn n)
      (stopping_time_measurable_nnreal (hσn n)) (stopping_time_measurable_nnreal (hτn n)) (hstn n)
      (stopping_before_measurable (hσn n)) (spatial_stopping_section (hσn n))
      (stopping_before_measurable (hτn n)) (spatial_stopping_section (hτn n))
      (fun z ω => htn n (z,ω)) (hin n) θ
  have hev (ω : Ω) : ∀ᶠ n in atTop,
      X (σn n) (τn n) ω = X σ τ ω ∧ E (σn n) (τn n) ω = E σ τ ω := by
    filter_upwards [hπlim ω] with n hn
    have hs (z : Z) : σn n (z,ω) = σ (z,ω) := by
      dsimp only [σn]; rw [hn, min_eq_left ((hστ (z,ω)).trans (hτb (z,ω))) ]
    have ht (z : Z) : τn n (z,ω) = τ (z,ω) := by
      dsimp only [τn]; rw [hn, min_eq_left (hτb (z,ω))]
    simp only [X, E, hs, ht, and_self]
  apply compensated_exponential_limit_energy
    (fun n => X (σn n) (τn n)) (fun n => E (σn n) (τn n)) (X σ τ) (E σ τ) θ
  · intro n
    exact ((((hxm n).1.const_mul θ).sub (((hxm n).2.const_mul (θ^2)).div_const 2)).exp).ennreal_ofReal.aemeasurable
  · apply Eventually.of_forall
    intro ω
    exact tendsto_const_nhds.congr' ((hev ω).mono fun n hn => hn.1.symm)
  · apply Eventually.of_forall
    intro ω
    exact tendsto_const_nhds.congr' ((hev ω).mono fun n hn => hn.2.symm)
  · exact hexp

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped ENNReal NNReal
namespace SLEExactGauge

lemma interval_square_energy_bound (f : ℝ → ℝ) (T : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (hb : (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal ((f t)^2)) ≤ ENNReal.ofReal V) :
    (∫ t in (0 : ℝ)..(T : ℝ), (f t)^2) ≤ V := by
  rw [intervalIntegral.integral_of_le T.coe_nonneg]
  have hnorm := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Ioc (0 : ℝ) (T : ℝ)))
    (fun t => (f t)^2)
  simp_rw [Real.enorm_eq_ofReal (sq_nonneg _)] at hnorm
  have hi : 0 ≤ ∫ t in Ioc (0 : ℝ) (T : ℝ), (f t)^2 := integral_nonneg (fun t => sq_nonneg _)
  rw [Real.enorm_eq_ofReal hi] at hnorm
  apply (ENNReal.ofReal_le_ofReal_iff hV).mp
  apply hnorm.trans
  apply le_trans _ hb
  exact lintegral_mono_set (fun t ht => ht.1.le)

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma slabVariance_nonneg (κ ε r : ℝ) (A : Set ℂ) : 0 ≤ slabVariance κ ε r A :=
  ENNReal.toReal_nonneg

lemma ofReal_slabVariance (κ ε r : ℝ) (A : Set ℂ) (hfin : volume A ≠ ∞) :
    ENNReal.ofReal (slabVariance κ ε r A) =
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2 / 4) *
        (2 * (ENNReal.ofReal (layerGreenConstant * r ^ 2) * volume A)) := by
  apply ENNReal.ofReal_toReal
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin))

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem localized_spatial_slab_exponential
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    [IsFiniteMeasure (volume.comap (Subtype.val : A → ℂ))]
    (hfin : volume A ≠ ∞)
    (ε r : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (hheight : ∀ z ∈ A, r ≤ z.im)
    (u δ : ℝ) (b : SpatialAngularFamily a.B a.measurable_B κ
      (Subtype.val : A → ℂ) u δ)
    (M : ℝ) (hM : ∀ z : A, ‖initialLogCoordinates z‖ ≤ M)
    (S : ℝ≥0) (θ : ℝ) :
    (∫⁻ ω : a.samples, ENNReal.ofReal (Real.exp
      (θ * (∫ z : A,
        (b.section z).physicalWeight (boundedSpatialHit (γ ω) z ε S) ω -
        (b.section z).physicalWeight (boundedSpatialHit (γ ω) z r S) ω
        ∂(volume.comap (Subtype.val : A → ℂ))) -
        θ^2 * slabVariance κ ε r A / 2)) ∂(P.comap Subtype.val)) ≤ 1 := by
  classical
  let ν := volume.comap (Subtype.val : A → ℂ)
  let σ (p : A × a.samples) := min (boundedSpatialHit (γ p.2) p.1 r S) (b.τ p)
  let τ (p : A × a.samples) := min (boundedSpatialHit (γ p.2) p.1 ε S) (b.τ p)
  have hσ : IsStoppingTime (spatialFiltration (Z := A) a.filtration)
      (fun p => (σ p : WithTop ℝ≥0)) := by
    simpa only [σ, WithTop.coe_min] using
      (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe r S).min b.stopping
  have hτ : IsStoppingTime (spatialFiltration (Z := A) a.filtration)
      (fun p => (τ p : WithTop ℝ≥0)) := by
    simpa only [τ, WithTop.coe_min] using
      (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe ε S).min b.stopping
  have hστ (p : A × a.samples) : σ p ≤ τ p := by
    apply min_le_min _ le_rfl
    apply boundedSpatialHit_antitone_radius (a.trace_continuous p.2) p.1 hεr
    rw [(a.witness p.2).2.1, dist_zero_left]
    exact (hheight p.1 p.1.2).trans ((le_abs_self p.1.val.im).trans (Complex.abs_im_le_norm p.1))
  have htbound (p : A × a.samples) : τ p ≤ b.T := (min_le_right _ _).trans (b.bounded p)
  have hin (z : A) (ω : a.samples) (t : ℝ≥0) (ht : t ≤ τ (z,ω)) :
      b.lo ≤ ((b.c (initialLogCoordinates z)).Q t ω).1.im ∧
        ((b.c (initialLogCoordinates z)).Q t ω).1.im ≤ b.hi :=
    (b.inside z ω t (ht.trans (min_le_right _ _))).2.2
  have hexp := clipped_spatial_green_window_unbounded_driver (ν := ν) a.measurable_B a.brownian
    a.continuous_B a.zero_B κ b.lo b.hi b.le hκ (by linarith) b.c
    (fun z : A => initialLogCoordinates z) (measurable_initialLogCoordinates.comp measurable_subtype_coe)
    M hM b.T σ τ hσ hτ hστ htbound hin θ
  let E (ω : a.samples) := ∫ t in (0 : ℝ)..(b.T : ℝ),
    (∫ z : A, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
      greenLogCoefficient κ ((b.c (initialLogCoordinates z)).Q t ω) (a.B t.toNNReal ω) else 0 ∂ν)^2
  have hE (ω : a.samples) : E ω ≤ slabVariance κ ε r A := by
    apply interval_square_energy_bound _ b.T _ (slabVariance_nonneg _ _ _ _)
    rw [ofReal_slabVariance _ _ _ _ hfin]
    apply (a.witness ω).spatial_masked_bracket_bound ((a.continuous_B ω).const_mul _)
      hκ hκ4 hε (hε.trans_le hεr) A hA (fun z hz => hεr.trans (hheight z hz))
    intro t ht z
    have hb := clipped_spatial_window_coefficient_le b.c a.continuous_B z
      (show z.val ∈ upperHalfPlane from hε.trans_le (hεr.trans (hheight z z.2))) ω (b.τ (z,ω)) S
      (γ ω) (a.G ω) (a.F ω) (a.witness ω)
      (fun s hs => (b.inside z ω s hs).2.2) r ε t.toNNReal
    simpa only [σ, τ, ← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht] using hb
  apply le_trans _ hexp
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  change θ * _ - θ^2 * slabVariance κ ε r A / 2 ≤ θ * _ - θ^2 * E ω / 2
  have hid : (∫ z : A,
      (b.section z).physicalWeight (boundedSpatialHit (γ ω) z ε S) ω -
      (b.section z).physicalWeight (boundedSpatialHit (γ ω) z r S) ω ∂ν) =
      ∫ z : A, greenLogDensity κ ((b.c (initialLogCoordinates z)).Q (τ (z,ω)) ω) (a.B (τ (z,ω)) ω) -
        greenLogDensity κ ((b.c (initialLogCoordinates z)).Q (σ (z,ω)) ω) (a.B (σ (z,ω)) ω) ∂ν := by
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by simp only [AngularLocalization.physicalWeight,
      SpatialAngularFamily.section, σ, τ, NNReal.coe_min]
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left (hE ω) (sq_nonneg θ)]

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
end
end
end
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
namespace SLEExactGauge
namespace SpatialAngularFamily
variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ : ℝ} {z : Z → ℂ} {u δ : ℝ}
lemma physicalWeight_joint_measurable (b : SpatialAngularFamily B hm κ z u δ)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : Measurable z)
    (η : Z × Ω → ℝ≥0) (hη : Measurable η) :
    Measurable (fun p : Z × Ω => (b.section p.1).physicalWeight (η p) p.2) := by
  let τ (p : Z × Ω) := min (η p) (b.τ p)
  have hτ : Measurable τ := hη.min (stopping_time_measurable_nnreal b.stopping)
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hBc hm
  have hq := measurable_initialLogCoordinates.comp hz
  have hQ := (clipped_family_joint_measurable b.c).comp
    (hτ.prodMk ((hq.comp measurable_fst).prodMk measurable_snd))
  exact (greenLogDensity_contDiff κ).continuous.measurable.comp
    (hQ.prodMk (hBm.comp (hτ.prodMk measurable_snd)))

lemma physicalWeight_uniform_bound (b : SpatialAngularFamily B hm κ z u δ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (l : ℝ) (hl : ∀ x, l ≤ Real.log (z x).im)
    (x : Z) (ω : Ω) (t : ℝ≥0) :
    ‖(b.section x).physicalWeight t ω‖ ≤ Real.exp (codimension κ * (u - Real.log 2 - l)) := by
  rw [Real.norm_eq_abs, abs_of_nonneg ((b.section x).physicalWeight_bound hκ hκ8 t ω).1]
  apply ((b.section x).physicalWeight_bound hκ hκ8 t ω).2.trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by linarith [hl x]) (codimension_pos κ hκ8).le

end SpatialAngularFamily

 

lemma spatial_angular_weight_integral_tendsto
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {ν : Measure Z} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ : ℝ} {z : Z → ℂ} {u : ℝ} {δ : ℕ → ℝ}
    (b : ∀ n, SpatialAngularFamily B hm κ z u (δ n))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : Measurable z)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hzH : ∀ x, z x ∈ upperHalfPlane)
    (l : ℝ) (hl : ∀ x, l ≤ Real.log (z x).im)
    (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (σ τ : Z × Ω → ℝ≥0) (hσ : Measurable σ) (hτ : Measurable τ) :
    Tendsto (fun n => ∫ x, (b n |>.section x).physicalWeight (τ (x,ω)) ω -
      (b n |>.section x).physicalWeight (σ (x,ω)) ω ∂ν) atTop
      (𝓝 (∫ x, physicalStoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G (z x) u (τ (x,ω)) -
        physicalStoppedGreen κ (fun t => Real.sqrt κ * B t ω) γ G (z x) u (σ (x,ω)) ∂ν)) := by
  let K := Real.exp (codimension κ * (u - Real.log 2 - l))
  apply tendsto_integral_of_dominated_convergence (fun _ => 2 * K)
  · intro n
    exact (((b n).physicalWeight_joint_measurable hBc hz τ hτ).sub
      ((b n).physicalWeight_joint_measurable hBc hz σ hσ)).comp
        (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    apply Eventually.of_forall
    intro x
    exact (norm_sub_le _ _).trans (show ‖(b n |>.section x).physicalWeight (τ (x,ω)) ω‖ +
        ‖(b n |>.section x).physicalWeight (σ (x,ω)) ω‖ ≤ 2 * K from by
      have h1 := (b n).physicalWeight_uniform_bound hκ hκ8 l hl x ω (τ (x,ω))
      have h2 := (b n).physicalWeight_uniform_bound hκ hκ8 l hl x ω (σ (x,ω))
      dsimp only [K]; linarith)
  · apply Eventually.of_forall
    intro x
    exact (physicalWeight_tendsto_source (fun n => (b n).section x) hδ hBc hκ hκ8
      (hzH x) ω γ G F hw (τ (x,ω))).sub
      (physicalWeight_tendsto_source (fun n => (b n).section x) hδ hBc hκ hκ8
        (hzH x) ω γ G F hw (σ (x,ω)))

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem spatial_slab_finite_exponential_of_localizations
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    [IsFiniteMeasure (volume.comap (Subtype.val : A → ℂ))]
    (hfin : volume A ≠ ∞)
    (ε r : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (hheight : ∀ z ∈ A, r ≤ z.im)
    (u : ℝ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (b : ∀ n, SpatialAngularFamily a.B a.measurable_B κ (Subtype.val : A → ℂ) u (δ n))
    (l : ℝ) (hl : ∀ z : A, l ≤ Real.log z.val.im)
    (hlevel : ∀ z : A, (2 * z.val.im) * Real.exp (-u) < ε)
    (M : ℝ) (hM : ∀ z : A, ‖initialLogCoordinates z‖ ≤ M)
    (S : ℝ≥0) (θ : ℝ) :
    (∫⁻ ω : a.samples, ENNReal.ofReal (Real.exp
      (θ * (∫ z : A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z
        ∂(volume.comap (Subtype.val : A → ℂ))) -
        θ^2 * slabVariance κ ε r A / 2)) ∂(P.comap Subtype.val)) ≤ 1 := by
  let ν := volume.comap (Subtype.val : A → ℂ)
  let σ (p : A × a.samples) := boundedSpatialHit (γ p.2) p.1 r S
  let τ (p : A × a.samples) := boundedSpatialHit (γ p.2) p.1 ε S
  have hσ : Measurable σ := stopping_time_measurable_nnreal
    (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe r S)
  have hτ : Measurable τ := stopping_time_measurable_nnreal
    (a.joint_boundedSpatialHit_stopping Subtype.val measurable_subtype_coe ε S)
  let X (n : ℕ) (ω : a.samples) := ∫ z : A,
        ((b n).section z).physicalWeight (τ (z,ω)) ω -
        ((b n).section z).physicalWeight (σ (z,ω)) ω ∂ν
  let Y (ω : a.samples) := ∫ z : A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (τ (z,ω)) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (σ (z,ω)) z ∂ν
  have hXm (n : ℕ) : Measurable (X n) :=
    (((b n).physicalWeight_joint_measurable a.continuous_B measurable_subtype_coe τ hτ).sub
      ((b n).physicalWeight_joint_measurable a.continuous_B measurable_subtype_coe σ hσ)).stronglyMeasurable.integral_prod_left'.measurable
  have hlim (ω : a.samples) : Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
    have hh := spatial_angular_weight_integral_tendsto (ν := ν) b hδ a.continuous_B
      measurable_subtype_coe hκ (by linarith) (fun z => hε.trans_le (hεr.trans (hheight z z.2)))
      l hl ω (γ ω) (a.G ω) (a.F ω) (a.witness ω) σ τ hσ hτ
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [(a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z ε hε (hεr.trans (hheight z z.2)) u (hlevel z) (τ (z,ω)) (boundedSpatialHit_le _ _ _ _),
      (a.witness ω).physicalGreen_eq_before_spatial ((a.continuous_B ω).const_mul _)
      κ z r (hε.trans_le hεr) (hheight z z.2) u ((hlevel z).trans_le hεr)
        (σ (z,ω)) (boundedSpatialHit_le _ _ _ _)]
  apply compensated_exponential_limit_energy X (fun _ _ => slabVariance κ ε r A) Y
    (fun _ => slabVariance κ ε r A) θ
  · intro n
    exact ((((hXm n).const_mul θ).sub_const (θ^2 * slabVariance κ ε r A / 2)).exp).ennreal_ofReal.aemeasurable
  · exact Eventually.of_forall hlim
  · exact Eventually.of_forall fun _ => tendsto_const_nhds
  · intro n
    exact a.localized_spatial_slab_exponential hκ hκ4 A hA hfin ε r hε hεr hheight u (δ n) (b n) M hM S θ

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma logAngleSq_initial (κ : ℝ) (z : ℂ) (hz : 0 < z.im) :
    logAngleSq κ (initialLogCoordinates z) 0 = z.im^2 / ‖z‖^2 := by
  have he : Real.exp (2 * Real.log z.im) = z.im ^ 2 := by
    rw [show 2 * Real.log z.im = Real.log z.im + Real.log z.im by ring,
      Real.exp_add, Real.exp_log hz, pow_two]
  rw [logAngleSq, initialLogCoordinates_im, he]
  congr 1
  rw [← Complex.normSq_eq_norm_sq]
  simp only [greenLogNormSq, initialLogCoordinates, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_self, add_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, he,
      Complex.normSq_apply, pow_two]

lemma initial_spatial_bounds (κ r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (z : ℂ) (hz : r ≤ z.im) (hzR : ‖z‖ ≤ R) :
    (Real.log r ≤ Real.log z.im ∧ Real.log z.im ≤ Real.log R) ∧
    r^2 / R^2 ≤ logAngleSq κ (initialLogCoordinates z) 0 ∧
    ‖initialLogCoordinates z‖ ≤ R + |Real.log r| + |Real.log R| := by
  have hy : 0 < z.im := hr.trans_le hz
  have him : z.im ≤ R := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hzR)
  have hl := Real.log_le_log hr hz
  have hh := Real.log_le_log hy him
  refine ⟨⟨hl, hh⟩, ?_, ?_⟩
  · rw [logAngleSq_initial κ z hy]
    have hn : 0 < ‖z‖ := hy.trans_le ((le_abs_self _).trans (Complex.abs_im_le_norm z))
    calc
      r^2 / R^2 ≤ z.im^2 / R^2 := div_le_div_of_nonneg_right
        (sq_le_sq₀ hr.le hy.le |>.mpr hz) (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hn)
        (sq_le_sq₀ (norm_nonneg z) hR.le |>.mpr hzR)
  · have hlog : |Real.log z.im| ≤ |Real.log r| + |Real.log R| := by
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (Real.log r), abs_nonneg (Real.log R)]
      · linarith [le_abs_self (Real.log R), abs_nonneg (Real.log r)]
    have hnorm : ‖initialLogCoordinates z‖ ≤ |z.re| + |Real.log z.im| := by
      have hh := norm_add_le (z.re : ℂ) ((Real.log z.im : ℂ) * Complex.I)
      simpa only [initialLogCoordinates, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _),
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using hh
    have hre := (Complex.abs_re_le_norm z).trans hzR
    exact hnorm.trans (by linarith)

lemma exists_uniform_radius_level (ε R : ℝ) (hε : 0 < ε) (_hR : 0 ≤ R) :
    ∃ u : ℝ, 0 ≤ u ∧ (2 * R) * Real.exp (-u) < ε := by
  have ht : Tendsto (fun u : ℝ => (2 * R) * Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (2 * R)
  obtain ⟨u, hu0, hu⟩ := (eventually_ge_atTop (0 : ℝ)).and ((tendsto_order.mp ht).2 ε hε) |>.exists
  exact ⟨u, hu0, hu⟩

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem spatial_slab_finite_exponential
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (S : ℝ≥0) (θ : ℝ) :
    (∫⁻ ω : a.samples, ENNReal.ofReal (Real.exp
      (θ * (∫ z in A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z) -
        θ^2 * slabVariance κ ε r A / 2)) ∂(P.comap Subtype.val)) ≤ 1 := by
  have hr : 0 < r := hε.trans_le hεr
  have hR : 0 < R := hr.trans_le hrR
  have hs : A ⊆ closedBall 0 R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hbound z hz
  have hfin : volume A ≠ ∞ := ne_of_lt
    ((measure_mono hs).trans_lt (isCompact_closedBall (0 : ℂ) R).measure_lt_top)
  let ν := volume.comap (Subtype.val : A → ℂ)
  let : IsFiniteMeasure ν := ⟨by
    have hh := Measure.comap_apply_le (Subtype.val : A → ℂ) volume
      (show NullMeasurableSet (univ : Set A) ν from MeasurableSet.univ.nullMeasurableSet)
    apply lt_of_le_of_lt hh
    simpa only [Set.image_univ, Subtype.range_coe] using lt_top_iff_ne_top.mpr hfin⟩
  obtain ⟨u, hu, hul⟩ := exists_uniform_radius_level ε R hε hR.le
  let α := r^2 / R^2
  have hα : 0 < α := by dsimp [α]; positivity
  let δ (n : ℕ) := α / ((n : ℝ) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ α := div_le_self hα.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul α
  have hbounds (z : A) := initial_spatial_bounds κ r R hr hR z (hheight z z.2) (hbound z z.2)
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  let b (n : ℕ) : SpatialAngularFamily a.B a.measurable_B κ (Subtype.val : A → ℂ) u (δ n) :=
    (exists_spatial_angular_family a.measurable_B hBm a.continuous_B a.zero_B κ Subtype.val
      measurable_subtype_coe (Real.log r) (Real.log R) (Real.log_le_log hr hrR)
      (fun z => (hbounds z).1) u (δ n) hu (hδpos n)
      (fun z => (hδle n).trans (hbounds z).2.1)).some
  have hlevel (z : A) : (2 * z.val.im) * Real.exp (-u) < ε := by
    have hi : z.val.im ≤ R := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans (hbound z z.2))
    exact (mul_le_mul_of_nonneg_right (by linarith : 2 * z.val.im ≤ 2 * R) (Real.exp_pos _).le).trans_lt hul
  have hh := a.spatial_slab_finite_exponential_of_localizations hκ hκ4 A hA hfin ε r hε hεr
    hheight u δ hδlim b (Real.log r) (fun z => (hbounds z).1.1) hlevel
    (R + |Real.log r| + |Real.log R|) (fun z => (hbounds z).2.2) S θ
  have he (ω : a.samples) :
      (∫ z : A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z
        ∂(volume.comap (Subtype.val : A → ℂ))) =
      ∫ z in A,
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
        greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z :=
    integral_subtype_comap (μ := volume) hA (fun z =>
      greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε S) z -
      greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r S) z)
  simpa only [he] using hh

end RegularSLEPresentation
end SLEExactGauge

 

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



theorem spatial_slab_terminal_exponential_oai [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (ε r R : ℝ) (hε : 0 < ε) (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (θ : ℝ) :
    (∫⁻ ω : a.samples, ENNReal.ofReal (Real.exp
      (θ * spatialSlabIncrement κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) A ε r - θ^2 * slabVariance κ ε r A / 2)) ∂(P.comap Subtype.val)) ≤ 1 := by
  have hs : A ⊆ closedBall 0 R := by
    intro z hz
    simpa only [mem_closedBall, dist_zero_right] using hbound z hz
  have hfin : volume A ≠ ∞ := ne_of_lt
    ((measure_mono hs).trans_lt (isCompact_closedBall (0 : ℂ) R).measure_lt_top)
  let X (n : ℕ) (ω : a.samples) := ∫ z in A,
    greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z ε n) z -
    greenDensity κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r n) z
  let Y (ω : a.samples) := spatialSlabIncrement κ (fun t => Real.sqrt κ * a.B t ω)
    (γ ω) (a.G ω) A ε r
  have hXm (n : ℕ) : Measurable (X n) :=
    ((a.boundedSpatialGreen_measurable ε n).sub
      (a.boundedSpatialGreen_measurable r n)).stronglyMeasurable.integral_prod_left'.measurable
  apply compensated_exponential_limit_energy X (fun _ _ => slabVariance κ ε r A) Y
    (fun _ => slabVariance κ ε r A) θ
  · intro n
    exact ((((hXm n).const_mul θ).sub_const (θ^2 * slabVariance κ ε r A / 2)).exp).ennreal_ofReal.aemeasurable
  · exact a.spatial_slab_area_tendsto hκ (by linarith) A hA hfin ε r R hε hεr hrR hheight hbound
  · exact Eventually.of_forall fun _ => tendsto_const_nhds
  · intro n
    exact a.spatial_slab_finite_exponential hκ hκ4 A hA ε r R hε hεr hrR hheight hbound n θ


end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal



open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
end
end
end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SLEExactGauge.RegularSLEPresentation.spatial_slab_terminal_exponential_oai.{u_1} := @OAI.SLEExactGauge.RegularSLEPresentation.spatial_slab_terminal_exponential_oai.{u_1}
