-- Prove2me | solution 1 for HighDimStat.Rkhs.mercer_spectral_basis_and_continuous_reps
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T04:46:37.711857+00:00
-- url     : https://prove2.me/submissions/c2a41a30-2401-4bb8-85c2-b6225cd66b98

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_HighDimStat_Rkhs_Core
import Theorems.Thm_HighDimStat_Rkhs_exists_countable_hilbertBasis_eigenvectors

open MeasureTheory ProbabilityTheory BoundedContinuousFunction Filter HighDimStat.Rkhs
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace MercerProof

noncomputable section

section KernelOperator

variable {X : Type*} [MetricSpace X] [CompactSpace X]

lemma exists_nonneg_bound_kernel (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x z : X, |K x z| ≤ M := by
  obtain ⟨M₀, hM₀⟩ :=
    isCompact_univ.exists_bound_of_continuousOn hKcont.continuousOn
  refine ⟨max M₀ 0, le_max_right _ _, fun x z => ?_⟩
  have h1 : ‖Function.uncurry K (x, z)‖ ≤ M₀ := hM₀ (x, z) (Set.mem_univ _)
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (le_max_left _ _)

def kxBCF (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (x : X) : X →ᵇ ℝ :=
  mkOfCompact ⟨fun z => K x z, hKcont.comp (continuous_const.prodMk continuous_id)⟩

@[simp]
lemma kxBCF_apply (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (x z : X) :
    kxBCF K hKcont x z = K x z := rfl

lemma continuous_kxBCF (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    Continuous (kxBCF K hKcont) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have huc := CompactSpace.uniformContinuous_of_continuous hKcont
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).mpr fun z => ?_)
    (half_lt_self hε)
  have hp : dist (y, z) (x, z) < δ := by
    simpa [Prod.dist_eq] using hy
  exact (hdist hp).le

variable [MeasurableSpace X] [BorelSpace X]

def kxLp (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (x : X) : Lp ℝ 2 P :=
  BoundedContinuousFunction.toLp 2 P ℝ (kxBCF K hKcont x)

lemma continuous_kxLp (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    Continuous (kxLp P K hKcont) :=
  (BoundedContinuousFunction.toLp 2 P ℝ).continuous.comp (continuous_kxBCF K hKcont)

lemma inner_kxLp_eq (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K))
    (x : X) (f : Lp ℝ 2 P) :
    ⟪kxLp P K hKcont x, f⟫ = ∫ z, K x z * f z ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 P ℝ (kxBCF K hKcont x)] with z hz
  change RCLike.re ((f z) * starRingEnd ℝ (kxLp P K hKcont x z)) = K x z * f z
  dsimp only [kxLp]
  rw [RCLike.re_to_real, starRingEnd_apply, star_trivial, hz, kxBCF_apply, mul_comm]

def intKernelBCF (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (f : Lp ℝ 2 P) : X →ᵇ ℝ :=
  mkOfCompact ⟨fun x => ⟪kxLp P K hKcont x, f⟫,
    (continuous_kxLp P K hKcont).inner continuous_const⟩

@[simp]
lemma intKernelBCF_apply (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K))
    (f : Lp ℝ 2 P) (x : X) :
    intKernelBCF P K hKcont f x = ∫ z, K x z * f z ∂P :=
  inner_kxLp_eq P K hKcont x f

def intKernelLM (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    Lp ℝ 2 P →ₗ[ℝ] (X →ᵇ ℝ) where
  toFun := intKernelBCF P K hKcont
  map_add' f g := by
    ext x
    change ⟪kxLp P K hKcont x, f + g⟫ = ⟪kxLp P K hKcont x, f⟫ + ⟪kxLp P K hKcont x, g⟫
    exact inner_add_right _ _ _
  map_smul' c f := by
    ext x
    change ⟪kxLp P K hKcont x, c • f⟫ = c * ⟪kxLp P K hKcont x, f⟫
    exact inner_smul_right _ _ _

lemma exists_norm_bound_kxLp (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : X, ‖kxLp P K hKcont x‖ ≤ B := by
  obtain ⟨B₀, hB₀⟩ :=
    isCompact_univ.exists_bound_of_continuousOn (continuous_kxLp P K hKcont).continuousOn
  refine ⟨max B₀ 0, le_max_right _ _, fun x => ?_⟩
  exact (hB₀ x (Set.mem_univ _)).trans (le_max_left _ _)

def intKernelCLM (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    Lp ℝ 2 P →L[ℝ] (X →ᵇ ℝ) :=
  let B := Classical.choose (exists_norm_bound_kxLp P K hKcont)
  have hB := Classical.choose_spec (exists_norm_bound_kxLp P K hKcont)
  LinearMap.mkContinuous (intKernelLM P K hKcont) B fun f => by
    refine (BoundedContinuousFunction.norm_le (mul_nonneg hB.1 (norm_nonneg f))).mpr fun x => ?_
    change ‖⟪kxLp P K hKcont x, f⟫‖ ≤ B * ‖f‖
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hB.2 x) (norm_nonneg f))

@[simp]
lemma intKernelCLM_apply (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K))
    (f : Lp ℝ 2 P) (x : X) :
    intKernelCLM P K hKcont f x = ∫ z, K x z * f z ∂P :=
  inner_kxLp_eq P K hKcont x f

lemma isCompactOperator_intKernelCLM (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    IsCompactOperator (intKernelCLM P K hKcont) := by
  obtain ⟨B, hB0, hBx⟩ := exists_norm_bound_kxLp P K hKcont
  refine ⟨closure (intKernelCLM P K hKcont '' Metric.ball 0 1), ?_,
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one)
      (Set.image_subset_iff.mp subset_closure)⟩
  refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) B)
    (isCompact_closedBall 0 B) _ ?_ ?_
  · rintro g x ⟨f, hf, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    have hf1 : ‖f‖ ≤ 1 := (mem_ball_zero_iff.mp hf).le
    change |⟪kxLp P K hKcont x, f⟫| ≤ B
    calc |⟪kxLp P K hKcont x, f⟫|
        ≤ ‖kxLp P K hKcont x‖ * ‖f‖ := abs_real_inner_le_norm _ _
      _ ≤ B * 1 := mul_le_mul (hBx x) hf1 (norm_nonneg _) hB0
      _ = B := mul_one B
  · intro x₀
    rw [Metric.equicontinuousAt_iff_pair]
    intro ε hε
    have hcont_at := (continuous_kxLp P K hKcont).continuousAt (x := x₀)
    have hnhds : {y : X | dist (kxLp P K hKcont y) (kxLp P K hKcont x₀) < ε / 2} ∈ 𝓝 x₀ :=
      hcont_at (Metric.ball_mem_nhds _ (half_pos hε))
    refine ⟨_, hnhds, ?_⟩
    rintro y hy z hz ⟨_, ⟨f, hf, rfl⟩⟩
    have hf1 : ‖f‖ ≤ 1 := (mem_ball_zero_iff.mp hf).le
    change dist (intKernelCLM P K hKcont f y) (intKernelCLM P K hKcont f z) < ε
    rw [Real.dist_eq]
    have hsub : intKernelCLM P K hKcont f y - intKernelCLM P K hKcont f z =
        ⟪kxLp P K hKcont y - kxLp P K hKcont z, f⟫ := by
      change ⟪kxLp P K hKcont y, f⟫ - ⟪kxLp P K hKcont z, f⟫ = _
      rw [inner_sub_left]
    rw [hsub]
    calc |⟪kxLp P K hKcont y - kxLp P K hKcont z, f⟫|
        ≤ ‖kxLp P K hKcont y - kxLp P K hKcont z‖ * ‖f‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖kxLp P K hKcont y - kxLp P K hKcont z‖ * 1 :=
            mul_le_mul_of_nonneg_left hf1 (norm_nonneg _)
      _ = dist (kxLp P K hKcont y) (kxLp P K hKcont z) := by rw [mul_one, dist_eq_norm]
      _ ≤ dist (kxLp P K hKcont y) (kxLp P K hKcont x₀) +
            dist (kxLp P K hKcont x₀) (kxLp P K hKcont z) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
            have hy' : dist (kxLp P K hKcont y) (kxLp P K hKcont x₀) < ε / 2 := hy
            have hz' : dist (kxLp P K hKcont z) (kxLp P K hKcont x₀) < ε / 2 := hz
            rw [dist_comm (kxLp P K hKcont x₀)]
            linarith
      _ = ε := add_halves ε

def tkCLM (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (BoundedContinuousFunction.toLp 2 P ℝ).comp (intKernelCLM P K hKcont)

lemma tkCLM_eq_TK (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K))
    (TK : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P)
    (hTK : ∀ f : Lp ℝ 2 P, (TK f : X → ℝ) =ᵐ[P] fun x => ∫ z, K x z * f z ∂P)
    (f : Lp ℝ 2 P) :
    tkCLM P K hKcont f = TK f := by
  rw [Lp.ext_iff]
  have h1 := BoundedContinuousFunction.coeFn_toLp 2 P ℝ (intKernelCLM P K hKcont f)
  filter_upwards [h1, hTK f] with x hx1 hx2
  dsimp only [tkCLM, ContinuousLinearMap.comp_apply]
  rw [hx1, intKernelCLM_apply, hx2]

lemma isCompactOperator_tkCLM (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) :
    IsCompactOperator (tkCLM P K hKcont) :=
  (isCompactOperator_intKernelCLM P K hKcont).clm_comp (BoundedContinuousFunction.toLp 2 P ℝ)

lemma integrable_kernel_prod (Q : Measure X) [IsFiniteMeasure Q]
    (H : X → X → ℝ) (hHcont : Continuous (Function.uncurry H))
    {f g : X → ℝ} (hf : Integrable f Q) (hg : Integrable g Q) :
    Integrable (fun p : X × X => H p.1 p.2 * f p.2 * g p.1) (Q.prod Q) := by
  obtain ⟨M, _, hM⟩ := exists_nonneg_bound_kernel H hHcont
  have hdom : Integrable (fun p : X × X => M * (‖g p.1‖ * ‖f p.2‖)) (Q.prod Q) :=
    (hg.norm.mul_prod hf.norm).const_mul M
  have haesm : AEStronglyMeasurable
      (fun p : X × X => H p.1 p.2 * f p.2 * g p.1) (Q.prod Q) :=
    (hHcont.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
      hg.aestronglyMeasurable.comp_fst
  refine hdom.mono' haesm (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |H p.1 p.2| * |f p.2| * |g p.1|
      ≤ M * |f p.2| * |g p.1| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hM p.1 p.2) (abs_nonneg _)) (abs_nonneg _)
    _ = M * (|g p.1| * |f p.2|) := by ring

lemma inner_tkCLM_eq_double_integral (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K))
    (f g : Lp ℝ 2 P) :
    ⟪tkCLM P K hKcont f, g⟫ = ∫ x, (∫ z, K x z * f z ∂P) * g x ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 P ℝ (intKernelCLM P K hKcont f)] with x hx
  change RCLike.re (g x * starRingEnd ℝ (tkCLM P K hKcont f x)) =
    (∫ z, K x z * f z ∂P) * g x
  dsimp only [tkCLM, ContinuousLinearMap.comp_apply]
  rw [RCLike.re_to_real, starRingEnd_apply, star_trivial, hx, intKernelCLM_apply, mul_comm]

lemma tkCLM_isSymmetric (P : Measure X) [IsFiniteMeasure P]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K))
    (hKsym : ∀ x z, K x z = K z x) :
    (tkCLM P K hKcont : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P).IsSymmetric := by
  intro f g
  change ⟪tkCLM P K hKcont f, g⟫ = ⟪f, tkCLM P K hKcont g⟫
  rw [real_inner_comm (tkCLM P K hKcont g) f,
    inner_tkCLM_eq_double_integral, inner_tkCLM_eq_double_integral]
  have hf1 : Integrable (f : X → ℝ) P := (Lp.memLp f).integrable one_le_two
  have hg1 : Integrable (g : X → ℝ) P := (Lp.memLp g).integrable one_le_two
  have hint := integrable_kernel_prod P K hKcont hf1 hg1
  have hl : (∫ x, (∫ z, K x z * f z ∂P) * g x ∂P) =
      ∫ x, ∫ z, K x z * f z * g x ∂P ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← integral_mul_const]
  have hr : (∫ z, (∫ x, K z x * g x ∂P) * f z ∂P) =
      ∫ z, ∫ x, K x z * f z * g x ∂P ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hKsym x z]; ring
  rw [hl, hr]
  exact MeasureTheory.integral_integral_swap hint

lemma tkCLM_inner_self_nonneg (P : Measure X) [IsFiniteMeasure P] [P.IsOpenPosMeasure]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (hKpsd : IsPSDKernel K)
    (f : Lp ℝ 2 P) :
    0 ≤ ⟪tkCLM P K hKcont f, f⟫ := by
  by_cases hX : Nonempty X
  · have : Nonempty X := hX
    have hP_ne_zero : P Set.univ ≠ 0 := isOpen_univ.measure_ne_zero P Set.univ_nonempty
    have hP_ne_top : P Set.univ ≠ ⊤ := measure_ne_top P Set.univ
    let P₀ : Measure X := (P Set.univ)⁻¹ • P
    have hP₀_prob : IsProbabilityMeasure P₀ := by
      refine ⟨?_⟩
      simp only [P₀, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hP_ne_zero hP_ne_top
    have : IsProbabilityMeasure P₀ := hP₀_prob
    have hf_P₀ : Integrable (f : X → ℝ) P₀ :=
      ((Lp.memLp f).integrable one_le_two).smul_measure (ENNReal.inv_ne_top.mpr hP_ne_zero)
    have hf2_P₀ : Integrable (fun x => (f x) ^ 2) P₀ :=
      ((Lp.memLp f).integrable_sq).smul_measure (ENNReal.inv_ne_top.mpr hP_ne_zero)
    obtain ⟨M, _, hM⟩ := exists_nonneg_bound_kernel K hKcont
    have hdiag_int : Integrable (fun x : X => f x * f x * K x x) P₀ := by
      have haesm : AEStronglyMeasurable (fun x : X => f x * f x * K x x) P₀ :=
        (hf_P₀.aestronglyMeasurable.mul hf_P₀.aestronglyMeasurable).mul
          (hKcont.comp (continuous_id.prodMk continuous_id)).aestronglyMeasurable
      refine (hf2_P₀.const_mul M).mono' haesm (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |f x| * |f x| * |K x x|
          ≤ |f x| * |f x| * M :=
            mul_le_mul_of_nonneg_left (hM x x) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = M * |f x| ^ 2 := by ring
        _ = M * (f x) ^ 2 := by rw [sq_abs]
    have hoff_int : Integrable (fun p : X × X => f p.1 * f p.2 * K p.1 p.2) (P₀.prod P₀) := by
      have h1 := integrable_kernel_prod P₀ K hKcont hf_P₀ hf_P₀
      refine h1.congr (Filter.Eventually.of_forall fun p => by ring)
    let I_off : ℝ := ∫ p : X × X, f p.1 * f p.2 * K p.1 p.2 ∂(P₀.prod P₀)
    let I_diag : ℝ := ∫ x : X, f x * f x * K x x ∂P₀
    have hineq_m : ∀ m : ℕ, 1 ≤ m → 0 ≤ ((m : ℝ) - 1) * I_off + I_diag := by
      intro m hm1
      let μm : Measure (Fin m → X) := Measure.pi (fun _ : Fin m => P₀)
      have hindep : iIndepFun (fun (i : Fin m) (ω : Fin m → X) => ω i) μm :=
        iIndepFun_pi fun _ => measurable_id.aemeasurable
      let term (a b : Fin m) (ω : Fin m → X) : ℝ := f (ω a) * f (ω b) * K (ω a) (ω b)
      have hterm_int_eq : ∀ a b : Fin m,
          Integrable (term a b) μm ∧
            ∫ ω, term a b ω ∂μm = if a = b then I_diag else I_off := by
        intro a b
        by_cases hab : a = b
        · subst hab
          rw [if_pos rfl]
          have hmp : MeasurePreserving (fun ω : Fin m → X => ω a) μm P₀ :=
            MeasureTheory.measurePreserving_eval (fun _ : Fin m => P₀) a
          have hint_ab : Integrable (term a a) μm :=
            hmp.integrable_comp_of_integrable hdiag_int
          refine ⟨hint_ab, ?_⟩
          have haesm : AEStronglyMeasurable (fun x : X => f x * f x * K x x)
              (Measure.map (fun ω : Fin m → X => ω a) μm) := by
            rw [hmp.map_eq]; exact hdiag_int.aestronglyMeasurable
          exact (MeasureTheory.integral_map hmp.measurable.aemeasurable haesm).symm.trans
            (by rw [hmp.map_eq])
        · rw [if_neg hab]
          have hind_ab : IndepFun (fun ω : Fin m → X => ω a) (fun ω : Fin m → X => ω b) μm :=
            hindep.indepFun hab
          have hmp_a : MeasurePreserving (fun ω : Fin m → X => ω a) μm P₀ :=
            MeasureTheory.measurePreserving_eval (fun _ : Fin m => P₀) a
          have hmp_b : MeasurePreserving (fun ω : Fin m → X => ω b) μm P₀ :=
            MeasureTheory.measurePreserving_eval (fun _ : Fin m => P₀) b
          have hmap_prod : Measure.map (fun ω : Fin m → X => (ω a, ω b)) μm = P₀.prod P₀ := by
            have hm := (indepFun_iff_map_prod_eq_prod_map_map
              hmp_a.measurable.aemeasurable hmp_b.measurable.aemeasurable).mp hind_ab
            rwa [hmp_a.map_eq, hmp_b.map_eq] at hm
          have hmp_pair : MeasurePreserving (fun ω : Fin m → X => (ω a, ω b)) μm (P₀.prod P₀) :=
            ⟨(measurable_pi_apply a).prodMk (measurable_pi_apply b), hmap_prod⟩
          have hint_ab : Integrable (term a b) μm :=
            hmp_pair.integrable_comp_of_integrable hoff_int
          refine ⟨hint_ab, ?_⟩
          have haesm : AEStronglyMeasurable (fun p : X × X => f p.1 * f p.2 * K p.1 p.2)
              (Measure.map (fun ω : Fin m → X => (ω a, ω b)) μm) := by
            rw [hmap_prod]; exact hoff_int.aestronglyMeasurable
          exact (MeasureTheory.integral_map hmp_pair.measurable.aemeasurable haesm).symm.trans
            (by rw [hmap_prod])
      have hsum_nonneg : 0 ≤ ∫ ω, (∑ a : Fin m, ∑ b : Fin m, term a b ω) ∂μm :=
        integral_nonneg fun ω => hKpsd.2 m ω (fun a => f (ω a))
      have hsum_eq :
          ∫ ω, (∑ a : Fin m, ∑ b : Fin m, term a b ω) ∂μm =
            ∑ a : Fin m, ∑ b : Fin m, (if a = b then I_diag else I_off) := by
        rw [integral_finsetSum _ fun a _ =>
          integrable_finsetSum _ fun b _ => (hterm_int_eq a b).1]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finsetSum _ fun b _ => (hterm_int_eq a b).1]
        exact Finset.sum_congr rfl fun b _ => (hterm_int_eq a b).2
      rw [hsum_eq] at hsum_nonneg
      have hinner : ∀ a : Fin m,
          (∑ b : Fin m, if a = b then I_diag else I_off) =
            I_diag + ((m : ℝ) - 1) * I_off := by
        intro a
        have h1 : (Finset.univ : Finset (Fin m)) = insert a (Finset.univ.erase a) :=
          (Finset.insert_erase (Finset.mem_univ a)).symm
        rw [h1, Finset.sum_insert (Finset.notMem_erase a _), if_pos rfl]
        have h2 : ∑ b ∈ Finset.univ.erase a, (if a = b then I_diag else I_off) =
            ∑ _b ∈ Finset.univ.erase a, I_off := by
          refine Finset.sum_congr rfl fun b hb => ?_
          rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hb))]
        rw [h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hm_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
          rw [Nat.cast_sub hm1, Nat.cast_one]
        rw [hm_cast]
      have htotal : (∑ a : Fin m, ∑ b : Fin m, if a = b then I_diag else I_off) =
          (m : ℝ) * (((m : ℝ) - 1) * I_off + I_diag) := by
        simp_rw [hinner]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [htotal] at hsum_nonneg
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      exact nonneg_of_mul_nonneg_right hsum_nonneg hm_pos
    have hI_off_nonneg : 0 ≤ I_off := by
      by_contra hneg
      push Not at hneg
      obtain ⟨m, hm_gt⟩ := exists_nat_gt (1 + (|I_diag| + 1) / (-I_off))
      have hm1 : 1 ≤ m := by
        have hpos : 0 < 1 + (|I_diag| + 1) / (-I_off) := by
          have : 0 < -I_off := by linarith
          positivity
        have : (1 : ℝ) < (m : ℝ) := by
          have : 0 ≤ (|I_diag| + 1) / (-I_off) := by
            have : 0 < -I_off := by linarith
            positivity
          linarith
        exact_mod_cast this.le
      have hge := hineq_m m hm1
      have hneg_pos : 0 < -I_off := by linarith
      have hlt : |I_diag| + 1 < ((m : ℝ) - 1) * (-I_off) := by
        rw [← div_lt_iff₀ hneg_pos]
        linarith
      have hle_abs : I_diag ≤ |I_diag| := le_abs_self I_diag
      linarith
    have hscale : I_off = (((P Set.univ)⁻¹).toReal) ^ 2 * ⟪tkCLM P K hKcont f, f⟫ := by
      dsimp [I_off]
      rw [MeasureTheory.integral_prod _ hoff_int]
      simp only [P₀, integral_smul_measure, smul_eq_mul]
      rw [inner_tkCLM_eq_double_integral]
      have hinner_eq : ∀ x : X,
          (∫ z : X, f x * f z * K x z ∂P) =
            (∫ z : X, K x z * f z ∂P) * f x := by
        intro x
        calc (∫ z : X, f x * f z * K x z ∂P)
            = ∫ z : X, (K x z * f z) * f x ∂P :=
              integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
          _ = (∫ z : X, K x z * f z ∂P) * f x := integral_mul_const _ _
      simp_rw [hinner_eq]
      calc (((P Set.univ)⁻¹).toReal * ∫ x : X, ((P Set.univ)⁻¹).toReal *
            ((∫ z : X, K x z * f z ∂P) * f x) ∂P)
          = (((P Set.univ)⁻¹).toReal * ((P Set.univ)⁻¹).toReal) *
              ∫ x : X, (∫ z : X, K x z * f z ∂P) * f x ∂P := by
              rw [integral_const_mul, mul_assoc]
        _ = (((P Set.univ)⁻¹).toReal) ^ 2 *
              ∫ x : X, (∫ z : X, K x z * f z ∂P) * f x ∂P := by ring
    have hc_pos : 0 < (((P Set.univ)⁻¹).toReal) ^ 2 := by
      have h1 : (P Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hP_ne_top
      have h2 : (P Set.univ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hP_ne_zero
      have htr : 0 < ((P Set.univ)⁻¹).toReal := ENNReal.toReal_pos h1 h2
      positivity
    rw [hscale] at hI_off_nonneg
    exact nonneg_of_mul_nonneg_right hI_off_nonneg hc_pos
  · have : IsEmpty X := not_nonempty_iff.mp hX
    have hf0 : f = 0 := Lp.ext_iff.mpr (Filter.Eventually.of_forall fun x => isEmptyElim x)
    rw [hf0, map_zero, inner_zero_left]

lemma bessel_diag_le {ι : Type*} [DecidableEq ι]
    (P : Measure X) [IsFiniteMeasure P] [P.IsOpenPosMeasure]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (hKpsd : IsPSDKernel K)
    (φ : HilbertBasis ι ℝ (Lp ℝ 2 P)) (μ : ι → ℝ) (ψ : ι → X → ℝ)
    (hφ_eig : ∀ j : ι, tkCLM P K hKcont (φ j) = μ j • (φ j : Lp ℝ 2 P))
    (hμ_nonneg : ∀ j : ι, 0 ≤ μ j)
    (hψ_cont : ∀ j : ι, 0 < μ j → Continuous (ψ j))
    (hφ_ae_ψ : ∀ j : ι, (φ j : X → ℝ) =ᵐ[P] ψ j)
    (hterm_cont : ∀ j : ι, Continuous (fun p : X × X => μ j * ψ j p.1 * ψ j p.2))
    (S : Finset ι) (x₀ : X) :
    ∑ j ∈ S, μ j * (ψ j x₀) ^ 2 ≤ K x₀ x₀ := by
  let T : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P := tkCLM P K hKcont
  have hT_sym : (T : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P).IsSymmetric :=
    tkCLM_isSymmetric P K hKcont hKpsd.1
  let R : X → X → ℝ := fun x z => K x z - ∑ j ∈ S, μ j * ψ j x * ψ j z
  have hR_cont : Continuous (Function.uncurry R) := by
    have heq : Function.uncurry R = fun p : X × X =>
        Function.uncurry K p - ∑ j ∈ S, μ j * ψ j p.1 * ψ j p.2 := by
      funext p; rfl
    rw [heq]
    exact hKcont.sub (continuous_finsetSum S fun j _ => hterm_cont j)
  have hR_L2_nonneg : ∀ f : Lp ℝ 2 P,
      0 ≤ ∫ x, (∫ z, R x z * f z ∂P) * f x ∂P := by
    intro f
    let pS : Lp ℝ 2 P := ∑ j ∈ S, ⟪φ j, f⟫ • φ j
    let fS : Lp ℝ 2 P := f - pS
    have hfS_orth : ∀ j ∈ S, ⟪φ j, fS⟫ = 0 := by
      intro j hj
      simp only [fS, pS, inner_sub_right, inner_sum, inner_smul_right]
      have hsum_orth : ∑ i ∈ S, ⟪φ i, f⟫ * ⟪φ j, φ i⟫ = ⟪φ j, f⟫ := by
        rw [Finset.sum_eq_single j]
        · rw [real_inner_self_eq_norm_mul_norm, φ.orthonormal.1 j, mul_one, mul_one]
        · intro i _ hij
          rw [φ.orthonormal.2 (Ne.symm hij), mul_zero]
        · intro hjS; exact False.elim (hjS hj)
      rw [hsum_orth, sub_self]
    have hTpS : T pS = ∑ j ∈ S, (μ j * ⟪φ j, f⟫) • φ j := by
      dsimp only [T, pS]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => by
        rw [map_smul, hφ_eig j, smul_smul, mul_comm]
    have hTfS_pS : ⟪T fS, pS⟫ = 0 := by
      have hsym_eq : ⟪T fS, pS⟫ = ⟪fS, T pS⟫ := hT_sym fS pS
      rw [hsym_eq, hTpS, inner_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [inner_smul_right, real_inner_comm (φ j) fS, hfS_orth j hj, mul_zero]
    have hpS_fS : ⟪T pS, fS⟫ = 0 := by
      rw [hTpS, sum_inner]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [inner_smul_left, RCLike.conj_to_real, hfS_orth j hj, mul_zero]
    have hTpS_pS : ⟪T pS, pS⟫ = ∑ j ∈ S, μ j * ⟪φ j, f⟫ ^ 2 := by
      rw [hTpS]
      simp only [pS, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.sum_eq_single j]
      · rw [real_inner_self_eq_norm_mul_norm, φ.orthonormal.1 j]
        ring
      · intro i _ hij
        rw [φ.orthonormal.2 hij, mul_zero]
      · intro hjS; exact False.elim (hjS hj)
    have hTf_decomp : ⟪T f, f⟫ - ∑ j ∈ S, μ j * ⟪φ j, f⟫ ^ 2 = ⟪T fS, fS⟫ := by
      have hf_eq : f = fS + pS := by simp [fS]
      have hTff : ⟪T f, f⟫ = ⟪T fS, fS⟫ + ∑ j ∈ S, μ j * ⟪φ j, f⟫ ^ 2 := by
        conv_lhs => rw [hf_eq]
        rw [map_add, inner_add_left, inner_add_right, inner_add_right,
          hTfS_pS, hpS_fS, hTpS_pS]
        ring
      linarith
    have hf1 : Integrable (f : X → ℝ) P := (Lp.memLp f).integrable one_le_two
    have hterm_int_z : ∀ (j : ι) (x : X),
        Integrable (fun z => μ j * ψ j x * ψ j z * f z) P := by
      intro j x
      by_cases hj : 0 < μ j
      · obtain ⟨Bj, _, hBj⟩ := exists_nonneg_bound_kernel
          (fun u v => μ j * ψ j u * ψ j v) (hterm_cont j)
        refine (hf1.norm.const_mul Bj).mono'
          (((hterm_cont j).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
            hf1.aestronglyMeasurable)
          (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hBj x z) (abs_nonneg _)
      · have hμ0 : μ j = 0 := le_antisymm (not_lt.mp hj) (hμ_nonneg j)
        simp [hμ0]
    have hinner_φ_ψ : ∀ j : ι, μ j * (∫ z, ψ j z * f z ∂P) = μ j * ⟪φ j, f⟫ := by
      intro j
      by_cases hj : 0 < μ j
      · congr 1
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [hφ_ae_ψ j] with z hz
        change ψ j z * f z = RCLike.re (f z * starRingEnd ℝ (φ j z))
        rw [RCLike.re_to_real, starRingEnd_apply, star_trivial, hz, mul_comm]
      · have hμ0 : μ j = 0 := le_antisymm (not_lt.mp hj) (hμ_nonneg j)
        simp [hμ0]
    have hR_int_eq : (∫ x, (∫ z, R x z * f z ∂P) * f x ∂P) =
        ⟪T f, f⟫ - ∑ j ∈ S, μ j * ⟪φ j, f⟫ ^ 2 := by
      have hK_z : ∀ x : X, Integrable (fun z => K x z * f z) P := fun x => by
        obtain ⟨M, _, hM⟩ := exists_nonneg_bound_kernel K hKcont
        refine (hf1.norm.const_mul M).mono'
          ((hKcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
            hf1.aestronglyMeasurable)
          (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hM x z) (abs_nonneg _)
      have hstep1 : ∀ x : X,
          (∫ z, R x z * f z ∂P) * f x =
            (∫ z, K x z * f z ∂P) * f x -
              ∑ j ∈ S, (μ j * ⟪φ j, f⟫) * (ψ j x * f x) := by
        intro x
        have hsub_fn : (fun z => R x z * f z) =
            fun z => K x z * f z - ∑ j ∈ S, (μ j * ψ j x * ψ j z * f z) := by
          funext z
          dsimp [R]
          rw [sub_mul, Finset.sum_mul]
        rw [hsub_fn, integral_sub (hK_z x) (integrable_finsetSum S fun j _ => hterm_int_z j x),
          integral_finsetSum S fun j _ => hterm_int_z j x, sub_mul, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have hpull : (∫ z, μ j * ψ j x * ψ j z * f z ∂P) =
            ψ j x * (μ j * ∫ z, ψ j z * f z ∂P) := by
          calc (∫ z, μ j * ψ j x * ψ j z * f z ∂P)
              = ∫ z, (μ j * ψ j x) * (ψ j z * f z) ∂P :=
                integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
            _ = (μ j * ψ j x) * ∫ z, ψ j z * f z ∂P := integral_const_mul _ _
            _ = ψ j x * (μ j * ∫ z, ψ j z * f z ∂P) := by ring
        rw [hpull, hinner_φ_ψ j]
        ring
      simp_rw [hstep1]
      have hKf_int : Integrable (fun x => (∫ z, K x z * f z ∂P) * f x) P := by
        have h1 : Integrable (fun x => intKernelCLM P K hKcont f x * f x) P := by
          obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
            (intKernelCLM P K hKcont f).continuous.continuousOn
          refine (hf1.norm.const_mul (max B 0)).mono'
            ((intKernelCLM P K hKcont f).continuous.aestronglyMeasurable.mul
              hf1.aestronglyMeasurable)
            (Filter.Eventually.of_forall fun x => ?_)
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          have hx : |intKernelCLM P K hKcont f x| ≤ max B 0 := by
            have h0 := hB x (Set.mem_univ _)
            rw [Real.norm_eq_abs] at h0
            exact h0.trans (le_max_left _ _)
          exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
        simpa only [intKernelCLM_apply] using h1
      have hsum_x_int : ∀ j ∈ S,
          Integrable (fun x => (μ j * ⟪φ j, f⟫) * (ψ j x * f x)) P := by
        intro j _
        by_cases hj : 0 < μ j
        · obtain ⟨Bj, hBj⟩ := isCompact_univ.exists_bound_of_continuousOn
            (hψ_cont j hj).continuousOn
          refine (hf1.norm.const_mul (|μ j * ⟪φ j, f⟫| * max Bj 0)).mono'
            (continuous_const.aestronglyMeasurable.mul
              ((hψ_cont j hj).aestronglyMeasurable.mul hf1.aestronglyMeasurable))
            (Filter.Eventually.of_forall fun x => ?_)
          rw [Real.norm_eq_abs, abs_mul (μ j * ⟪φ j, f⟫), abs_mul (ψ j x), Real.norm_eq_abs]
          have hx : |ψ j x| ≤ max Bj 0 := by
            have h0 := hBj x (Set.mem_univ _)
            rw [Real.norm_eq_abs] at h0
            exact h0.trans (le_max_left _ _)
          calc |μ j * ⟪φ j, f⟫| * (|ψ j x| * |f x|)
              ≤ |μ j * ⟪φ j, f⟫| * (max Bj 0 * |f x|) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hx (abs_nonneg _)) (abs_nonneg _)
            _ = |μ j * ⟪φ j, f⟫| * max Bj 0 * |f x| := by ring
        · have hμ0 : μ j = 0 := le_antisymm (not_lt.mp hj) (hμ_nonneg j)
          simp [hμ0]
      rw [integral_sub hKf_int (integrable_finsetSum S hsum_x_int),
        ← inner_tkCLM_eq_double_integral P K hKcont f f, integral_finsetSum S hsum_x_int]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      calc (∫ x, (μ j * ⟪φ j, f⟫) * (ψ j x * f x) ∂P)
          = ⟪φ j, f⟫ * (μ j * ∫ x, ψ j x * f x ∂P) := by
            rw [integral_const_mul]; ring
        _ = ⟪φ j, f⟫ * (μ j * ⟪φ j, f⟫) := by rw [hinner_φ_ψ j]
        _ = μ j * ⟪φ j, f⟫ ^ 2 := by ring
    rw [hR_int_eq, hTf_decomp]
    exact tkCLM_inner_self_nonneg P K hKcont hKpsd fS
  suffices hR0 : 0 ≤ R x₀ x₀ by
    dsimp [R] at hR0
    have hsq : ∑ j ∈ S, μ j * (ψ j x₀) ^ 2 = ∑ j ∈ S, μ j * ψ j x₀ * ψ j x₀ :=
      Finset.sum_congr rfl fun j _ => by ring
    linarith
  by_contra hneg
  push Not at hneg
  have hcont_at := hR_cont.continuousAt (x := (x₀, x₀))
  have hε : 0 < -R x₀ x₀ / 2 := by linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont_at (-R x₀ x₀ / 2) hε
  let B : Set X := Metric.ball x₀ δ
  have hB_meas : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hB_fin : P B ≠ ⊤ := measure_ne_top P B
  have hB_pos : 0 < P.real B := by
    rw [Measure.real_def]
    exact ENNReal.toReal_pos
      (Metric.isOpen_ball.measure_ne_zero P ⟨x₀, Metric.mem_ball_self hδ⟩) hB_fin
  let fB : Lp ℝ 2 P := indicatorConstLp 2 hB_meas hB_fin (1 : ℝ)
  have hfB_ae : (fB : X → ℝ) =ᵐ[P] B.indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn
  have hR_lt : ∀ x ∈ B, ∀ z ∈ B, R x z ≤ R x₀ x₀ / 2 := by
    intro x hx z hz
    have hp : dist (x, z) (x₀, x₀) < δ := by
      rw [Prod.dist_eq]
      exact max_lt hx hz
    have hd := hball hp
    rw [Real.dist_eq, abs_lt] at hd
    dsimp [Function.uncurry] at hd
    linarith
  have hint_B_le : (∫ x, (∫ z, R x z * fB z ∂P) * fB x ∂P) ≤
      (R x₀ x₀ / 2) * (P.real B) ^ 2 := by
    obtain ⟨MR, _, hMR⟩ := exists_nonneg_bound_kernel R hR_cont
    have hpoint_z : ∀ x : X,
        ∫ z, R x z * fB z ∂P = ∫ z in B, R x z ∂P := by
      intro x
      have hae : (fun z => R x z * fB z) =ᵐ[P] B.indicator (fun z => R x z) := by
        filter_upwards [hfB_ae] with z hz
        rw [hz]
        by_cases hzB : z ∈ B <;> simp [hzB]
      rw [integral_congr_ae hae, integral_indicator hB_meas]
    have houter_ae : (fun x => (∫ z, R x z * fB z ∂P) * fB x) =ᵐ[P]
        B.indicator (fun x => ∫ z in B, R x z ∂P) := by
      filter_upwards [hfB_ae] with x hx
      rw [hpoint_z x, hx]
      by_cases hxB : x ∈ B <;> simp [hxB]
    rw [integral_congr_ae houter_ae, integral_indicator hB_meas]
    have hinner_le : ∀ x ∈ B, (∫ z in B, R x z ∂P) ≤ (R x₀ x₀ / 2) * P.real B := by
      intro x hxB
      have hint_Rx : IntegrableOn (fun z => R x z) B P := by
        have hc : Continuous (fun z => R x z) :=
          hR_cont.comp (continuous_const.prodMk continuous_id)
        refine (integrable_const MR).mono' hc.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs]; exact hMR x z
      calc (∫ z in B, R x z ∂P)
          ≤ ∫ _z in B, (R x₀ x₀ / 2) ∂P :=
            setIntegral_mono_on hint_Rx (integrable_const _) hB_meas (fun z hz => hR_lt x hxB z hz)
        _ = (R x₀ x₀ / 2) * P.real B := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
    have hint_outer : IntegrableOn (fun x => ∫ z in B, R x z ∂P) B P := by
      rw [IntegrableOn]
      have hright := (integrable_kernel_prod (P.restrict B) R hR_cont
        (integrable_const 1) (integrable_const 1)).integral_prod_left
      simpa using hright
    calc (∫ x in B, (∫ z in B, R x z ∂P) ∂P)
        ≤ ∫ _x in B, ((R x₀ x₀ / 2) * P.real B) ∂P :=
          setIntegral_mono_on hint_outer (integrable_const _) hB_meas hinner_le
      _ = (R x₀ x₀ / 2) * (P.real B) ^ 2 := by
          rw [setIntegral_const, smul_eq_mul]
          ring
  have hge0 := hR_L2_nonneg fB
  have hneg_rhs : (R x₀ x₀ / 2) * (P.real B) ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (pow_pos hB_pos 2)
  linarith

lemma mercer_expansion_convergence {ι : Type*}
    (P : Measure X) [IsFiniteMeasure P] [P.IsOpenPosMeasure]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K))
    (φ : HilbertBasis ι ℝ (Lp ℝ 2 P)) (μ : ι → ℝ) (ψ : ι → X → ℝ)
    (hμ_nonneg : ∀ j : ι, 0 ≤ μ j)
    (hφ_ae_ψ : ∀ j : ι, (φ j : X → ℝ) =ᵐ[P] ψ j)
    (hinner_kx_φ : ∀ (j : ι) (x : X), ⟪φ j, kxLp P K hKcont x⟫ = μ j * ψ j x)
    (hterm_cont : ∀ j : ι, Continuous (fun p : X × X => μ j * ψ j p.1 * ψ j p.2))
    (hbessel_diag : ∀ (S : Finset ι) (x : X), ∑ j ∈ S, μ j * (ψ j x) ^ 2 ≤ K x x) :
    (∀ e : ℕ ≃ ι, TendstoUniformly (fun n : ℕ => fun p : X × X =>
        ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2)
      (Function.uncurry K) Filter.atTop) ∧
    (∀ x z : X, HasSum (fun j => μ j * ψ j x * ψ j z) (K x z)) := by
  obtain ⟨M₀, _, hM₀⟩ := exists_nonneg_bound_kernel K hKcont
  have hdiag_le_M₀ : ∀ (S : Finset ι) (z : X),
      ∑ j ∈ S, μ j * (ψ j z) ^ 2 ≤ M₀ := fun S z =>
    (hbessel_diag S z).trans ((le_abs_self _).trans (hM₀ z z))
  have hsum_diag_summable : ∀ x : X, Summable (fun j : ι => μ j * (ψ j x) ^ 2) := fun x =>
    summable_of_sum_le (fun j => mul_nonneg (hμ_nonneg j) (sq_nonneg _))
      (fun S => hdiag_le_M₀ S x)
  have hcs_finset : ∀ (T : Finset ι) (x z : X),
      |∑ j ∈ T, μ j * ψ j x * ψ j z| ≤
        Real.sqrt (∑ j ∈ T, μ j * (ψ j x) ^ 2) *
          Real.sqrt (∑ j ∈ T, μ j * (ψ j z) ^ 2) := by
    intro T x z
    have hrewrite : ∑ j ∈ T, μ j * ψ j x * ψ j z =
        ∑ j ∈ T, (Real.sqrt (μ j) * ψ j x) * (Real.sqrt (μ j) * ψ j z) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsq : Real.sqrt (μ j) * Real.sqrt (μ j) = μ j := Real.mul_self_sqrt (hμ_nonneg j)
      calc μ j * ψ j x * ψ j z
          = (Real.sqrt (μ j) * Real.sqrt (μ j)) * ψ j x * ψ j z := by rw [hsq]
        _ = (Real.sqrt (μ j) * ψ j x) * (Real.sqrt (μ j) * ψ j z) := by ring
    have hsq_le := Finset.sum_mul_sq_le_sq_mul_sq T
      (fun j => Real.sqrt (μ j) * ψ j x) (fun j => Real.sqrt (μ j) * ψ j z)
    have hfx : ∑ j ∈ T, (Real.sqrt (μ j) * ψ j x) ^ 2 = ∑ j ∈ T, μ j * (ψ j x) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (hμ_nonneg j)]
    have hfz : ∑ j ∈ T, (Real.sqrt (μ j) * ψ j z) ^ 2 = ∑ j ∈ T, μ j * (ψ j z) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (hμ_nonneg j)]
    rw [← hrewrite, hfx, hfz] at hsq_le
    have hsqrt := Real.sqrt_le_sqrt hsq_le
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_mul
      (Finset.sum_nonneg fun j _ => mul_nonneg (hμ_nonneg j) (sq_nonneg _))] at hsqrt
  let termBCF (x : X) (j : ι) : X →ᵇ ℝ :=
    mkOfCompact ⟨fun z => μ j * ψ j x * ψ j z,
      (hterm_cont j).comp (continuous_const.prodMk continuous_id)⟩
  have htermBCF_summable : ∀ x : X, Summable (termBCF x) := by
    intro x
    rw [summable_iff_vanishing_norm]
    intro ε hε
    let δ : ℝ := (ε / (Real.sqrt M₀ + 1)) ^ 2
    have hδ_pos : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp (hsum_diag_summable x) δ hδ_pos
    refine ⟨s, fun t hts => ?_⟩
    have hsum_t : ∑ j ∈ t, μ j * (ψ j x) ^ 2 < δ := by
      have hn := hs t hts
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Finset.sum_nonneg fun j _ => mul_nonneg (hμ_nonneg j) (sq_nonneg _))] at hn
      exact hn
    have hnorm_le : ‖∑ j ∈ t, termBCF x j‖ ≤
        Real.sqrt (∑ j ∈ t, μ j * (ψ j x) ^ 2) * Real.sqrt M₀ := by
      refine (BoundedContinuousFunction.norm_le
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr fun z => ?_
      have happly : (∑ j ∈ t, termBCF x j) z = ∑ j ∈ t, μ j * ψ j x * ψ j z := by
        simp [termBCF]
      rw [Real.norm_eq_abs, happly]
      exact (hcs_finset t x z).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hdiag_le_M₀ t z)) (Real.sqrt_nonneg _))
    have hsqrt_lt : Real.sqrt (∑ j ∈ t, μ j * (ψ j x) ^ 2) < ε / (Real.sqrt M₀ + 1) := by
      have h1 := Real.sqrt_lt_sqrt
        (Finset.sum_nonneg fun j _ => mul_nonneg (hμ_nonneg j) (sq_nonneg _)) hsum_t
      have h2 : Real.sqrt δ = ε / (Real.sqrt M₀ + 1) :=
        Real.sqrt_sq (by positivity)
      rwa [h2] at h1
    calc ‖∑ j ∈ t, termBCF x j‖
        ≤ Real.sqrt (∑ j ∈ t, μ j * (ψ j x) ^ 2) * Real.sqrt M₀ := hnorm_le
      _ ≤ Real.sqrt (∑ j ∈ t, μ j * (ψ j x) ^ 2) * (Real.sqrt M₀ + 1) := by
            have := Real.sqrt_nonneg (∑ j ∈ t, μ j * (ψ j x) ^ 2)
            linarith
      _ < (ε / (Real.sqrt M₀ + 1)) * (Real.sqrt M₀ + 1) :=
            mul_lt_mul_of_pos_right hsqrt_lt (by positivity)
      _ = ε := div_mul_cancel₀ ε (by positivity)
  have hhasSum_bcf : ∀ x : X, HasSum (termBCF x) (kxBCF K hKcont x) := by
    intro x
    have hsum_x := (htermBCF_summable x).hasSum
    have hL := (BoundedContinuousFunction.toLp 2 P ℝ).hasSum hsum_x
    have hterm_lp : ∀ j : ι,
        BoundedContinuousFunction.toLp 2 P ℝ (termBCF x j) =
          (φ.repr (kxLp P K hKcont x) j) • φ j := by
      intro j
      rw [φ.repr_apply_apply, hinner_kx_φ j x, Lp.ext_iff]
      have h1 := BoundedContinuousFunction.coeFn_toLp 2 P ℝ (termBCF x j)
      have h2 := Lp.coeFn_smul (μ j * ψ j x) (φ j)
      filter_upwards [h1, h2, hφ_ae_ψ j] with z hz1 hz2 hz3
      rw [hz1, hz2, Pi.smul_apply, smul_eq_mul, hz3]
      rfl
    simp_rw [hterm_lp] at hL
    have hrepr := φ.hasSum_repr (kxLp P K hKcont x)
    have hlp_eq : BoundedContinuousFunction.toLp 2 P ℝ (∑' j, termBCF x j) =
        BoundedContinuousFunction.toLp 2 P ℝ (kxBCF K hKcont x) :=
      hL.unique hrepr
    have hbcf_eq : (∑' j, termBCF x j) = kxBCF K hKcont x :=
      (BoundedContinuousFunction.toLp_inj P (E := ℝ) (p := 2) (𝕜 := ℝ)).mp hlp_eq
    rwa [hbcf_eq] at hsum_x
  have hhasSum_pt : ∀ x z : X, HasSum (fun j => μ j * ψ j x * ψ j z) (K x z) := by
    intro x z
    simpa [termBCF] using (BoundedContinuousFunction.evalCLM ℝ z).hasSum (hhasSum_bcf x)
  refine ⟨fun e => ?_, hhasSum_pt⟩
  let D : ℕ → X → ℝ := fun n x =>
    ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) x * ψ (e k) x
  have hD_cont : ∀ n : ℕ, Continuous (D n) := fun n =>
    continuous_finsetSum _ fun k _ =>
      (hterm_cont (e k)).comp (continuous_id.prodMk continuous_id)
  have hD_mono : Monotone D := by
    intro m n hmn x
    dsimp [D]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) fun k _ _ => ?_
    have hsq : μ (e k) * ψ (e k) x * ψ (e k) x = μ (e k) * (ψ (e k) x) ^ 2 := by ring
    rw [hsq]
    exact mul_nonneg (hμ_nonneg (e k)) (sq_nonneg _)
  have hKdiag_cont : Continuous (fun x : X => K x x) :=
    hKcont.comp (continuous_id.prodMk continuous_id)
  have hpt_range : ∀ x z : X,
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) x * ψ (e k) z)
        atTop (𝓝 (K x z)) := by
    intro x z
    have hcomp : HasSum (fun k : ℕ => μ (e k) * ψ (e k) x * ψ (e k) z) (K x z) :=
      e.hasSum_iff.mpr (hhasSum_pt x z)
    exact hcomp.tendsto_sum_nat
  have hD_unif : TendstoUniformly D (fun x : X => K x x) atTop :=
    hD_mono.tendstoUniformly_of_forall_tendsto hD_cont hKdiag_cont (fun x => hpt_range x x)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let η : ℝ := (ε / (2 * (Real.sqrt M₀ + 1))) ^ 2
  have hη_pos : 0 < η := by dsimp [η]; positivity
  have hev := Metric.tendstoUniformly_iff.mp hD_unif η hη_pos
  filter_upwards [hev] with n hn
  intro p
  have htail_le : ∀ m : ℕ, n ≤ m →
      |(∑ k ∈ Finset.range m, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2) -
        (∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2)| ≤
        Real.sqrt (D m p.1 - D n p.1) * Real.sqrt M₀ := by
    intro m hnm
    rw [← Finset.sum_Ico_eq_sub _ hnm]
    have hmap : ∑ k ∈ Finset.Ico n m, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2 =
        ∑ j ∈ (Finset.Ico n m).map e.toEmbedding, μ j * ψ j p.1 * ψ j p.2 := by
      rw [Finset.sum_map]; rfl
    have hmap_x : ∑ j ∈ (Finset.Ico n m).map e.toEmbedding, μ j * (ψ j p.1) ^ 2 =
        D m p.1 - D n p.1 := by
      rw [Finset.sum_map]
      dsimp [D]
      rw [← Finset.sum_Ico_eq_sub _ hnm]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hmap]
    calc |∑ j ∈ (Finset.Ico n m).map e.toEmbedding, μ j * ψ j p.1 * ψ j p.2|
        ≤ Real.sqrt (∑ j ∈ (Finset.Ico n m).map e.toEmbedding, μ j * (ψ j p.1) ^ 2) *
            Real.sqrt (∑ j ∈ (Finset.Ico n m).map e.toEmbedding, μ j * (ψ j p.2) ^ 2) :=
          hcs_finset _ p.1 p.2
      _ ≤ Real.sqrt (D m p.1 - D n p.1) * Real.sqrt M₀ := by
          rw [hmap_x]
          exact mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (hdiag_le_M₀ _ p.2)) (Real.sqrt_nonneg _)
  have htend_lhs : Tendsto
      (fun m : ℕ => |(∑ k ∈ Finset.range m, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2) -
        (∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2)|)
      atTop (𝓝 |(K p.1 p.2 - ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2)|) :=
    ((hpt_range p.1 p.2).sub tendsto_const_nhds).abs
  have htend_rhs : Tendsto
      (fun m : ℕ => Real.sqrt (D m p.1 - D n p.1) * Real.sqrt M₀)
      atTop (𝓝 (Real.sqrt (K p.1 p.1 - D n p.1) * Real.sqrt M₀)) :=
    (((hpt_range p.1 p.1).sub tendsto_const_nhds).sqrt).mul tendsto_const_nhds
  have hlim_le :
      |K p.1 p.2 - ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2| ≤
        Real.sqrt (K p.1 p.1 - D n p.1) * Real.sqrt M₀ :=
    le_of_tendsto_of_tendsto htend_lhs htend_rhs (eventually_ge_atTop n |>.mono htail_le)
  have hD_gap_lt : K p.1 p.1 - D n p.1 < η := by
    have hd := hn p.1
    rw [Real.dist_eq] at hd
    exact (le_abs_self _).trans_lt hd
  have hD_gap_nonneg : 0 ≤ K p.1 p.1 - D n p.1 := by
    have hle : D n p.1 ≤ K p.1 p.1 :=
      ge_of_tendsto (hpt_range p.1 p.1)
        (eventually_ge_atTop n |>.mono fun m hnm => hD_mono hnm p.1)
    linarith
  have hsqrt_lt : Real.sqrt (K p.1 p.1 - D n p.1) < ε / (2 * (Real.sqrt M₀ + 1)) := by
    have h1 := Real.sqrt_lt_sqrt hD_gap_nonneg hD_gap_lt
    have h2 : Real.sqrt η = ε / (2 * (Real.sqrt M₀ + 1)) := Real.sqrt_sq (by positivity)
    rwa [h2] at h1
  rw [Real.dist_eq]
  calc |Function.uncurry K p - ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2|
      ≤ Real.sqrt (K p.1 p.1 - D n p.1) * Real.sqrt M₀ := hlim_le
    _ ≤ Real.sqrt (K p.1 p.1 - D n p.1) * (Real.sqrt M₀ + 1) := by
          have := Real.sqrt_nonneg (K p.1 p.1 - D n p.1)
          linarith
    _ < (ε / (2 * (Real.sqrt M₀ + 1))) * (Real.sqrt M₀ + 1) :=
          mul_lt_mul_of_pos_right hsqrt_lt (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

end KernelOperator

end

end MercerProof

open MercerProof

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (P : Measure X) [IsFiniteMeasure P] [P.IsOpenPosMeasure]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (hKpsd : IsPSDKernel K)
    (_hHS : Integrable (fun p : X × X => (K p.1 p.2) ^ 2) (P.prod P))
    (TK : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P)
    (hTK : ∀ f : Lp ℝ 2 P, (TK f : X → ℝ) =ᵐ[P] fun x => ∫ z, K x z * (f z) ∂P) :
    ∃ (ι : Type) (_ : Countable ι) (φ : HilbertBasis ι ℝ (Lp ℝ 2 P)) (μ : ι → ℝ)
      (ψ : ι → X → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j, TK (φ j) = μ j • (φ j : Lp ℝ 2 P)) ∧
      (∀ j, (φ j : X → ℝ) =ᵐ[P] ψ j) ∧
      (∀ j, 0 < μ j → Continuous (ψ j)) ∧
      (∀ e : ℕ ≃ ι, TendstoUniformly (fun n : ℕ => fun p : X × X =>
          ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2)
        (Function.uncurry K) Filter.atTop) ∧
      (∀ x z, HasSum (fun j => μ j * ψ j x * ψ j z) (K x z)) := by
  let T : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P := tkCLM P K hKcont
  have hT_eq : ∀ f : Lp ℝ 2 P, T f = TK f := tkCLM_eq_TK P K hKcont TK hTK
  have hT_comp : IsCompactOperator T := isCompactOperator_tkCLM P K hKcont
  have hT_sym : (T : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P).IsSymmetric :=
    tkCLM_isSymmetric P K hKcont hKpsd.1
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨ι, hι_count, φ, μ, hφ_eig⟩ :=
    HighDimStat.Rkhs.exists_countable_hilbertBasis_eigenvectors T hT_comp hT_sym
  have : Countable ι := hι_count
  classical
  have hTK_eig : ∀ j : ι, TK (φ j) = μ j • (φ j : Lp ℝ 2 P) := fun j => by
    rw [← hT_eq, hφ_eig j]
  have hμ_nonneg : ∀ j : ι, 0 ≤ μ j := fun j => by
    have hnn := tkCLM_inner_self_nonneg P K hKcont hKpsd (φ j)
    change 0 ≤ ⟪T (φ j), φ j⟫ at hnn
    rw [hφ_eig j, inner_smul_left, RCLike.conj_to_real,
      real_inner_self_eq_norm_mul_norm, φ.orthonormal.1 j, mul_one, mul_one] at hnn
    exact hnn
  let ψ : ι → X → ℝ := fun j x =>
    if 0 < μ j then (μ j)⁻¹ * intKernelCLM P K hKcont (φ j) x else φ j x
  have hψ_cont : ∀ j : ι, 0 < μ j → Continuous (ψ j) := by
    intro j hj
    have heq : ψ j = fun x => (μ j)⁻¹ * intKernelCLM P K hKcont (φ j) x := by
      funext x; simp [ψ, hj]
    rw [heq]
    exact continuous_const.mul (intKernelCLM P K hKcont (φ j)).continuous
  have hφ_ae_ψ : ∀ j : ι, (φ j : X → ℝ) =ᵐ[P] ψ j := by
    intro j
    by_cases hj : 0 < μ j
    · have h1 : (TK (φ j) : X → ℝ) =ᵐ[P] fun x => μ j * φ j x := by
        rw [hTK_eig j]
        exact Lp.coeFn_smul (μ j) (φ j)
      have h2 := (h1.symm.trans (hTK (φ j)))
      filter_upwards [h2] with x hx
      simp only [ψ, if_pos hj]
      rw [intKernelCLM_apply, ← hx, inv_mul_cancel_left₀ hj.ne']
    · have heq : ψ j = fun x => φ j x := by funext x; simp [ψ, hj]
      rw [heq]
  have hinner_kx_φ : ∀ (j : ι) (x : X),
      ⟪φ j, kxLp P K hKcont x⟫ = μ j * ψ j x := by
    intro j x
    rw [real_inner_comm, inner_kxLp_eq, ← intKernelCLM_apply]
    by_cases hj : 0 < μ j
    · simp only [ψ, if_pos hj]
      exact (mul_inv_cancel_left₀ hj.ne' _).symm
    · have hμ0 : μ j = 0 := le_antisymm (not_lt.mp hj) (hμ_nonneg j)
      rw [hμ0, zero_mul]
      have hT0 : T (φ j) = 0 := by rw [hφ_eig j, hμ0, zero_smul]
      have hinj : intKernelCLM P K hKcont (φ j) = 0 := by
        apply (BoundedContinuousFunction.toLp_inj P (E := ℝ) (p := 2) (𝕜 := ℝ)).mp
        simpa [T, tkCLM] using hT0
      rw [hinj]; rfl
  have hterm_cont : ∀ j : ι, Continuous (fun p : X × X => μ j * ψ j p.1 * ψ j p.2) := by
    intro j
    by_cases hj : 0 < μ j
    · exact ((continuous_const.mul ((hψ_cont j hj).comp continuous_fst)).mul
        ((hψ_cont j hj).comp continuous_snd))
    · have hμ0 : μ j = 0 := le_antisymm (not_lt.mp hj) (hμ_nonneg j)
      have heq : (fun p : X × X => μ j * ψ j p.1 * ψ j p.2) = fun _ => 0 := by
        funext p; simp [hμ0]
      rw [heq]; exact continuous_const
  have hbessel_diag : ∀ (S : Finset ι) (x : X), ∑ j ∈ S, μ j * (ψ j x) ^ 2 ≤ K x x :=
    bessel_diag_le P K hKcont hKpsd φ μ ψ hφ_eig hμ_nonneg hψ_cont hφ_ae_ψ hterm_cont
  obtain ⟨htendsto_unif, hhasSum_pt⟩ :=
    mercer_expansion_convergence P K hKcont φ μ ψ hμ_nonneg hφ_ae_ψ
      hinner_kx_φ hterm_cont hbessel_diag
  exact ⟨ι, hι_count, φ, μ, ψ, hμ_nonneg, hTK_eig, hφ_ae_ψ, hψ_cont, htendsto_unif, hhasSum_pt⟩
