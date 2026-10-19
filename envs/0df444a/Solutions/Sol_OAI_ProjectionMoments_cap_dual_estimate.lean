-- Prove2me | solution 1 for OAI.ProjectionMoments.cap_dual_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:05:33.115171+00:00
-- url     : https://prove2.me/submissions/ecdb154d-2b5d-4065-89e5-94df965ce933

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/CapDuality.lean:L161-L215
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.cap_dual_estimate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Theorems.Thm_OAI_NoiselessRegression_ae_pi_snoc
import Theorems.Thm_OAI_ProjectionMoments_capTest_allBall
import Theorems.Thm_OAI_ProjectionMoments_normalizedDensity_unitBall
import Theorems.Thm_OAI_ProjectionMoments_normalized_unitBall_moment
import Theorems.Thm_OAI_ProjectionMoments_rescaled_projection_ac
import Theorems.Thm_OAI_ProjectionMoments_sphere_frame_ac

-- ---- from OAI.Probability.GaussianRegression.Gram ----
namespace OAI

/-!
Gram determinants, orthogonal distances, and product integration.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
lemma gram_linear_combination (w : ι → E) (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, (T i j) • w i) =
      T.transpose * Matrix.gram ℝ w * T := by
  ext a b
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  congr 1
  ext j
  congr 1
  ext i
  ring

variable (n : ℕ)
lemma gsUpper_expansion (v : Fin n → E) (j : Fin n) :
    ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i = v j := by
  simp only [gsUpper, add_smul, Finset.sum_add_distrib]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs => rw [gramSchmidt_def'' ℝ v j]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

lemma gsUpper_det (v : Fin n → E) : (gsUpper n v).det = 1 := by
  have htri : (gsUpper n v).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [gsUpper, (ne_of_gt hij), (not_lt_of_ge hij.le)]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gsUpper]

lemma gram_gramSchmidt_diagonal (v : Fin n → E) :
    Matrix.gram ℝ (gramSchmidt ℝ v) = Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖ ^ 2) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.gram_apply]
  · simp [Matrix.gram_apply, hij,
      gramSchmidt_orthogonal ℝ v hij]

theorem det_gram_eq_prod_gramSchmidt (v : Fin n → E) :
    (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  have hv : (fun j => ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i) = v :=
    funext (gsUpper_expansion n v)
  have h := gram_linear_combination (gramSchmidt ℝ v) (gsUpper n v)
  rw [hv] at h
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, gsUpper_det,
    one_mul, mul_one, gram_gramSchmidt_diagonal, Matrix.det_diagonal]
end GramFactorization

section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
omit [FiniteDimensional ℝ E] in
lemma sub_gramSchmidt_mem_span (v : Fin n → E) (j : Fin n) :
    v j - gramSchmidt ℝ v j ∈ Submodule.span ℝ (v '' Set.Iio j) := by
  rw [← span_gramSchmidt_Iio ℝ v j]
  conv => arg 2; lhs; rw [gramSchmidt_def'' ℝ v j]
  rw [add_sub_cancel_left]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

omit [FiniteDimensional ℝ E] in
lemma gramSchmidt_mem_span_orthogonal (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j ∈ (Submodule.span ℝ (v '' Set.Iio j))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, hi, rfl⟩
    exact gramSchmidt_inv_triangular ℝ v hi
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul c x _ hx => simp [inner_smul_right, hx]

lemma gramSchmidt_eq_sub_starProjection (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j = v j -
      (Submodule.span ℝ (v '' Set.Iio j)).starProjection (v j) := by
  have h := (Submodule.span ℝ (v '' Set.Iio j)).eq_starProjection_of_mem_orthogonal
    (u := v j) (sub_gramSchmidt_mem_span v j)
    (by simpa using gramSchmidt_mem_span_orthogonal v j)
  rw [h, sub_sub_cancel]

lemma norm_gramSchmidt_eq_infDist (v : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ v j‖ = Metric.infDist (v j)
      (Submodule.span ℝ (v '' Set.Iio j) : Set E) := by
  rw [gramSchmidt_eq_sub_starProjection, Submodule.starProjection_minimal,
    Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    v '' Set.Iio j.castSucc = (fun i => v i.castSucc) '' Set.Iio j := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i.val < n := lt_trans hi j.isLt
    exact ⟨⟨i.val, hin⟩, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, hi, rfl⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_last (v : Fin (n+1) → E) :
    v '' Set.Iio (Fin.last n) = Set.range (fun i : Fin n => v i.castSucc) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, i.isLt, rfl⟩

lemma gramSchmidt_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    gramSchmidt ℝ v j.castSucc = gramSchmidt ℝ (fun i => v i.castSucc) j := by
  rw [gramSchmidt_eq_sub_starProjection, gramSchmidt_eq_sub_starProjection,
    image_Iio_castSucc]

variable [MeasurableSpace E] [BorelSpace E]
lemma measurable_gramSchmidt (j : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidt ℝ v j) := by
  refine (wellFounded_lt : WellFounded ((· < ·) : Fin n → Fin n → Prop)).induction
    (C := fun j : Fin n => Measurable (fun v : Fin n → E => gramSchmidt ℝ v j)) j ?_
  intro j ih
  have heq : (fun v : Fin n → E => gramSchmidt ℝ v j) =
      fun v => v j - ∑ i ∈ Finset.Iio j,
        (⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2) • gramSchmidt ℝ v i := by
    ext v
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton]
    rfl
  rw [heq]
  apply (measurable_pi_apply j).sub
  apply Finset.measurable_sum
  intro i hi
  have hi' := ih i (Finset.mem_Iio.mp hi)
  exact ((hi'.inner (measurable_pi_apply j)).div (hi'.norm.pow_const 2)).smul hi'
end GramDistances

variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.ReplicaMoments ----
namespace OAI

/-!
Inverse Gram moments and almost-everywhere replica independence.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ReplicaMoments
section AePiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
end AePiLast

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurableSet_gramSchmidt_ne_zero (p : E) (n : ℕ) :
    MeasurableSet {v : Fin n → E | ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have h := (measurable_gramSchmidt i).comp
    (show Measurable (fun v : Fin n → E => fun j => v j - p) by fun_prop)
  exact (measurableSet_eq_fun h measurable_const).compl

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.GaussianKernel ----
namespace OAI

/-!
Gaussian coordinate domination and replica kernel bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussianReal_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  conv_rhs => rw [← withDensity_one (μ := (volume : Measure ℝ))]
  apply withDensity_mono
  filter_upwards [] with x
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) ≤ 1
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) := by
    norm_num only [NNReal.coe_one, mul_one]
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have he : Real.exp (-(x - 0)^2 / (2 * (1 : ℝ≥0))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact (mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hs)).trans he
lemma measure_pi_mono {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {μ ν : ∀ i, Measure (X i)}
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have ho : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    exact (OuterMeasure.pi_pi_le _ s).trans (Finset.prod_le_prod (fun _ _ => zero_le) fun i _ => h i (s i))
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi_def, Measure.pi_def, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  exact ho s

lemma pi_gaussianReal_le_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≤ (volume : Measure (Fin n → ℝ)) :=
  measure_pi_mono (fun _ => gaussianReal_le_volume)
end GaussianDomination

section ReplicaKernel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ReplicaKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Graph ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

section GaussianGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianGraph

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dilate_rescale (z : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    dilate z R (rescale z R x) = x := by
  simp [dilate, rescale, smul_smul, hR]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rescale_preimage_closedBall (z b : E) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    rescale z R ⁻¹' Metric.closedBall b t = Metric.closedBall (dilate z R b) (R*t) := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have he : rescale z R x - b = R⁻¹ • (x - dilate z R b) := by
    simp [rescale, dilate, smul_sub, smul_add, smul_smul, hR.ne', sub_sub, add_comm]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  rw [inv_mul_le_iff₀ hR]

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.GaussianDensity ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_le_volume : stdGaussian E ≤ volume := by
  let b := stdOrthonormalBasis ℝ E
  have hp : MeasurePreserving (fun x : Fin (Module.finrank ℝ E) → ℝ =>
      ∑ i, x i • b i) (volume : Measure (Fin (Module.finrank ℝ E) → ℝ)) volume := by
    have he : (fun x : Fin (Module.finrank ℝ E) → ℝ => ∑ i, x i • b i) =
        (fun x => b.repr.symm (WithLp.toLp 2 x)) := by
      funext x
      exact b.sum_repr_symm (WithLp.toLp 2 x)
    rw [he]
    exact b.measurePreserving_repr_symm.comp
      (PiLp.volume_preserving_toLp (Fin (Module.finrank ℝ E)))
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, ← hp.map_eq]
  exact Measure.map_mono (NoiselessRegression.pi_gaussianReal_le_volume _) hp.measurable

lemma stdGaussian_submodule_null (S : Submodule ℝ E) (hS : S ≠ ⊤) :
    stdGaussian E S = 0 := by
  apply le_antisymm _ zero_le
  exact (stdGaussian_le_volume (E := E) S).trans_eq (Measure.addHaar_submodule volume S hS)

lemma gaussian_rows_ae_gramSchmidt_ne_zero (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∀ᵐ A : Fin m → E ∂Measure.pi (fun _ => stdGaussian E), ∀ i, gramSchmidt ℝ A i ≠ 0 := by
  induction m with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ m ih =>
    rw [NoiselessRegression.ae_pi_snoc _ (by
      simpa only [sub_zero] using NoiselessRegression.measurableSet_gramSchmidt_ne_zero (0 : E) (m+1))]
    filter_upwards [ih (by omega)] with v hv
    let S := Submodule.span ℝ (Set.range v)
    have hd : Module.finrank ℝ S ≤ m := by
      simpa only [S, Fintype.card_fin, Set.finrank] using finrank_range_le_card (R := ℝ) v
    have hs : S ≠ ⊤ := by
      intro he
      rw [he, finrank_top] at hd
      omega
    have ha : ∀ᵐ x ∂stdGaussian E, x ∉ S := by
      rw [ae_iff]
      convert stdGaussian_submodule_null S hs using 2
      ext x
      simp
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [NoiselessRegression.norm_gramSchmidt_eq_infDist,
        NoiselessRegression.image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((S.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨0, S.zero_mem⟩).mp hx)
    | cast j => simpa only [NoiselessRegression.gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

lemma gaussian_rows_ae_linearIndependent (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∀ᵐ A : Fin m → E ∂Measure.pi (fun _ => stdGaussian E), LinearIndependent ℝ A := by
  filter_upwards [gaussian_rows_ae_gramSchmidt_ne_zero m hm] with A hA
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [NoiselessRegression.det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hA i))

end

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Frames ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
attribute [fun_prop] measurable_lowerDensity

section Rotations
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {E}

variable [MeasurableSpace E] [BorelSpace E]

end Rotations

section Triangular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Triangular

section CoordinateDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_eq_toLp_coordinateMap [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) :
    (rowMap A : E → Label m) = (WithLp.toLp 2) ∘ coordinateMap A := rfl

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Polar ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixRows_mul [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M N : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) :
    mixRows (M*N) X = mixRows M (mixRows N X) := by
  ext i
  simp only [mixRows, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gram_mixRows [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) :
    Matrix.gram ℝ (mixRows M X) = M * Matrix.gram ℝ X * M.transpose := by
  ext i j
  simp only [Matrix.gram_apply, mixRows, inner_sum, sum_inner, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_squared [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) :
    polarRadial X * polarRadial X = Matrix.gram ℝ X :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_gram ℝ X).nonneg

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_pos [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) : 0 ≤ polarRadial X := CFC.sqrt_nonneg _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_isUnit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    IsUnit (polarRadial X) :=
  (CFC.isUnit_sqrt_iff _ (Matrix.posSemidef_gram ℝ X).nonneg).mpr
    (Matrix.posDef_gram_iff_linearIndependent.mpr hX).isUnit

lemma rawPolarRows_orthonormal {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    Orthonormal ℝ (rawPolarRows X) := by
  have hH := polarRadial_isUnit hX
  have hdet : IsUnit (polarRadial X).det := (Matrix.isUnit_iff_isUnit_det _).mp hH
  have hsym : (polarRadial X)⁻¹.transpose = (polarRadial X)⁻¹ := by
    have hh : (polarRadial X).IsHermitian := (polarRadial_pos X).isSelfAdjoint
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh.inv
  have hgram : Matrix.gram ℝ (rawPolarRows X) = 1 := by
    rw [rawPolarRows, gram_mixRows, hsym, ← polarRadial_squared,
      ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul, Matrix.mul_nonsing_inv _ hdet]
  apply orthonormal_iff_ite.mpr
  intro i j
  simpa only [Matrix.gram_apply, Matrix.one_apply] using congrFun (congrFun hgram i) j

lemma polar_reconstruction {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    mixRows (polarRadial X) (rawPolarRows X) = X := by
  rw [rawPolarRows, ← mixRows_mul, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (polarRadial_isUnit hX)), mixRows_one]

lemma polarRows_orthonormal {k : ℕ} {u : Fin k → E} (hu : Orthonormal ℝ u)
    (X : Fin k → E) : Orthonormal ℝ (polarRows u X) := by
  by_cases hX : LinearIndependent ℝ X
  · simpa only [polarRows, ite_eq_left hX] using rawPolarRows_orthonormal hX
  · simpa only [polarRows, ite_eq_right hX] using hu

end

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.BallMoments ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_polarRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rowMap_ac_iff {ν : Measure E} {k : ℕ} (A : Fin k → E) :
    ν.map (rowMap A) ≪ (volume : Measure (Label k)) ↔
      ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  constructor
  · intro h
    have hh := h.map (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm.measurable
    rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k)).map_eq,
      Measure.map_map (by fun_prop) (by fun_prop)] at hh
    exact hh
  · intro h
    rw [rowMap_eq_toLp_coordinateMap, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← (PiLp.volume_preserving_toLp (Fin k)).map_eq]
    exact h.map (by fun_prop)

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Caps ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma capMeasure_ac (c : E) (r : ℝ) : capMeasure c r ≪ NoiselessRegression.ambientSphereLaw :=
  Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict

lemma capMeasure_support (c : E) (r : ℝ) : (capMeasure c r).support ⊆ Metric.closedBall c r := by
  intro x hx
  have hh := (Measure.support_restrict_subset
    (Measure.smul_absolutelyContinuous.support_mono hx)).1
  simpa only [Metric.isClosed_closedBall.closure_eq] using hh

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.CapTests ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma capTestMeasure_mass {h : E → ℝ≥0∞} {c : E} {r α : ℝ} (hr : 0 < r)
    (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    capTestMeasure h c r Set.univ ≤ 1 := by
  have hp := hdual D.parent
  rw [D.parent_center,D.parent_radius,div_self hr.ne',Real.one_rpow,ENNReal.ofReal_one] at hp
  simpa only [capTestMeasure,Measure.map_apply (measurable_rescale c r) MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hp

lemma capTestMeasure_finite {h : E → ℝ≥0∞} {c : E} {r α : ℝ} (hr : 0 < r)
    (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    IsFiniteMeasure (capTestMeasure h c r) :=
  ⟨(capTestMeasure_mass hr D hdual).trans_lt (by simp)⟩

lemma capTestMeasure_support (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r) :
    (capTestMeasure h c r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  apply (ae_map_iff (measurable_rescale c r).aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
  filter_upwards [((capMeasure c r).withDensity h).support_mem_ae] with x hx
  have hx' := capMeasure_support c r ((withDensity_absolutelyContinuous (capMeasure c r) h).support_mono hx)
  change x ∈ rescale c r ⁻¹' Metric.closedBall 0 1
  rw [rescale_preimage_closedBall c 0 hr, dilate, smul_zero, zero_add, mul_one]
  exact hx'

lemma capTest_frame_ac [Nontrivial E] (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r)
    {k : ℕ} (hk : k+2 ≤ Module.finrank ℝ E) (A : Fin k → E) (hA : Orthonormal ℝ A) :
    (capTestMeasure h c r).map (rowMap A) ≪ (volume : Measure (Label k)) := by
  apply (rowMap_ac_iff _).mpr
  apply rescaled_projection_ac A c hr
  have hh := (((withDensity_absolutelyContinuous (capMeasure c r) h).trans (capMeasure_ac c r)).map
    (show Measurable (coordinateMap A) by fun_prop)).trans (sphere_frame_ac hk hA)
  exact hh

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.CapDuality ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_mixRows [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) (s : E) :
    rowMap (mixRows M X) s = WithLp.toLp 2 (M *ᵥ (rowMap X s).ofLp) := by
  ext i
  simp [rowMap, mixRows, Matrix.mulVec, dotProduct]

lemma polar_label_identity {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X)
    (u : Fin k → E) (c s : E) (r : ℝ) :
    rowMap X (dilate c r s) = rowMap X c + r • radialLabel X (rowMap (polarRows u X) s) := by
  have he : radialLabel X (rowMap (polarRows u X) s) = rowMap X s := by
    rw [radialLabel, ← rowMap_mixRows]
    simp only [polarRows, ite_eq_left hX, polar_reconstruction hX]
  rw [he, dilate, map_add, map_smul]
  exact add_comm _ _

lemma cap_kernel_test_identity {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {K : (Fin k → E) × Label k → ℝ≥0∞} (hK : Measurable K)
    (h : E → ℝ≥0∞) (hh : Measurable h) (c : E) {r : ℝ} (hr : 0 < r)
    {u : Fin k → E} (hu : Orthonormal ℝ u)
    [IsFiniteMeasure ((capMeasure c r).withDensity h)]
    (hac : ∀ X, (capTestMeasure h c r).map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k))) :
    (∫⁻ s, h s * capKernelValue K s ∂capMeasure c r) =
      ∫⁻ X, ∫⁻ z, normalizedDensity (capTestMeasure h c r) k u (X,z) *
        K (X,capReferenceLabel c r X z) ∂unitBallLaw k ∂Measure.pi (fun _ => stdGaussian E) := by
  let μ := (capMeasure c r).withDensity h
  let ν := capTestMeasure h c r
  have : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have hf (X : Fin k → E) : Measurable (fun s => K (X,rowMap X s)) := by fun_prop
  have he (X : Fin k → E) (hX : LinearIndependent ℝ X) :
      (∫⁻ s, K (X,rowMap X s) ∂μ) =
      ∫⁻ z, normalizedDensity ν k u (X,z)*K (X,capReferenceLabel c r X z) ∂unitBallLaw k := by
    have hid := lintegral_withDensity_eq_lintegral_mul (unitBallLaw k)
      (show Measurable (fun z => normalizedDensity ν k u (X,z)) by fun_prop)
      (show Measurable (fun z => K (X,capReferenceLabel c r X z)) by fun_prop)
    simp only [Pi.mul_apply] at hid
    rw [← hid,
      normalizedDensity_unitBall ν hu (capTestMeasure_support h c hr) X (hac X),
      lintegral_map (by fun_prop) (by fun_prop)]
    change _ = ∫⁻ s, K (X,capReferenceLabel c r X (rowMap (polarRows u X) s)) ∂μ.map (rescale c r)
    rw [lintegral_map (by fun_prop) (measurable_rescale c r)]
    apply lintegral_congr
    intro s
    congr 1
    rw [capReferenceLabel, ← polar_label_identity hX u c (rescale c r s) r,
      dilate_rescale c hr.ne']
  have hid := lintegral_withDensity_eq_lintegral_mul (capMeasure c r) hh (measurable_capKernelValue hK)
  simp only [Pi.mul_apply] at hid
  rw [← hid]
  change (∫⁻ s, ∫⁻ X, K (X,rowMap X s) ∂Measure.pi (fun _ => stdGaussian E) ∂μ) = _
  rw [lintegral_lintegral_swap (show AEMeasurable (fun z : E × (Fin k → E) => K (z.2,rowMap z.2 z.1)) _ by
    apply Measurable.aemeasurable; exact hK.comp (measurable_snd.prodMk (by simp only [rowMap_apply]; fun_prop)))]
  exact lintegral_congr_ae (by filter_upwards [gaussian_rows_ae_linearIndependent k hk] with X hX; exact he X hX)

end

lemma holder_bounded_kernel {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {g f : Ω → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1)
    {p : ℝ} (hp : 1 < p) {D : ℝ≥0∞} (hD : (∫⁻ x, g x^p ∂μ) ≤ D) :
    (∫⁻ x, g x*f x ∂μ) ≤ D^(1/p) * (∫⁻ x, f x ∂μ)^(1-1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hg.aemeasurable hf.aemeasurable
  have he : 1 / Real.conjExponent p = 1-1/p := by
    simpa only [one_div] using hpq.one_sub_inv.symm
  have hpow : ∀ x, f x ^ Real.conjExponent p ≤ f x := by
    intro x
    simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_ge (hf1 x) hpq.symm.lt.le
  simp only [Pi.mul_apply, he] at hh
  exact hh.trans (mul_le_mul' (ENNReal.rpow_le_rpow hD (by positivity))
    (ENNReal.rpow_le_rpow (lintegral_mono hpow) (by rw [← he]; exact one_div_nonneg.mpr hpq.symm.pos.le)))

lemma cap_exp_root (C d : ℝ) {p : ℝ} (hp : 0 < p) :
    (ENNReal.ofReal (Real.exp (C*d*p))) ^ (1/p) = ENNReal.ofReal (Real.exp (C*d)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 2
  field_simp

lemma cap_dual_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 32 ≤ d →
      let k := d/16
      let α : ℝ := ((d:ℝ)-1)/2
      ∀ (c : EuclideanSpace ℝ (Fin d)), ‖c‖ = 1 →
      ∀ r : ℝ, 0 < r → r ≤ 2 →
      ∀ D : CapDictionary c r α,
      ∀ K : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞,
      Measurable K → (∀ z, K z ≤ 1) →
      ∀ h : EuclideanSpace ℝ (Fin d) → ℝ≥0∞, Measurable h →
      (∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) →
      (∫⁻ s, h s*capKernelValue K s ∂capMeasure c r) ≤
        ENNReal.ofReal (Real.exp (C*d)) * (capReference K c r)^(1-1/(k:ℝ)) := by
  obtain ⟨C,hC,hmoment⟩ := normalized_unitBall_moment 2048 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro d hd k α c hc r hr hr2 D K hK hK1 h hh hdual
  let : NeZero d := ⟨by omega⟩
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkd : k ≤ d := by dsimp [k]; omega
  have hkd2 : k+2 ≤ d := by dsimp [k]; omega
  have hdR : (32:ℝ) ≤ d := by exact_mod_cast hd
  have hα : 2*α = (Module.finrank ℝ (EuclideanSpace ℝ (Fin d))-1:ℕ) := by
    simp only [finrank_euclideanSpace_fin, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    dsimp [α]
    ring
  let u : Fin k → EuclideanSpace ℝ (Fin d) := (EuclideanSpace.basisFun (Fin d) ℝ) ∘ Fin.castLE hkd
  have hu : Orthonormal ℝ u := (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp _ (Fin.castLE_injective hkd)
  let ν := capTestMeasure h c r
  have hmass := capTestMeasure_mass hr D hdual
  let : IsFiniteMeasure ν := capTestMeasure_finite hr D hdual
  have hs := capTestMeasure_support h c hr
  have hball := capTest_allBall hc hr hr2 (by dsimp [α]; linarith : 0 ≤ α) hα D hdual
  simp only [finrank_euclideanSpace_fin] at hball
  have hac : ∀ X, ν.map (rowMap (polarRows u X)) ≪ (volume : Measure (Label k)) :=
    fun X => capTest_frame_ac h c hr (by simpa using hkd2) _ (polarRows_orthonormal hu X)
  have hm := (hmoment d hd ν u hmass hs hball hu (Filter.Eventually.of_forall hac)).2.2.2
  have hp : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  let γ := Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin d)))
  let F : (Fin k → EuclideanSpace ℝ (Fin d)) × Label k → ℝ≥0∞ :=
    fun z => K (z.1,capReferenceLabel c r z.1 z.2)
  have hF : Measurable F := hK.comp (measurable_fst.prodMk (measurable_capReferenceLabel c r))
  have hnorm : (∫⁻ z, normalizedDensity ν k u z ^ (k:ℝ) ∂γ.prod (unitBallLaw k)) ≤
      ENNReal.ofReal (Real.exp (C*d*k)) := by
    rw [lintegral_prod _ (by fun_prop)]
    simpa only [ENNReal.rpow_natCast] using hm
  have hb := holder_bounded_kernel (γ.prod (unitBallLaw k))
    (measurable_normalizedDensity ν k u) hF (fun z => hK1 _) hp hnorm
  rw [cap_exp_root C d (by positivity : (0:ℝ)<k), lintegral_prod _ (by fun_prop),
    lintegral_prod _ (by fun_prop)] at hb
  have hparent : (∫⁻ s, h s ∂capMeasure c r) ≤ 1 := by
    simpa only [D.parent_center,D.parent_radius,div_self hr.ne',Real.one_rpow,ENNReal.ofReal_one] using hdual D.parent
  let : IsFiniteMeasure ((capMeasure c r).withDensity h) :=
    isFiniteMeasure_withDensity (ne_of_lt (hparent.trans_lt (by simp)))
  rw [cap_kernel_test_identity (by simpa using hkd) hK h hh c hr hu hac]
  exact hb

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.cap_dual_estimate := @_root_.OAI.ProjectionMoments.cap_dual_estimate
