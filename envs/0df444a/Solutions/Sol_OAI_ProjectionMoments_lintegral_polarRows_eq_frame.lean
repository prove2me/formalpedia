-- Prove2me | solution 1 for OAI.ProjectionMoments.lintegral_polarRows_eq_frame
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:43:07.412243+00:00
-- url     : https://prove2.me/submissions/b3a120b7-97bd-4fda-ad79-c3476fff8205

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Polar.lean:L161-L193
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.lintegral_polarRows_eq_frame. The node keeps its source
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
import Theorems.Thm_OAI_NoiselessRegression_ae_pi_snoc
import Theorems.Thm_OAI_ProjectionMoments_rotation_transitive

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

lemma rotationLaw_orbit_eq {ι : Type*} [Fintype ι] {u v : ι → E}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    (rotationLaw E).map (fun O => rotateRows O u) =
      (rotationLaw E).map (fun O => rotateRows O v) := by
  obtain ⟨Q, hQ⟩ := rotation_transitive hu hv
  have he : rotateRows Q u = v := funext hQ
  have hm : Measurable (fun O : Rotation E => rotateRows O u) :=
    measurable_rotateRows.comp (measurable_id.prodMk measurable_const)
  rw [← he]
  conv_lhs => rw [← (measurePreserving_mul_right (rotationLaw E) Q).map_eq]
  rw [Measure.map_map hm (by fun_prop)]
  rfl

lemma gaussianRows_rotation_invariant (m : ℕ) (O : Rotation E) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map (rotateRows O) =
      Measure.pi (fun _ : Fin m => stdGaussian E) := by
  change (Measure.pi (fun _ : Fin m => stdGaussian E)).map
    (fun v i => O.val (v i)) = _
  rw [Measure.pi_map_pi (f := fun _ : Fin m => (O.val : E →L[ℝ] E))
    (fun _ => O.val.continuous.measurable.aemeasurable)]
  congr 1
  funext j
  exact stdGaussian_map (Unitary.linearIsometryEquiv O)

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

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma frameLaw_eq {m : ℕ} {u v : Fin m → E} (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    frameLaw u = frameLaw v := rotationLaw_orbit_eq hu hv

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

omit [MeasurableSpace E] [BorelSpace E] in
lemma gram_rotateRows [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) (O : Rotation E) :
    Matrix.gram ℝ (rotateRows O X) = Matrix.gram ℝ X := by
  ext i j
  exact (Unitary.linearIsometryEquiv O).inner_map_map (X i) (X j)

lemma polarRadial_rotateRows {k : ℕ} (X : Fin k → E) (O : Rotation E) :
    polarRadial (rotateRows O X) = polarRadial X := by
  simp only [polarRadial, gram_rotateRows]

lemma rawPolarRows_rotateRows {k : ℕ} (X : Fin k → E) (O : Rotation E) :
    rawPolarRows (rotateRows O X) = rotateRows O (rawPolarRows X) := by
  ext i
  simp only [rawPolarRows, polarRadial_rotateRows, mixRows, rotateRows, map_sum, map_smul]

lemma polarRows_orthonormal {k : ℕ} {u : Fin k → E} (hu : Orthonormal ℝ u)
    (X : Fin k → E) : Orthonormal ℝ (polarRows u X) := by
  by_cases hX : LinearIndependent ℝ X
  · simpa only [polarRows, ite_eq_left hX] using rawPolarRows_orthonormal hX
  · simpa only [polarRows, ite_eq_right hX] using hu

lemma polarRows_rotateRows {k : ℕ} (u : Fin k → E) {X : Fin k → E}
    (hX : LinearIndependent ℝ X) (O : Rotation E) :
    polarRows u (rotateRows O X) = rotateRows O (polarRows u X) := by
  have hXO : LinearIndependent ℝ (rotateRows O X) := by
    rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, gram_rotateRows,
      Matrix.det_gram_ne_zero_iff_linearIndependent]
    exact hX
  simp only [polarRows, ite_eq_left hX, ite_eq_left hXO, rawPolarRows_rotateRows]

lemma lintegral_polarRows_eq_frame {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {u : Fin k → E} (hu : Orthonormal ℝ u) (f : (Fin k → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ X, f (polarRows u X) ∂Measure.pi (fun _ => stdGaussian E)) = ∫⁻ A, f A ∂frameLaw u := by
  let γ := Measure.pi (fun _ : Fin k => stdGaussian E)
  have hrot (O : Rotation E) : (∫⁻ X, f (polarRows u X) ∂γ) =
      ∫⁻ X, f (rotateRows O (polarRows u X)) ∂γ := by
    calc
      _ = ∫⁻ X, f (polarRows u (rotateRows O X)) ∂γ := by
        have hm : Measurable (rotateRows O : (Fin k → E) → (Fin k → E)) :=
          measurable_rotateRows.comp (measurable_const.prodMk measurable_id)
        have hh := lintegral_map (μ := γ) (hf.comp (measurable_polarRows u)) hm
        rw [show γ.map (rotateRows O) = γ from gaussianRows_rotation_invariant k O] at hh
        exact hh
      _ = _ := lintegral_congr_ae (by
        filter_upwards [gaussian_rows_ae_linearIndependent k hk] with X hX
        rw [polarRows_rotateRows u hX])
  calc
    _ = ∫⁻ O, ∫⁻ X, f (rotateRows O (polarRows u X)) ∂γ ∂rotationLaw E := by
      simp_rw [← hrot]
      simp only [lintegral_const, measure_univ, mul_one]
      rfl
    _ = ∫⁻ X, ∫⁻ O, f (rotateRows O (polarRows u X)) ∂rotationLaw E ∂γ := by
      apply lintegral_lintegral_swap
      exact (hf.comp (measurable_rotateRows.comp
        (measurable_fst.prodMk ((measurable_polarRows u).comp measurable_snd)))).aemeasurable
    _ = ∫⁻ X, ∫⁻ A, f A ∂frameLaw u ∂γ := by
      apply lintegral_congr
      intro X
      rw [frameLaw_eq hu (polarRows_orthonormal hu X), frameLaw]
      have hm : Measurable (fun O : Rotation E => rotateRows O (polarRows u X)) :=
        measurable_rotateRows.comp (measurable_id.prodMk measurable_const)
      exact (lintegral_map hf hm).symm
    _ = _ := by simp [γ]

end

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.lintegral_polarRows_eq_frame := @_root_.OAI.ProjectionMoments.lintegral_polarRows_eq_frame
