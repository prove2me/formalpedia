-- Prove2me | solution 1 for OAI.ProjectionMoments.frame_gaussian_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:28:05.660985+00:00
-- url     : https://prove2.me/submissions/84defdcb-9020-4697-aac2-45c319fe734b

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Frames.lean:L336-L389
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.frame_gaussian_comparison. The node keeps its source
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
import Theorems.Thm_OAI_NoiselessRegression_ae_pi_snoc
import Theorems.Thm_OAI_ProjectionMoments_density_moment_equiv
import Theorems.Thm_OAI_ProjectionMoments_gaussian_norm_ball_mass
import Theorems.Thm_OAI_ProjectionMoments_lowerDensity_is_density
import Theorems.Thm_OAI_ProjectionMoments_rotation_transitive
import Theorems.Thm_OAI_ProjectionMoments_rows_factor

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

lemma map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map (show Measurable (s.indicator (fun y => f (e.symm y))) from
      (hf.comp e.symm.measurable).indicator hs) e.measurable]
  have he (x : X) : s.indicator (fun y => f (e.symm y)) (e x) =
      (e ⁻¹' s).indicator f x := by
    by_cases hx : e x ∈ s <;> simp [hx]
  simp_rw [he]
  exact (lintegral_indicator (hs.preimage e.measurable) f).symm

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Frames ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowJacobian_pos [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} {A : Fin m → E} (hA : LinearIndependent ℝ A) :
    0 < rowJacobian A := Finset.prod_pos (fun i _ => norm_pos_iff.mpr (gramSchmidt_ne_zero i hA))

omit [MeasurableSpace E] [BorelSpace E] in
lemma rowJacobian_le [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) :
    rowJacobian A ≤ ∏ i, ‖A i‖ := by
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [NoiselessRegression.norm_gramSchmidt_eq_infDist]
  simpa only [dist_zero_right] using
    Metric.infDist_le_dist_of_mem (x := A i) (Submodule.zero_mem (Submodule.span ℝ (A '' Set.Iio i)))

lemma coordinateMap_rotateRows {m : ℕ} (O : Rotation E) (A : Fin m → E) (x : E) :
    coordinateMap (rotateRows O A) x =
      coordinateMap A ((Unitary.linearIsometryEquiv O).symm x) := by
  ext i
  simp only [coordinateMap_apply, rotateRows]
  calc
    _ = ⟪(Unitary.linearIsometryEquiv O) (A i), x⟫ := real_inner_comm _ _
    _ = ⟪A i, (Unitary.linearIsometryEquiv O).symm x⟫ :=
      LinearIsometryEquiv.inner_map_eq_flip _ _ _
    _ = _ := real_inner_comm _ _

end Triangular

section CoordinateDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_eq_toLp_coordinateMap [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) :
    (rowMap A : E → Label m) = (WithLp.toLp 2) ∘ coordinateMap A := rfl

lemma coordinateDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    volume.withDensity (fun y => coordinateDensity ν m (A,y)) = ν.map (coordinateMap A) := by
  have hr : ν.map (rowMap A) ≪ (volume : Measure (Label m)) := by
    rw [rowMap_eq_toLp_coordinateMap, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← (PiLp.volume_preserving_toLp (Fin m)).map_eq]
    exact hA.map (by fun_prop)
  have h := congrArg (fun μ : Measure (Label m) => μ.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm)
    (lowerDensity_is_density ν m A hr)
  rw [map_withDensity_equiv _ _ _ (by fun_prop),
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

lemma labelMoment_factor (ν : Measure E) [IsFiniteMeasure ν] {m n : ℕ}
    (A u : Fin m → E) (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hf : ∀ x, coordinateMap A x = T (coordinateMap u x))
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hT : (volume : Measure (Fin m → ℝ)).map T = c • volume)
    (hu : ν.map (coordinateMap u) ≪ (volume : Measure (Fin m → ℝ))) :
    labelMoment ν m n A = c^n * labelMoment ν m n u := by
  have he : ν.map (coordinateMap A) = (ν.map (coordinateMap u)).map T := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    exact funext hf
  have ha : ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
    rw [he]
    have h := hu.map T.continuous.measurable
    rw [hT] at h
    exact h.trans Measure.smul_absolutelyContinuous
  apply density_moment_equiv volume T.toHomeomorph.toMeasurableEquiv c hc0 hct hT
    (by fun_prop) (by fun_prop)
  rw [coordinateDensity_is_density ν m A ha, coordinateDensity_is_density ν m u hu, he]
  rfl

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma frameLaw_eq {m : ℕ} {u v : Fin m → E} (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    frameLaw u = frameLaw v := rotationLaw_orbit_eq hu hv

lemma orbitMoment_eq_frame (ν : Measure E) [SFinite ν] (m n : ℕ) (u : Fin m → E) :
    orbitMoment ν m n u = ∫⁻ A, labelMoment ν m n A ∂frameLaw u := by
  rw [frameLaw, lintegral_map (measurable_labelMoment ν m n) (measurable_rotateRows_left u)]
  rfl

lemma orbitMoment_factor (ν : Measure E) [IsFiniteMeasure ν] {m n : ℕ}
    (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)))
    (A : Fin m → E) (hA : LinearIndependent ℝ A) :
    orbitMoment ν m n A = (ENNReal.ofReal (rowJacobian A))⁻¹ ^ n * orbitMoment ν m n u := by
  obtain ⟨v, hv, T, hT, hvol⟩ := rows_factor A hA
  have hacv : ∀ᵐ O ∂rotationLaw E,
      ν.map (coordinateMap (rotateRows O v)) ≪ (volume : Measure (Fin m → ℝ)) := by
    apply ae_of_ae_map (p := fun B : Fin m → E => ν.map (coordinateMap B) ≪ (volume : Measure (Fin m → ℝ)))
      (measurable_rotateRows_left v).aemeasurable
    change ∀ᵐ B ∂frameLaw v, _
    rwa [← frameLaw_eq hu hv]
  have hi : orbitMoment ν m n A =
      (ENNReal.ofReal (rowJacobian A))⁻¹ ^ n * orbitMoment ν m n v := by
    unfold orbitMoment
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply lintegral_congr_ae
    filter_upwards [hacv] with O hO
    apply labelMoment_factor ν (rotateRows O A) (rotateRows O v) T
      (fun x => ?_) ((ENNReal.ofReal (rowJacobian A))⁻¹) (by simp)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (rowJacobian_pos hA))) hvol hO
    rw [coordinateMap_rotateRows, coordinateMap_rotateRows, hT]
  rw [hi, orbitMoment_eq_frame, ← frameLaw_eq hu hv, ← orbitMoment_eq_frame]

lemma gaussian_lintegral_orbitMoment (ν : Measure E) [SFinite ν] (m n : ℕ) :
    ∫⁻ A, orbitMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) =
      ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by
  unfold orbitMoment
  rw [lintegral_lintegral_swap (by
    exact ((measurable_labelMoment ν m n).comp (measurable_rotateRows.comp measurable_swap)).aemeasurable)]
  have hi (O : Rotation E) :
      ∫⁻ A, labelMoment ν m n (rotateRows O A) ∂Measure.pi (fun _ => stdGaussian E) =
        ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by
    rw [← lintegral_map (measurable_labelMoment ν m n) (measurable_rotateRows_right O),
      gaussianRows_rotation_invariant]
  simp_rw [hi]
  simp

theorem frame_gaussian_comparison (ν : Measure E) [IsFiniteMeasure ν]
    {m n : ℕ} (hm : m ≤ Module.finrank ℝ E) (hd : 0 < Module.finrank ℝ E)
    (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    orbitMoment ν m n u ≤
      (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2 * Module.finrank ℝ E))^(m*n) *
        ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by
  let γ : Measure (Fin m → E) := Measure.pi (fun _ => stdGaussian E)
  let t : ℝ := Real.sqrt (2 * Module.finrank ℝ E)
  let G : Set (Fin m → E) := Set.univ.pi (fun _ => Metric.closedBall (0 : E) t)
  have ht : 0 < t := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < 2 * Module.finrank ℝ E by omega))
  have hG : MeasurableSet G := MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  have hGmass : (2 : ℝ≥0∞)⁻¹^m ≤ γ G := by
    rw [show γ G = ∏ _ : Fin m, stdGaussian E (Metric.closedBall 0 t) from Measure.pi_pi _ _]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod' (s := Finset.univ) (fun (_ : Fin m) _ => gaussian_norm_ball_mass (E := E) hd)
  let B : ℝ≥0∞ := ENNReal.ofReal t ^ m
  have hB0 : B ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr ht)
  have hBt : B ≠ ∞ := by simp [B]
  have hJ (A : Fin m → E) (hA : A ∈ G) : ENNReal.ofReal (rowJacobian A) ≤ B := by
    have hnorm (i : Fin m) : ‖A i‖ ≤ t := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hA i (Set.mem_univ i)
    have h := (rowJacobian_le A).trans (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hnorm i))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    simpa only [B, ENNReal.ofReal_pow ht.le] using ENNReal.ofReal_le_ofReal h
  have hlow : B⁻¹^n * orbitMoment ν m n u * γ G ≤
      ∫⁻ A, orbitMoment ν m n A ∂γ := by
    calc
      _ = ∫⁻ A in G, B⁻¹^n * orbitMoment ν m n u ∂γ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ A in G, orbitMoment ν m n A ∂γ := by
        apply setLIntegral_mono_ae' hG
        filter_upwards [gaussian_rows_ae_linearIndependent m hm] with A hA
        intro hAG
        rw [orbitMoment_factor ν u hu hac A hA]
        exact mul_le_mul' (pow_le_pow_left' (ENNReal.inv_le_inv.mpr (hJ A hAG)) n) le_rfl
      _ ≤ ∫⁻ A, orbitMoment ν m n A ∂γ := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
  have hlow' : ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n) * orbitMoment ν m n u ≤
      ∫⁻ A, labelMoment ν m n A ∂γ := by
    rw [← gaussian_lintegral_orbitMoment ν m n]
    exact (show ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n) * orbitMoment ν m n u ≤
        B⁻¹^n * orbitMoment ν m n u * γ G from by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul' hGmass (le_rfl : B⁻¹^n * orbitMoment ν m n u ≤ B⁻¹^n * orbitMoment ν m n u)).trans hlow
  have hc0 : (2 : ℝ≥0∞)⁻¹^m * B⁻¹^n ≠ 0 := by simp [hBt]
  have hct : (2 : ℝ≥0∞)⁻¹^m * B⁻¹^n ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) (by finiteness)
  have h := mul_le_mul' (le_rfl : ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n)⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n)⁻¹) hlow'
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul] at h
  have he : ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n)⁻¹ = (2 : ℝ≥0∞)^m * ENNReal.ofReal t^(m*n) := by
    rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by finiteness)),
      ← ENNReal.inv_pow, ← ENNReal.inv_pow, inv_inv, inv_inv]
    simp only [B, ← pow_mul]
  rw [he] at h
  exact h

end ProjectionMoments
end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.frame_gaussian_comparison := @_root_.OAI.ProjectionMoments.frame_gaussian_comparison
