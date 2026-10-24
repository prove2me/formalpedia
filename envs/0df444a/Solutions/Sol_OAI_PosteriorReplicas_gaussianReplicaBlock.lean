-- Prove2me | solution 1 for OAI.PosteriorReplicas.gaussianReplicaBlock
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:46:13.506085+00:00
-- url     : https://prove2.me/submissions/967cf182-2d70-4716-bf25-971b34742da8

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000
import Theorems.Thm_OAI_PosteriorReplicas_gaussian_replica_information_cost

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_PiLast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section PiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma lintegral_pi_snoc (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => ν) =
      ∫⁻ v : Fin n → E, ∫⁻ x, f (Fin.snoc v x) ∂ν ∂Measure.pi (fun _ => ν) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f,
    lintegral_prod_symm]
  · congr 1
    ext v
    congr 1
    ext x
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact Fin.insertNth_last' x v
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable
end PiLast

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GramFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
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

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_AePiLast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section AePiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma ae_pi_snoc {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => ν), P v) ↔
      ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), ∀ᵐ x ∂ν, P (Fin.snoc v x) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.map_eq, MeasurableEmbedding.ae_map_iff (MeasurableEquiv.measurableEmbedding _)]
  have heq : (fun z : E × (Fin n → E) =>
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) (Fin.last n)).symm z) =
      fun z => Fin.snoc z.2 z.1 := by
    ext z : 1
    change (Fin.last n).insertNth (α := fun _ => E) z.1 z.2 = _
    exact Fin.insertNth_last' z.1 z.2
  have hm : Measurable (fun z : E × (Fin n → E) => Fin.snoc (α := fun _ => E) z.2 z.1) := by
    rw [← heq]
    exact hp.measurable
  change (∀ᵐ z ∂ν.prod (Measure.pi (fun _ : Fin n => ν)),
      P ((fun z => (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E)
        (Fin.last n)).symm z) z)) ↔ _
  have hPP : MeasurableSet {z : E × (Fin n → E) | P (Fin.snoc z.2 z.1)} := hP.preimage hm
  rw [heq, Measure.ae_prod_iff_ae_ae hPP]
  exact Measure.ae_ae_comm hPP
end AePiLast

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_InverseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
section InverseMoments

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma inverse_pow_dyadic_majorant (f : X → ℝ) (m : ℕ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    ENNReal.ofReal ((f x)⁻¹ ^ m) ≤
      1 + ∑' k : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1)))) x := by
  classical
  by_cases hzero : f x = 0
  · simp only [hzero, inv_zero]
    exact le_add_of_le_left (by cases m <;> simp)
  have hxpos : 0 < f x := lt_of_le_of_ne (hf x) (Ne.symm hzero)
  by_cases hxone : 1 ≤ f x
  · apply le_add_of_le_left
    have h : (f x)⁻¹ ^ m ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr (hf x)) (inv_le_one_of_one_le₀ hxone)
    simpa using ENNReal.ofReal_le_ofReal h
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hxpos
    (le_of_not_ge hxone) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hinv : (f x)⁻¹ ≤ (2 : ℝ) ^ (k + 1) := by
    have h := (inv_le_inv₀ hxpos (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _)).2 hklo.le
    simpa using h
  have hpow : ENNReal.ofReal ((f x)⁻¹ ^ m) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) := by
    apply ENNReal.ofReal_le_ofReal
    simpa [← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ (inv_nonneg.mpr (hf x)) hinv m
  calc
    ENNReal.ofReal ((f x)⁻¹ ^ m) ≤ ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) := hpow
    _ = ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1)))) x := by
      rw [Set.indicator_of_mem (show x ∈ {x | f x ≤ (1 / 2 : ℝ) ^ k} from hkhi)]
    _ ≤ ∑' j : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x :=
      ENNReal.le_tsum (f := fun index : ℕ =>
        ({point | f point ≤ (1 / 2 : ℝ) ^ index}).indicator
          (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (index + 1)))) x) k
    _ ≤ 1 + ∑' j : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x := le_add_left le_rfl

lemma dyadic_power_cancel (m k : ℕ) :
    (2 : ℝ) ^ (m * (k + 1)) * ((1 / 2 : ℝ) ^ k) ^ (m + 1) =
      (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ k := by
  rw [Nat.mul_add, mul_one, pow_add, pow_succ]
  have h : (2 : ℝ) ^ (m * k) * ((1 / 2 : ℝ) ^ k) ^ m = 1 := by
    rw [Nat.mul_comm m k, pow_mul, ← mul_pow, ← mul_pow]
    norm_num
  calc
    2 ^ (m * k) * 2 ^ m * (((1 / 2 : ℝ) ^ k) ^ m * (1 / 2 : ℝ) ^ k) =
      (2 ^ (m * k) * ((1 / 2 : ℝ) ^ k) ^ m) * (2 ^ m * (1 / 2 : ℝ) ^ k) := by ring
    _ = _ := by rw [h, one_mul]

theorem inverse_moment_of_tube_bound (μ : Measure X) (f : X → ℝ) (m : ℕ)
    (hf : Measurable f) (hnonneg : ∀ x, 0 ≤ f x) (C : ℝ≥0∞)
    (htube : ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ {x | f x ≤ r} ≤ C * ENNReal.ofReal (r ^ (m + 1))) :
    ∫⁻ x, ENNReal.ofReal ((f x)⁻¹ ^ m) ∂μ ≤
      μ Set.univ + C * (2 : ℝ≥0∞) ^ (m + 1) := by
  classical
  let g : ℕ → X → ℝ≥0∞ := fun k =>
    ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
      (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))))
  have hg : ∀ k, Measurable (g k) := fun k =>
    measurable_const.indicator (measurableSet_le hf measurable_const)
  calc
    ∫⁻ x, ENNReal.ofReal ((f x)⁻¹ ^ m) ∂μ ≤ ∫⁻ x, 1 + ∑' k, g k x ∂μ :=
      lintegral_mono (inverse_pow_dyadic_majorant f m hnonneg)
    _ = μ Set.univ + ∑' k, ∫⁻ x, g k x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, one_mul, lintegral_tsum (fun k => (hg k).aemeasurable)]
    _ ≤ μ Set.univ + ∑' k, C * ENNReal.ofReal ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ k) := by
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro k
      dsimp only [g]
      rw [lintegral_indicator (measurableSet_le hf measurable_const), lintegral_const,
        Measure.restrict_apply_univ]
      calc
        ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) * μ {x | f x ≤ (1 / 2 : ℝ) ^ k} ≤
            ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) *
              (C * ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ (m + 1))) := by
          gcongr
          exact htube _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
        _ = _ := by
          rw [← mul_assoc, mul_comm _ C, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            dyadic_power_cancel]
    _ = μ Set.univ + C * (2 : ℝ≥0∞) ^ (m + 1) := by
      simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ m),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      norm_num [pow_succ, mul_assoc, ENNReal.ofReal_div_of_pos]

end InverseMoments

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GramDistances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
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
lemma infDist_affine_mk' (p x : E) (K : Submodule ℝ E) :
    Metric.infDist x (AffineSubspace.mk' p K : Set E) =
      Metric.infDist (x - p) (K : Set E) := by
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
    EuclideanGeometry.orthogonalProjection_apply_mem _ (AffineSubspace.self_mem_mk' p K),
    dist_eq_norm, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  change ‖x - _‖ = ⨅ y : K, ‖(x - p) - y‖
  rw [← Submodule.starProjection_minimal]
  simp only [AffineSubspace.direction_mk', vsub_eq_sub, vadd_eq_add,
    Submodule.coe_orthogonalProjectionOnto_apply]
  congr 1
  abel

lemma norm_gramSchmidt_sub_eq_affine_infDist (p : E) (t : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ (fun i => t i - p) j‖ =
      Metric.infDist (t j) (AffineSubspace.mk' p
        (Submodule.span ℝ ((fun i => t i - p) '' Set.Iio j)) : Set E) := by
  rw [infDist_affine_mk', norm_gramSchmidt_eq_infDist]

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

end GramDistances

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ReplicaMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_replicaWeight (m : ℕ) (p : E) (n : ℕ) :
    Measurable (replicaWeight m p (n := n)) := by
  have hs : Measurable (fun v : Fin n → E => fun j => v j - p) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m).ennreal_ofReal

omit [MeasurableSpace E] [BorelSpace E] in
lemma replicaWeight_snoc (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) (x : E) :
    replicaWeight m p (Fin.snoc v x) = replicaWeight m p v *
      ENNReal.ofReal ((Metric.infDist x (AffineSubspace.mk' p
        (Submodule.span ℝ (Set.range (fun i => v i - p))) : Set E))⁻¹ ^ m) := by
  unfold replicaWeight
  rw [Fin.prod_univ_castSucc]
  simp only [gramSchmidt_castSucc, Fin.snoc_castSucc]
  rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]

end ReplicaMoments

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Regression_ReplicaNondegenerate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section ReplicaNondegenerate
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

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma sqrt_det_gram (n : ℕ) (v : Fin n → E) :
    Real.sqrt (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  rw [det_gram_eq_prod_gramSchmidt, Real.sqrt_prod _ (fun _ _ => sq_nonneg _)]
  simp only [Real.sqrt_sq (norm_nonneg _)]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma replicaWeight_eq_det (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) :
    replicaWeight m p v = ENNReal.ofReal
      ((Real.sqrt (Matrix.gram ℝ (fun j => v j - p)).det)⁻¹ ^ m) := by
  rw [sqrt_det_gram, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)).symm

end ReplicaNondegenerate

end PosteriorRegression
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace PosteriorReplicas

section GaussianSplitting
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma pairing_starProjection (U : Submodule ℝ E) {v : E} (hv : v ∈ U) (x : E) :
    ⟪v, U.starProjection x⟫ = ⟪v, x⟫ := by
  rw [← U.inner_starProjection_left_eq_right, U.starProjection_eq_self_iff.mpr hv]

end GaussianSplitting
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_DensityTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma lintegral_fin_prod {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : (i : Fin n) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E i.succ),
          f 0 x.1 * ∏ i, f i.succ (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp
          (by exact Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i)))]
        simp only [Fin.prod_univ_succ, Fin.zero_succAbove]
        rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
        have hg : Measurable (fun x : (i : Fin n) → E i.succ => ∏ i, f i.succ (x i)) :=
          Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))
        rw [lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable,
          ih _ _ (fun i => hf i.succ)]
      _ = _ := by rw [Fin.prod_univ_succ]

lemma lintegral_finite_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : (i : ι) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp
    (show Measurable (fun x => ∏ i, f i (x i)) from Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i)))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod _ _ (fun i => hf (e i))

lemma pi_withDensity {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [lintegral_finite_prod _ _ hf]
  congr 1
  ext i
  rw [withDensity_apply _ (hs i)]

lemma pi_gaussian_density (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  have h : gaussianReal 0 1 = (volume : Measure ℝ).withDensity (gaussianPDF 0 1) :=
    gaussianReal_of_var_ne_zero _ (by norm_num)
  have : IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    rw [← h]
    infer_instance
  rw [h]
  exact pi_withDensity _ _ (fun _ => measurable_gaussianPDF _ _)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

lemma gaussian_density_product {n : ℕ} (z : Fin n → ℝ) :
    (∏ i, gaussianPDF 0 1 (z i)) = ENNReal.ofReal
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-(∑ i, (z i)^2) / 2)) := by
  have hconst : (Real.sqrt (2 * Real.pi))⁻¹ ^ n =
      (2 * Real.pi) ^ (-(n : ℝ) / 2) := by
    rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1
    ring
  simp only [gaussianPDF_def]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 (z i))]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hconst, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianPolar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_density : stdGaussian E = volume.withDensity
    (fun x : E => gaussianRadialDensity (Module.finrank ℝ E) ‖x‖) := by
  let b := stdOrthonormalBasis ℝ E
  have hp : MeasurePreserving (fun x : Fin (Module.finrank ℝ E) → ℝ => ∑ i, x i • b i)
      volume volume := by
    have heq : (fun x : Fin (Module.finrank ℝ E) → ℝ => ∑ i, x i • b i) =
        b.repr.symm ∘ WithLp.toLp 2 := by
      funext x
      exact b.sum_repr_symm (WithLp.toLp 2 x)
    rw [heq]
    exact b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp _)
  apply Measure.ext_of_lintegral
  intro g hg
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    lintegral_map hg (by fun_prop), pi_gaussian_density,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg,
    ← hp.lintegral_comp (by fun_prop)]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  have hnorm : ‖∑ i, x i • b i‖^2 = ∑ i, (x i)^2 := by
    rw [← real_inner_self_eq_norm_sq, b.orthonormal.inner_sum]
    simp [sq]
  rw [gaussian_density_product, gaussianRadialDensity, hnorm]

lemma stdGaussian_absolutelyContinuous_volume : stdGaussian E ≪ volume := by
  rw [stdGaussian_density]
  exact withDensity_absolutelyContinuous _ _

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianSmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_density_ball_lower {R : ℝ} (hR : 0 ≤ R) :
    ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (-R^2/2)) * volume (closedBall (0 : E) R) ≤ 1 := by
  calc
    _ = ∫⁻ x in closedBall (0 : E) R,
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-R^2/2)) ∂volume := by simp
    _ ≤ ∫⁻ x in closedBall (0 : E) R,
      gaussianRadialDensity (Module.finrank ℝ E) ‖x‖ ∂volume := by
      apply setLIntegral_mono' isClosed_closedBall.measurableSet
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hn : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
      nlinarith [norm_nonneg x, sq_nonneg (R-‖x‖)]
    _ = stdGaussian E (closedBall (0 : E) R) := by
      rw [stdGaussian_density, withDensity_apply _ isClosed_closedBall.measurableSet]
    _ ≤ 1 := prob_le_one

lemma gaussian_density_ball_upper (a : E) (r : ℝ) :
    stdGaussian E (closedBall a r) ≤
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) *
        volume (closedBall a r) := by
  rw [stdGaussian_density, withDensity_apply _ isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∫⁻ _ in closedBall a r,
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) ∂volume := by
      apply lintegral_mono
      intro x
      apply ENNReal.ofReal_le_ofReal
      have he : Real.exp (-‖x‖^2/2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg ‖x‖]
      exact mul_le_of_le_one_right (by positivity) he
    _ = _ := by simp

lemma gaussian_closedBall_ratio (a : E) {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) :
    stdGaussian E (closedBall a r) ≤
      ENNReal.ofReal (Real.exp (R^2/2) * (r/R)^(Module.finrank ℝ E)) := by
  let c : ℝ := (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  have hexp : ENNReal.ofReal (Real.exp (R^2/2)) *
      ENNReal.ofReal (Real.exp (-R^2/2)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    have he : R^2/2 + -R^2/2 = 0 := by ring
    rw [he, Real.exp_zero, ENNReal.ofReal_one]
  have h := mul_le_mul_right (gaussian_density_ball_lower (E := E) hR.le)
    (ENNReal.ofReal (Real.exp (R^2/2)))
  have hvol : ENNReal.ofReal c * volume (closedBall (0 : E) R) ≤
      ENNReal.ofReal (Real.exp (R^2/2)) := by
    dsimp only [c] at *
    rw [ENNReal.ofReal_mul (by positivity), mul_one] at h
    calc
      _ = (ENNReal.ofReal (Real.exp (R^2/2)) * ENNReal.ofReal (Real.exp (-R^2/2))) *
        (ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) *
          volume (closedBall (0 : E) R)) := by rw [hexp, one_mul]
      _ ≤ _ := by simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hscale : volume (closedBall a r) =
      ENNReal.ofReal ((r/R)^(Module.finrank ℝ E)) * volume (closedBall (0 : E) R) := by
    have hh := Measure.addHaar_closedBall_mul (volume : Measure E) a (div_nonneg hr hR.le) hR.le
    rw [div_mul_cancel₀ _ hR.ne'] at hh
    exact hh
  calc
    _ ≤ ENNReal.ofReal c * volume (closedBall a r) := gaussian_density_ball_upper a r
    _ = ENNReal.ofReal ((r/R)^(Module.finrank ℝ E)) *
        (ENNReal.ofReal c * volume (closedBall (0 : E) R)) := by rw [hscale]; ac_rfl
    _ ≤ ENNReal.ofReal ((r/R)^(Module.finrank ℝ E)) *
        ENNReal.ofReal (Real.exp (R^2/2)) := mul_le_mul_right hvol _
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

lemma gaussian_normalized_inverse_moment (a : E) (k : ℕ) (hk : k+1 ≤ Module.finrank ℝ E)
    {R : ℝ} (hR : 0 < R) :
    (∫⁻ x : E, ENNReal.ofReal (((‖x-a‖ / R)⁻¹)^k) ∂stdGaussian E) ≤
      1 + ENNReal.ofReal (Real.exp (R^2/2)) * 2^(k+1) := by
  have h := PosteriorRegression.inverse_moment_of_tube_bound (stdGaussian E)
    (fun x : E => ‖x-a‖/R) k (by fun_prop) (fun x => by positivity)
    (ENNReal.ofReal (Real.exp (R^2/2))) ?_
  · simpa only [measure_univ] using h
  intro r hr hr1
  have hs : {x : E | ‖x-a‖ / R ≤ r} = closedBall a (r*R) := by
    ext x
    simp only [mem_ofPred_eq, mem_closedBall, dist_eq_norm, div_le_iff₀ hR]
  rw [hs]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (R^2/2) * ((r*R)/R)^(Module.finrank ℝ E)) :=
      gaussian_closedBall_ratio a hR (mul_nonneg hr.le hR.le)
    _ ≤ _ := by
      rw [mul_div_cancel_right₀ _ hR.ne', ENNReal.ofReal_mul (by positivity)]
      apply mul_le_mul_right
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr.le hr1 hk)

lemma gaussian_inverse_norm_moment (a : E) (k : ℕ) (hk : k+1 ≤ Module.finrank ℝ E)
    {R : ℝ} (hR : 0 < R) :
    (∫⁻ x : E, ENNReal.ofReal (‖x-a‖⁻¹^k) ∂stdGaussian E) ≤
      ENNReal.ofReal (R⁻¹^k) * (1 + ENNReal.ofReal (Real.exp (R^2/2)) * 2^(k+1)) := by
  have he : (∫⁻ x : E, ENNReal.ofReal (‖x-a‖⁻¹^k) ∂stdGaussian E) =
      ENNReal.ofReal (R⁻¹^k) * ∫⁻ x : E, ENNReal.ofReal (((‖x-a‖/R)⁻¹)^k) ∂stdGaussian E := by
    rw [← lintegral_const_mul _ (show Measurable (fun x : E =>
      ENNReal.ofReal (((‖x-a‖/R)⁻¹)^k)) by fun_prop)]
    apply lintegral_congr
    intro x
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    congr 2
    rw [inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  rw [he]
  exact mul_le_mul_right (gaussian_normalized_inverse_moment a k hk hR) _

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_SphereSubspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_orthogonalProjectionOnto (U : Submodule ℝ E) :
    (stdGaussian E).map U.orthogonalProjectionOnto = stdGaussian U := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have he (x : E) : ⟪U.orthogonalProjectionOnto x, t⟫ = ⟪x, (t : E)⟫ := by
    change ⟪U.starProjection x, (t : E)⟫ = _
    rw [real_inner_comm, pairing_starProjection U t.2, real_inner_comm]
  simp_rw [he]
  change charFun (stdGaussian E) (t : E) = _
  rw [charFun_stdGaussian, charFun_stdGaussian]
  rfl

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_AffineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma replica_integral_of_affine_moment {ν : Measure E} [IsFiniteMeasure ν]
    (m n : ℕ) (p : E) (C : ℝ≥0∞)
    (hmoment : ∀ L : AffineSubspace ℝ E, ∀ (_ : Nonempty L),
      Module.finrank ℝ L.direction < n →
      ∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ m) ∂ν ≤ C) :
    ∫⁻ v : Fin n → E, PosteriorRegression.replicaWeight m p v ∂Measure.pi (fun _ => ν) ≤ C^n := by
  induction n with
  | zero => simp [PosteriorRegression.replicaWeight]
  | succ n ih =>
    have hinner (v : Fin n → E) :
        ∫⁻ x, PosteriorRegression.replicaWeight m p (Fin.snoc v x) ∂ν ≤
          PosteriorRegression.replicaWeight m p v * C := by
      simp_rw [PosteriorRegression.replicaWeight_snoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      gcongr
      apply hmoment _ inferInstance
      rw [AffineSubspace.direction_mk']
      have hdim := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simpa only [AffineSubspace.direction_mk', Fintype.card_fin, Nat.lt_succ_iff, Set.finrank] using hdim
    calc
      _ = ∫⁻ v : Fin n → E, ∫⁻ x, PosteriorRegression.replicaWeight m p (Fin.snoc v x) ∂ν
          ∂Measure.pi (fun _ => ν) := PosteriorRegression.lintegral_pi_snoc ν _
            (PosteriorRegression.measurable_replicaWeight m p (n+1))
      _ ≤ ∫⁻ v : Fin n → E, PosteriorRegression.replicaWeight m p v * C
          ∂Measure.pi (fun _ => ν) := lintegral_mono hinner
      _ = (∫⁻ v : Fin n → E, PosteriorRegression.replicaWeight m p v
          ∂Measure.pi (fun _ => ν)) * C := lintegral_mul_const _
            (PosteriorRegression.measurable_replicaWeight m p n)
      _ ≤ C^n * C := mul_le_mul' (ih (fun L hL hdim => hmoment L hL (by omega))) le_rfl
      _ = _ := (pow_succ _ _).symm

lemma ae_replica_independent_of_affine_null {ν : Measure E} [IsFiniteMeasure ν]
    (p : E) (n : ℕ)
    (hnull : ∀ L : AffineSubspace ℝ E, ∀ (_ : Nonempty L),
      Module.finrank ℝ L.direction < n → ν L = 0) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν), LinearIndependent ℝ (fun j => v j - p) := by
  suffices h : ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0 by
    filter_upwards [h] with v hv
    apply Matrix.linearIndependent_of_det_gram_ne_zero
    rw [PosteriorRegression.det_gram_eq_prod_gramSchmidt]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ n ih =>
    rw [PosteriorRegression.ae_pi_snoc ν (PosteriorRegression.measurableSet_gramSchmidt_ne_zero p (n+1))]
    filter_upwards [ih (fun L hL hdim => hnull L hL (by omega))] with v hv
    let L := AffineSubspace.mk' p (Submodule.span ℝ (Set.range (fun i : Fin n => v i - p)))
    have hdim : Module.finrank ℝ L.direction < n + 1 := by
      dsimp only [L]
      rw [AffineSubspace.direction_mk']
      have hh := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simpa only [Fintype.card_fin, Nat.lt_succ_iff, Set.finrank] using hh
    have ha : ∀ᵐ x ∂ν, x ∉ L := by
      rw [ae_iff]
      simpa using hnull L inferInstance hdim
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [PosteriorRegression.norm_gramSchmidt_sub_eq_affine_infDist, PosteriorRegression.image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((L.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨p, AffineSubspace.self_mem_mk' _ _⟩).mp hx)
    | cast j => simpa only [PosteriorRegression.gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

end Generic

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianGramMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma infDist_affine_projection [MeasurableSpace E] [BorelSpace E]
    (L : AffineSubspace ℝ E) {p : E} (hp : p ∈ L) (x : E) :
    Metric.infDist x L = ‖L.directionᗮ.orthogonalProjectionOnto x -
      L.directionᗮ.orthogonalProjectionOnto p‖ := by
  conv_lhs => rw [← AffineSubspace.mk'_eq hp]
  rw [PosteriorRegression.infDist_affine_mk', Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  change (⨅ y : L.direction, ‖x-p-(y : E)‖) = _
  rw [← L.direction.starProjection_minimal (x-p)]
  rw [← map_sub]
  change ‖x-p-L.direction.starProjection (x-p)‖ = ‖L.directionᗮ.starProjection (x-p)‖
  rw [Submodule.starProjection_orthogonal_val]

lemma gaussian_affine_inverse_moment (L : AffineSubspace ℝ E) [Nonempty L]
    (k : ℕ) (hk : Module.finrank ℝ L.direction + k + 1 ≤ Module.finrank ℝ E)
    {R : ℝ} (hR : 0 < R) :
    (∫⁻ x : E, ENNReal.ofReal ((Metric.infDist x L)⁻¹^k) ∂stdGaussian E) ≤
      ENNReal.ofReal (R⁻¹^k) * (1 + ENNReal.ofReal (Real.exp (R^2/2)) * 2^(k+1)) := by
  obtain ⟨⟨p,hp⟩⟩ := ‹Nonempty L›
  have hdim : k+1 ≤ Module.finrank ℝ L.directionᗮ := by
    have := L.direction.finrank_add_finrank_orthogonal
    omega
  have h := gaussian_inverse_norm_moment (L.directionᗮ.orthogonalProjectionOnto p) k hdim hR
  rw [← gaussian_orthogonalProjectionOnto L.directionᗮ,
    lintegral_map (by fun_prop) (by fun_prop)] at h
  simpa only [infDist_affine_projection L hp] using h

lemma gaussianMomentConstant_ne_top (k : ℕ) : gaussianMomentConstant k ≠ ∞ := by
  unfold gaussianMomentConstant
  finiteness

lemma gaussian_gram_inverse_moment (k m : ℕ) (hk : 1 ≤ k)
    (hd : k+m ≤ Module.finrank ℝ E) (p : E) :
    (∫⁻ v : Fin m → E,
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ (fun j => v j-p)).det)⁻¹ ^ k)
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (gaussianMomentConstant k)^m := by
  have h := replica_integral_of_affine_moment (ν := stdGaussian E) k m p (gaussianMomentConstant k) ?_
  · simpa only [PosteriorRegression.replicaWeight_eq_det] using h
  intro L hL hdim
  have hkp : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hb := gaussian_affine_inverse_moment L k (by omega :
    Module.finrank ℝ L.direction + k + 1 ≤ Module.finrank ℝ E) (Real.sqrt_pos.mpr hkp)
  simpa only [gaussianMomentConstant, Real.sq_sqrt hkp.le] using hb

lemma gaussian_gram_inverse_moment_centered (k m : ℕ) (hk : 1 ≤ k)
    (hd : k+m ≤ Module.finrank ℝ E) :
    (∫⁻ v : Fin m → E,
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹ ^ k)
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (gaussianMomentConstant k)^m := by
  simpa only [sub_zero] using gaussian_gram_inverse_moment k m hk hd (0 : E)

lemma ae_gaussian_columns_independent (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∀ᵐ v : Fin m → E ∂Measure.pi (fun _ => stdGaussian E), LinearIndependent ℝ v := by
  have h := ae_replica_independent_of_affine_null (ν := stdGaussian E) (0 : E) m ?_
  · simpa only [sub_zero] using h
  intro L hL hdim
  apply stdGaussian_absolutelyContinuous_volume
  apply Measure.addHaar_affineSubspace _ L
  intro htop
  have hr : L.direction = ⊤ := by rw [htop, AffineSubspace.direction_top]
  rw [hr, finrank_top] at hdim
  omega

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianLogMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gramVolume_eq_prod [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {m : ℕ} (v : Fin m → E) :
    gramVolume v = ∏ i, ‖gramSchmidt ℝ v i‖ := PosteriorRegression.sqrt_det_gram m v

@[fun_prop] lemma measurable_gramVolume {m : ℕ} : Measurable (gramVolume : (Fin m → E) → ℝ) := by
  change Measurable (fun v : Fin m → E => gramVolume v)
  simp_rw [gramVolume_eq_prod]
  exact Finset.measurable_prod _ (fun i _ => (PosteriorRegression.measurable_gramSchmidt i).norm)

lemma gramVolume_pos {m : ℕ} {v : Fin m → E} (hv : LinearIndependent ℝ v) :
    0 < gramVolume v := by
  rw [gramVolume_eq_prod]
  exact Finset.prod_pos fun i _ => norm_pos_iff.mpr (gramSchmidt_ne_zero i hv)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_GaussianWishart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma wishartMoment_bound {ℓ m k : ℕ} (hk : 1 ≤ k) (hkm : k+m ≤ ℓ) :
    wishartMoment ℓ m k ≤ gaussianMomentConstant k ^ m := by
  exact gaussian_gram_inverse_moment_centered k m hk (by simpa using hkm)

lemma wishartMoment_ne_top {ℓ m k : ℕ} (hk : 1 ≤ k) (hkm : k+m ≤ ℓ) :
    wishartMoment ℓ m k ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.pow_ne_top (gaussianMomentConstant_ne_top k)) (wishartMoment_bound hk hkm)

lemma wishartMoment_pos {ℓ m k : ℕ} (hm : m ≤ ℓ) : 0 < wishartMoment ℓ m k := by
  unfold wishartMoment
  apply (lintegral_pos_iff_support (by fun_prop)).mpr
  have h : ∀ᵐ G : Rows ℓ m ∂gaussianRows ℓ m, 0 < ENNReal.ofReal ((gramVolume G)⁻¹^k) := by
    filter_upwards [ae_gaussian_columns_independent (E := Vec ℓ) m (by simpa using hm)] with G hG
    exact ENNReal.ofReal_pos.mpr (pow_pos (inv_pos.mpr (gramVolume_pos hG)) _)
  have he : (gaussianRows ℓ m) (Function.support (fun G : Rows ℓ m => ENNReal.ofReal ((gramVolume G)⁻¹^k))) = 1 := by
    apply (ae_iff_prob_eq_one (by fun_prop)).mp
    filter_upwards [h] with G hG
    exact hG.ne'
  rw [he]
  norm_num

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_LabelEllipsoids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma label_closedBall_volume {k : ℕ} (r : ℝ) :
    (volume : Measure (Labels k)) {y | labelNorm y ≤ r} =
      volume (closedBall (0 : Vec k) r) := by
  rw [← (PiLp.volume_preserving_toLp (Fin k)).measure_preimage (by measurability)]
  congr 1
  ext y
  simp [labelNorm, mem_closedBall, dist_zero_right]

lemma label_closedBall_scale {k : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Labels k)) {y | labelNorm y ≤ r} =
      ENNReal.ofReal (r^k) * volume {y : Labels k | labelNorm y ≤ 1} := by
  rw [label_closedBall_volume, label_closedBall_volume]
  simpa using Measure.addHaar_closedBall_mul (volume : Measure (Vec k)) (0 : Vec k) hr (by norm_num : (0:ℝ) ≤ 1)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_BinCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma real_pow_cutoff {d k : ℕ} {L : ℝ} (hL : 1 ≤ L) :
    L*(72:ℝ)^d*(1/2)^binCutoff d k L*(1+2^(k+1)) ≤ 1 := by
  have hLp : 0 < L := by linarith
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hceil := Nat.le_ceil (2*Real.log L)
  have hpowL : L ≤ (2:ℝ)^Nat.ceil (2*Real.log L) := by
    apply (Real.log_le_log_iff hLp (by positivity)).mp
    rw [Real.log_pow]
    nlinarith [mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α:=ℝ) (Nat.ceil (2*Real.log L)))]
  have h72 : (72:ℝ)^d ≤ 2^(7*d) := by
    calc
      _ ≤ ((2:ℝ)^7)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
      _ = _ := (pow_mul _ _ _).symm
  have hsum : (1:ℝ)+2^(k+1) ≤ 2^(k+2) := by
    have h := one_le_pow₀ (show (1:ℝ)≤2 by norm_num) (n:=k+1)
    norm_num [pow_add] at h ⊢
    linarith
  have hp : L*(72:ℝ)^d*(1+2^(k+1)) ≤ 2^binCutoff d k L := by
    calc
      _ ≤ (2:ℝ)^Nat.ceil (2*Real.log L)*2^(7*d)*2^(k+2) :=
        mul_le_mul (mul_le_mul hpowL h72 (by positivity) (by positivity)) hsum (by positivity) (by positivity)
      _ = _ := by rw [← pow_add,← pow_add]; congr 1; unfold binCutoff; omega
  calc
    _ = (L*(72:ℝ)^d*(1+2^(k+1)))*(1/2)^binCutoff d k L := by ring
    _ ≤ (2:ℝ)^binCutoff d k L * (1/2)^binCutoff d k L := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

lemma binCutoff_bound {d k : ℕ} (hk : k≤d) {L : ℝ} (hL : 1≤L) :
    (binCutoff d k L : ℝ)+2 ≤ 16*(1+(d:ℝ)+Real.log L) := by
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.log_nonneg hL))).le
  have hkr : (k:ℝ)≤d := by exact_mod_cast hk
  unfold binCutoff
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) d,Real.log_nonneg hL]

lemma binCutoff_valid {d k : ℕ} {L : ℝ} (hL : 1≤L) :
    (ENNReal.ofReal L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^binCutoff d k L)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1 := by
  have hh := ENNReal.ofReal_le_ofReal (real_pow_cutoff (d:=d) (k:=k) hL)
  have hL0 : 0 ≤ L := by linarith
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul hL0,
    ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2)] at hh
  simpa only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat] using hh

lemma binCutoff_log_bound {d k : ℕ} (hk : k≤d) {L : ℝ} (hL : 1≤L) :
    Real.log ((binCutoff d k L:ℝ)+2) ≤ 16+Real.log (1+(d:ℝ)+Real.log L) := by
  have ha : 0 < 1+(d:ℝ)+Real.log L := by linarith [Nat.cast_nonneg (α:=ℝ) d,Real.log_nonneg hL]
  have hh := Real.log_le_log (by positivity : 0<(binCutoff d k L:ℝ)+2) (binCutoff_bound hk hL)
  rw [Real.log_mul (by norm_num) ha.ne'] at hh
  linarith [Real.log_le_self (by norm_num : (0:ℝ)≤16)]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_DensityRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_normalizedRatio {d ℓ k m : ℕ} {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (@normalizedRatio d ℓ k m f) := by unfold normalizedRatio labels; fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_ReplicaGaussianMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

@[fun_prop] lemma measurable_projectionGramRatio {d ℓ k m : ℕ} :
    Measurable (@projectionGramRatio d ℓ k m) := by unfold projectionGramRatio; fun_prop

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ReplicaLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma label_unitBall_ne_top (k : ℕ) : (volume {y : Labels k | labelNorm y ≤ 1}) ≠ ∞ := by
  rw [label_closedBall_volume]
  exact measure_closedBall_lt_top.ne

lemma label_unitBall_pos (k : ℕ) : 0 < (volume {y : Labels k | labelNorm y ≤ 1}) := by
  rw [label_closedBall_volume]
  exact (measure_ball_pos volume (0 : Vec k) (by norm_num : (0:ℝ)<1)).trans_le
    (measure_mono ball_subset_closedBall)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ReplicaCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma gaussianMomentConstant_log_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log (gaussianMomentConstant k).toReal ≤ -(k:ℝ)/2*Real.log k + 4*k := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have he : (gaussianMomentConstant k).toReal = (Real.sqrt k)⁻¹^k *
      (1+Real.exp ((k:ℝ)/2)*2^(k+1)) := by
    unfold gaussianMomentConstant
    rw [ENNReal.toReal_mul,ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_mul]
    simp only [ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (Real.sqrt (k:ℝ))⁻¹^k),
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [he,Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_inv,
    Real.log_sqrt hkp.le]
  have hone : (1:ℝ) ≤ Real.exp ((k:ℝ)/2)*2^(k+1) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp_iff.mpr (by positivity)) (one_le_pow₀ (by norm_num))
  have hlog := Real.log_le_log (by positivity : 0 < 1+Real.exp ((k:ℝ)/2)*2^(k+1))
    (show 1+Real.exp ((k:ℝ)/2)*2^(k+1) ≤ 2*(Real.exp ((k:ℝ)/2)*2^(k+1)) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_mul (Real.exp_pos _).ne' (by positivity),
    Real.log_exp,Real.log_pow] at hlog
  have hl2 : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
  push_cast at hlog
  nlinarith [mul_le_mul_of_nonneg_left hl2 (show 0 ≤ (k:ℝ)+2 by positivity)]

lemma wishartMoment_log_le {ℓ m k : ℕ} (hk : 1 ≤ k) (hkm : k+m ≤ ℓ) :
    Real.log (wishartMoment ℓ m k).toReal ≤ (m:ℝ)*(-(k:ℝ)/2*Real.log k + 4*k) := by
  have hp := ENNReal.toReal_pos (wishartMoment_pos (by omega : m ≤ ℓ)).ne' (wishartMoment_ne_top hk hkm)
  have ht := ENNReal.pow_ne_top (gaussianMomentConstant_ne_top k) (n := m)
  have hb := (ENNReal.toReal_le_toReal (wishartMoment_ne_top hk hkm) ht).mpr (wishartMoment_bound hk hkm)
  have hlog := Real.log_le_log hp hb
  rw [ENNReal.toReal_pow,Real.log_pow] at hlog
  exact hlog.trans (mul_le_mul_of_nonneg_left (gaussianMomentConstant_log_le hk) (Nat.cast_nonneg m))

lemma label_unitBall_log_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log (volume {y : Labels k | labelNorm y ≤ 1}).toReal ≤
      (k:ℝ)/2*(Real.log (2*Real.pi)+1-Real.log k) := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have h := gaussian_density_ball_lower (E := Vec k) (Real.sqrt_nonneg (k:ℝ))
  rw [← label_closedBall_volume, label_closedBall_scale (Real.sqrt_nonneg (k:ℝ))] at h
  simp only [finrank_euclideanSpace_fin,Real.sq_sqrt hkp.le] at h
  have hr := ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ∞) h
  simp only [ENNReal.toReal_mul,ENNReal.toReal_one,ENNReal.toReal_ofReal (by positivity :
    0 ≤ (2*Real.pi)^(-(k:ℝ)/2)*Real.exp (-(k:ℝ)/2)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (Real.sqrt (k:ℝ))^k)] at hr
  have hv : 0 < (volume {y : Labels k | labelNorm y ≤ 1}).toReal :=
    ENNReal.toReal_pos (label_unitBall_pos k).ne' (label_unitBall_ne_top k)
  have hp : 0 < (2*Real.pi)^(-(k:ℝ)/2)*Real.exp (-(k:ℝ)/2) := by positivity
  have hh := Real.log_le_log (mul_pos hp (mul_pos (pow_pos (Real.sqrt_pos.mpr hkp) _) hv)) hr
  rw [Real.log_one,Real.log_mul hp.ne' (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity),Real.log_exp,Real.log_mul (by positivity) hv.ne',Real.log_pow,
    Real.log_sqrt hkp.le] at hh
  linarith

lemma binMeanBound_log_le {k : ℕ} (hk : 1 ≤ k) (J : ℕ) :
    Real.log (binMeanBound k J) ≤ (k:ℝ)/2*(Real.log (2*Real.pi)+1-Real.log k)+
      Real.log ((J:ℝ)+2)+(k:ℝ)*Real.log 2 := by
  have hv : 0 < (volume {y : Labels k | labelNorm y ≤ 1}).toReal :=
    ENNReal.toReal_pos (label_unitBall_pos k).ne' (label_unitBall_ne_top k)
  rw [binMeanBound,Real.log_mul hv.ne' (by positivity)]
  have hb : (2+(J:ℝ)*2^k) ≤ ((J:ℝ)+2)*2^k := by
    have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    nlinarith
  have hh := Real.log_le_log (by positivity : (0:ℝ)<2+(J:ℝ)*2^k) hb
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hh
  linarith [label_unitBall_log_le hk]

lemma scaled_dimension_log_le {n k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a)
    (hn : (n:ℝ)+1 ≤ a*k) : Real.log ((n:ℝ)+1) ≤ Real.log k + a := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have h := Real.log_le_log (by positivity : (0:ℝ)<(n:ℝ)+1) hn
  rw [Real.log_mul ha.ne' hkp.ne'] at h
  linarith [Real.log_le_self ha.le]

lemma comparisonCost_le {d ℓ k m : ℕ} (hk : 1 ≤ k) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k) (J : ℕ) :
    comparisonCost d ℓ k m J ≤ (m:ℝ)*((40+Real.pi)*(k:ℝ)+Real.log ((J:ℝ)+2)) := by
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hdn : (d:ℝ) ≤ 32*k := by exact_mod_cast hdk
  have hℓn : (ℓ:ℝ) ≤ 16*k := by exact_mod_cast hℓk
  have hl := scaled_dimension_log_le hk (by norm_num : (0:ℝ)<17) (by linarith : (ℓ:ℝ)+1≤17*k)
  have hd := scaled_dimension_log_le hk (by norm_num : (0:ℝ)<33) (by linarith : (d:ℝ)+1≤33*k)
  have hZ := wishartMoment_log_le hk hkm
  have hB := binMeanBound_log_le hk J
  have hL2 : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hLp : Real.log (2*Real.pi) ≤ 2*Real.pi := Real.log_le_self (by positivity)
  have hk0 : 0 ≤ (k:ℝ) := by positivity
  have hm0 : 0 ≤ (m:ℝ) := by positivity
  have hl' := mul_le_mul_of_nonneg_left hl (show 0 ≤ (k:ℝ)*(m:ℝ)/2 by positivity)
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ (m:ℝ)*(k:ℝ)/2 by positivity)
  have hB' := mul_le_mul_of_nonneg_left hB hm0
  have hL2' := mul_le_mul_of_nonneg_left hL2 (show 0 ≤ (m:ℝ)*(k:ℝ) by positivity)
  have hLp' := mul_le_mul_of_nonneg_left hLp (show 0 ≤ (m:ℝ)*(k:ℝ)/2 by positivity)
  unfold comparisonCost
  nlinarith [mul_nonneg hm0 hk0]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_GenericInformationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma spherical_density_bound_one_le {d : ℕ} (hd : 0 < d)
    {f : Vec d → ℝ} {L : ℝ} (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)))] : 1 ≤ L := by
  let : NeZero d := ⟨hd.ne'⟩
  have : IsProbabilityMeasure (sphereLaw d) := by
    change IsProbabilityMeasure (BaseLaw.spherical.measure d); infer_instance
  apply ENNReal.one_le_ofReal.mp
  calc
    (1:ℝ≥0∞) = ((sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x))) univ := (measure_univ).symm
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂sphereLaw d := by rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    _ ≤ ∫⁻ _x, ENNReal.ofReal L ∂sphereLaw d := lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfL x))
    _ = ENNReal.ofReal L := by simp

lemma gaussian_replica_information {d ℓ k m N : ℕ} [NeZero N]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ} (hL : 1 ≤ L)
    (hfL : ∀ x, f x ≤ ENNReal.ofReal L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    conditionalInformation (sideLaw ℓ (signalMessageLaw ((sphereLaw d).withDensity f) κ)) ≤
      ENNReal.ofReal (messageEntropy (signalMessageLaw ((sphereLaw d).withDensity f) κ) / ((m+1:ℕ):ℝ) +
        (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)+Real.log L)) := by
  have hi := gaussian_replica_information_cost hd hk hm hkm hf ENNReal.ofReal_ne_top hfL κ
    (binCutoff d k L) (binCutoff_valid hL)
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hcost := comparisonCost_le hk hkm hdk hℓk (binCutoff d k L)
  have hlog := binCutoff_log_bound (by omega : k≤d) hL
  have hmm : 0 ≤ (m:ℝ) := by positivity
  have hkr : (k:ℝ) ≤ d := by exact_mod_cast (by omega : k≤d)
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1≤d)
  have hln : 0 ≤ Real.log (1+(d:ℝ)+Real.log L) := Real.log_nonneg (by linarith [Real.log_nonneg hL])
  have hb : (40+Real.pi)*(k:ℝ)+Real.log ((binCutoff d k L:ℝ)+2) ≤
      (100+Real.pi)*(d:ℝ)+Real.log (1+(d:ℝ)+Real.log L) := by
    nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left hkr (show (0:ℝ)≤40+Real.pi by positivity)]
  have ha : 0 ≤ (100+Real.pi)*(d:ℝ)+Real.log (1+(d:ℝ)+Real.log L) := by positivity
  have hb' := mul_le_mul_of_nonneg_left hb hmm
  have hm1 : ((m+1:ℕ):ℝ) = (m:ℝ)+1 := by norm_cast
  rw [hm1]
  rw [add_assoc]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(m:ℝ)+1)).mpr
  rw [add_mul,div_mul_cancel₀ _ (by positivity : (m:ℝ)+1 ≠ 0)]
  nlinarith

lemma gaussian_replica_information_real {d ℓ k m N : ℕ} [NeZero N]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k)
    (p : Measure (Vec d)) [IsProbabilityMeasure p]
    {f : Vec d → ℝ} (hf : Measurable f) {L : ℝ} (hL : 1 ≤ L)
    (hfL : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hp : p = (sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x)))
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    conditionalInformation (sideLaw ℓ (signalMessageLaw p κ)) ≤
      ENNReal.ofReal (messageEntropy (signalMessageLaw p κ) / ((m+1:ℕ):ℝ) +
        (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)+Real.log L)) := by
  subst p
  exact gaussian_replica_information hd hk hm hkm hdk hℓk hf.ennreal_ofReal hL
    (fun x => ENNReal.ofReal_le_ofReal (hfL x).2) κ

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_HeadlineInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma priorLog_le_dimension_add_log {d : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1+(d:ℝ)+u) ≤ (d:ℝ)+Real.log (1+u) := by
  have hd : 0 ≤ (d:ℝ) := by positivity
  have hh := Real.log_le_log (by positivity : 0<1+(d:ℝ)+u)
    (show 1+(d:ℝ)+u ≤ (1+(d:ℝ))*(1+u) by nlinarith)
  rw [Real.log_mul (by positivity) (by positivity)] at hh
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0<1+(d:ℝ))
  linarith

theorem gaussianReplicaBlock_oai : GaussianReplicaBlock := by
  refine ⟨200+Real.pi,by positivity,64,?_⟩
  intro d hd
  dsimp only
  intro p hp f L hf hfL hpf N hN κ hκ
  have hL : 1 ≤ L := by
    have : IsProbabilityMeasure ((sphereLaw d).withDensity (fun x => ENNReal.ofReal (f x))) := hpf ▸ hp
    exact spherical_density_bound_one_le (by omega) (fun x => (hfL x).2)
  have hi := gaussian_replica_information_real (m := 2*(d/16))
    (by omega : 4*(2*(d/16))+2*(d/16)+2≤d) (by omega) (by omega)
    (by omega : 2*(d/16)+2*(d/16)≤4*(2*(d/16))) (by omega) (by omega)
    p hf hL hfL hpf κ
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hlog := priorLog_le_dimension_add_log (d:=d) (Real.log_nonneg hL)
  have hmono := Real.log_le_log (by linarith [Real.log_nonneg hL] : 0<1+Real.log L)
    (show 1+Real.log L ≤ 2+Real.log L by linarith)
  have hpos := Real.log_nonneg (show 1≤2+Real.log L by linarith [Real.log_nonneg hL])
  have hdp : 0 ≤ (d:ℝ) := by positivity
  nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le hpos]

end PosteriorReplicas
end

end OAI
end

theorem solution : type_of% @OAI.PosteriorReplicas.gaussianReplicaBlock_oai := @OAI.PosteriorReplicas.gaussianReplicaBlock_oai
