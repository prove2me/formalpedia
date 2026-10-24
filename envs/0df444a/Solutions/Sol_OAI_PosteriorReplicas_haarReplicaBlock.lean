-- Prove2me | solution 1 for OAI.PosteriorReplicas.haarReplicaBlock
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:48:48.911185+00:00
-- url     : https://prove2.me/submissions/1fac227b-1cf4-4fbf-84b4-b26b6f3c0db3

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

section PairingsDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pairingTriangular_expansion [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (j : Fin n) : ∑ i, pairingTriangular v i j • gramSchmidtNormed ℝ v i = v j := by
  have hn (i : Fin n) : ‖gramSchmidt ℝ v i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)
  rw [← PosteriorRegression.gsUpper_expansion n v j]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pairingTriangular, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
  congr 1
  simp [hn i, mul_comm]

lemma pairingTriangular_det [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (v : Fin n → E) :
    (pairingTriangular v).transpose.det = Real.sqrt (Matrix.gram ℝ v).det := by
  rw [pairingTriangular, Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal,
    PosteriorRegression.gsUpper_det, mul_one, PosteriorRegression.sqrt_det_gram]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma pairingTriangular_det_pos {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) :
    0 < (pairingTriangular v).transpose.det := by
  rw [pairingTriangular_det]
  exact Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hv).det_pos

lemma pairings_eq_triangular {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) :
    (fun x : E => fun j => ⟪v j, x⟫) =
      (Matrix.toLin' (pairingTriangular v).transpose) ∘
        (fun x => fun i => ⟪gramSchmidtNormed ℝ v i, x⟫) := by
  funext x j
  rw [← pairingTriangular_expansion hv j]
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, sum_inner, inner_smul_left]

end PairingsDensity
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
-- module Solutions.OAIQW_PosteriorReplicas.Information_KLTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma klDiv_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : X ≃ᵐ Y) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le _ _ e.measurable)
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self, Measure.map_id] using h

lemma klDiv_swap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure (X × Y)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map Prod.swap) (ν.map Prod.swap) = klDiv μ ν :=
  klDiv_map_equiv μ ν MeasurableEquiv.prodComm

lemma klDiv_prod_first_chain {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y]
    (q : Measure (X × Y)) [IsProbabilityMeasure q]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν] :
    klDiv q (μ.prod ν) = klDiv q.fst μ + klDiv q (q.fst.prod ν) := by
  have h := klDiv_compProd_eq_add q.fst μ q.condKernel (Kernel.const X ν)
  simpa only [Measure.disintegrate q q.condKernel, Measure.compProd_const] using h

lemma klDiv_prod_decomposition {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (q : Measure (X × Y)) [IsProbabilityMeasure q]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν] :
    klDiv q (μ.prod ν) = klDiv q.fst μ + klDiv q.snd ν + klDiv q (q.fst.prod q.snd) := by
  rw [klDiv_prod_first_chain]
  haveI : IsProbabilityMeasure (q.map Prod.swap) := Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  have h := klDiv_prod_first_chain (q.map Prod.swap) ν q.fst
  rw [Measure.fst_map_swap] at h
  have h1 : klDiv (q.map Prod.swap) (ν.prod q.fst) = klDiv q (q.fst.prod ν) := by
    rw [← Measure.prod_swap, klDiv_swap]
  have h2 : klDiv (q.map Prod.swap) (q.snd.prod q.fst) = klDiv q (q.fst.prod q.snd) := by
    rw [← Measure.prod_swap, klDiv_swap]
  rw [h1, h2] at h
  rw [h, add_assoc]

section KernelKL
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountableOrCountablyGenerated X Y]
  (μ : Measure X) [IsFiniteMeasure μ] (κ η : Kernel X Y)
  [IsMarkovKernel κ] [IsMarkovKernel η]

lemma withDensity_kernel_rnDeriv (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (μ ⊗ₘ η).withDensity (fun z => κ.rnDeriv η z.1 z.2) = μ ⊗ₘ κ := by
  rw [← Measure.compProd_withDensity (Kernel.measurable_rnDeriv κ η)]
  apply Measure.compProd_congr
  filter_upwards [hac] with x hx
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv κ η)]
  rw [withDensity_congr_ae (Kernel.rnDeriv_eq_rnDeriv_measure), Measure.withDensity_rnDeriv_eq _ _ hx]

lemma rnDeriv_compProd_kernel (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] (fun z => κ.rnDeriv η z.1 z.2) := by
  conv_lhs => rw [← withDensity_kernel_rnDeriv μ κ η hac]
  exact Measure.rnDeriv_withDensity _ (Kernel.measurable_rnDeriv κ η)

lemma klDiv_compProd_kernel_integral (hac : ∀ᵐ x ∂μ, κ x ≪ η x) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  rw [klDiv_eq_lintegral_klFun_of_ac (Measure.AbsolutelyContinuous.compProd_right hac)]
  calc
    _ = ∫⁻ z, ENNReal.ofReal (klFun (κ.rnDeriv η z.1 z.2).toReal) ∂μ ⊗ₘ η := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_compProd_kernel μ κ η hac] with z hz
      rw [hz]
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (klFun (κ.rnDeriv η x y).toReal) ∂η x ∂μ := by
      rw [Measure.lintegral_compProd (by fun_prop)]
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hac] with x hx
      rw [klDiv_eq_lintegral_klFun_of_ac hx]
      apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := x)] with y hy
      rw [hy]

lemma measurable_kernel_klDiv : Measurable (fun x => klDiv (κ x) (η x)) := by
  classical
  have he : (fun x => klDiv (κ x) (η x)) = fun x =>
      if κ x ≪ η x then ∫⁻ y, ENNReal.ofReal (klFun (κ.rnDeriv η x y).toReal) ∂η x
      else ∞ := by
    funext x
    split_ifs with hx
    · rw [klDiv_eq_lintegral_klFun_of_ac hx]
      apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := x)] with y hy
      rw [hy]
    · exact klDiv_of_not_ac hx
  rw [he]
  apply Measurable.ite (Kernel.measurableSet_absolutelyContinuous κ η) _ measurable_const
  exact Measurable.lintegral_kernel_prod_right' (κ := η) (by
    exact ENNReal.measurable_ofReal.comp (continuous_klFun.measurable.comp
      (Kernel.measurable_rnDeriv κ η).ennreal_toReal))

lemma klDiv_compProd_kernel :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  by_cases hac : ∀ᵐ x ∂μ, κ x ≪ η x
  · exact klDiv_compProd_kernel_integral μ κ η hac
  · have hnot : ¬ μ ⊗ₘ κ ≪ μ ⊗ₘ η := fun h => hac h.kernel_of_compProd
    rw [klDiv_of_not_ac hnot]
    apply (eq_top_iff.mpr _).symm
    by_contra h
    have hfin : (∫⁻ x, klDiv (κ x) (η x) ∂μ) < ∞ := lt_of_not_ge h
    have ha := ae_lt_top (measurable_kernel_klDiv κ η) hfin.ne
    apply hac
    filter_upwards [ha] with x hx
    exact (klDiv_ne_top_iff.mp hx.ne).1

end KernelKL
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ConditionalKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section Conditional
variable {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
  (μ : Measure Z) [IsFiniteMeasure μ]
  (κ : Kernel Z (X × Y)) (η : Kernel Z X) (ρ : Kernel Z Y)
  [IsMarkovKernel κ] [IsMarkovKernel η] [IsMarkovKernel ρ]

lemma klDiv_kernel_prod_decomposition :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (η ×ₖ ρ)) =
      klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) +
      klDiv (μ ⊗ₘ κ.fst) (μ ⊗ₘ η) + klDiv (μ ⊗ₘ κ.snd) (μ ⊗ₘ ρ) := by
  simp_rw [klDiv_compProd_kernel]
  calc
    _ = ∫⁻ z, (klDiv (κ z) ((κ.fst ×ₖ κ.snd) z) +
        klDiv (κ.fst z) (η z)) + klDiv (κ.snd z) (ρ z) ∂μ := by
      apply lintegral_congr
      intro z
      have h := klDiv_prod_decomposition (κ z) (η z) (ρ z)
      simpa only [Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply,
        Measure.fst, Measure.snd, add_assoc, add_comm, add_left_comm] using h
    _ = _ := by
      rw [lintegral_add_aux (by
          exact ((measurable_kernel_klDiv κ (κ.fst ×ₖ κ.snd)).add
            (measurable_kernel_klDiv κ.fst η)))
          (measurable_kernel_klDiv κ.snd ρ),
        lintegral_add_aux (measurable_kernel_klDiv κ (κ.fst ×ₖ κ.snd))
          (measurable_kernel_klDiv κ.fst η)]

end Conditional

lemma cmi_eq_kernel_integral {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (q : Measure (Z × (X × Y))) [IsFiniteMeasure q] :
    cmi q = ∫⁻ z, klDiv (q.condKernel z)
      ((q.condKernel z).fst.prod (q.condKernel z).snd) ∂q.fst := by
  unfold cmi
  conv_lhs => lhs; rw [← Measure.disintegrate q q.condKernel]
  rw [klDiv_compProd_kernel]
  simp only [Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply, Measure.fst, Measure.snd]

lemma klDiv_conditional_chain {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (q : Measure (Z × (X × Y))) [IsProbabilityMeasure q]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    klDiv q (q.fst ⊗ₘ (q.condKernel.fst ×ₖ Kernel.const Z ν)) =
      cmi q + klDiv (q.map (fun z => (z.1, z.2.2))) (q.fst.prod ν) := by
  have h := klDiv_kernel_prod_decomposition q.fst q.condKernel q.condKernel.fst
    (Kernel.const Z ν)
  rw [Measure.disintegrate q q.condKernel, klDiv_self, add_zero, Measure.compProd_const] at h
  rw [Kernel.snd_eq, Measure.compProd_map measurable_snd,
    Measure.disintegrate q q.condKernel] at h
  have hm : (Prod.map id Prod.snd : Z × (X × Y) → Z × Y) = (fun z => (z.1,z.2.2)) := by
    funext z
    rfl
  rw [hm] at h
  simpa only [cmi, Kernel.snd_eq] using h

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_FiniteKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section Finite
variable {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]

omit [MeasurableSingletonClass W] in
lemma finite_ac_of_singleton {μ ν : Measure W}
    (h : ∀ w, ν {w} = 0 → μ {w} = 0) : μ ≪ ν := by
  intro s hs
  apply measure_eq_zero_iff_ae_notMem.mpr
  apply ae_iff_of_countable.mpr
  intro w hw hws
  exact hw (h w (measure_mono_null (singleton_subset_iff.mpr hws) hs))

lemma finite_withDensity_ratio (μ ν : Measure W) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) : ν.withDensity (fun w => μ {w} / ν {w}) = μ := by
  apply Measure.ext_of_singleton
  intro w
  rw [withDensity_apply _ (measurableSet_singleton w), lintegral_singleton]
  by_cases h : ν {w} = 0
  · simp [h, hac h]
  · exact ENNReal.div_mul_cancel h (measure_ne_top ν {w})

lemma finite_llr_ratio (μ ν : Measure W) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) : llr μ ν =ᵐ[μ] (fun w => Real.log (μ.real {w} / ν.real {w})) := by
  have hd : μ.rnDeriv ν =ᵐ[ν] (fun w => μ {w} / ν {w}) := by
    conv_lhs => rw [← finite_withDensity_ratio μ ν hac]
    exact Measure.rnDeriv_withDensity _ (measurable_of_countable _)
  filter_upwards [hac.ae_le hd] with w hw
  simp only [llr, hw, ENNReal.toReal_div, measureReal_def]

lemma finite_klDiv_formula (μ ν : Measure W) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) :
    klDiv μ ν = ENNReal.ofReal (∑ w, μ.real {w} * Real.log (μ.real {w} / ν.real {w})) := by
  rw [klDiv_of_ac_of_integrable hac Integrable.of_finite]
  rw [integral_congr_ae (finite_llr_ratio μ ν hac), integral_fintype Integrable.of_finite]
  simp [smul_eq_mul, measureReal_def]

lemma finite_klDiv_le_crossEntropy (μ ν : Measure W)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    klDiv μ ν ≤ ENNReal.ofReal (∑ w, μ.real {w} * (-Real.log (ν.real {w}))) := by
  rw [finite_klDiv_formula μ ν hac]
  apply ENNReal.ofReal_le_ofReal
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : μ {w} = 0
  · simp [measureReal_def, hw]
  · have hw' : 0 < μ.real {w} := ENNReal.toReal_pos hw (measure_ne_top μ {w})
    have hv : ν {w} ≠ 0 := fun h => hw (hac h)
    have hv' : 0 < ν.real {w} := ENNReal.toReal_pos hv (measure_ne_top ν {w})
    rw [Real.log_div hw'.ne' hv'.ne']
    apply mul_le_mul_of_nonneg_left _ hw'.le
    have hl := Real.log_nonpos hw'.le (measureReal_le_one (μ := μ) (s := {w}))
    linarith

omit [MeasurableSingletonClass W] in
lemma finite_crossEntropy_nonneg (μ ν : Measure W)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ ∑ w, μ.real {w} * (-Real.log (ν.real {w})) := by
  apply Finset.sum_nonneg
  intro w _
  apply mul_nonneg measureReal_nonneg
  exact neg_nonneg.mpr (Real.log_nonpos measureReal_nonneg measureReal_le_one)

end Finite

section Kernel
variable {X W : Type*} [MeasurableSpace X] [Fintype W] [MeasurableSpace W]
  [MeasurableSingletonClass W]
  (μ : Measure X) [IsProbabilityMeasure μ] (κ : Kernel X W) [IsMarkovKernel κ]

lemma ae_kernel_ac_marginal : ∀ᵐ x ∂μ, κ x ≪ (μ ⊗ₘ κ).snd := by
  have h : ∀ w : W, ∀ᵐ x ∂μ, (μ ⊗ₘ κ).snd {w} = 0 → κ x {w} = 0 := by
    intro w
    by_cases hw : (μ ⊗ₘ κ).snd {w} = 0
    · have he : (∫⁻ x, κ x {w} ∂μ) = 0 := by
        rw [Measure.snd_compProd, Measure.bind_apply (measurableSet_singleton w) κ.measurable.aemeasurable] at hw
        exact hw
      filter_upwards [(lintegral_eq_zero_iff (Kernel.measurable_coe κ (measurableSet_singleton w))).mp he]
        with x hx
      exact fun _ => hx
    · exact ae_of_all _ (fun _ => fun h => (hw h).elim)
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact finite_ac_of_singleton hx

omit [Fintype W] in
lemma integrable_kernel_atom (w : W) : Integrable (fun x => (κ x).real {w}) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    ((Kernel.measurable_coe κ (measurableSet_singleton w)).ennreal_toReal.aestronglyMeasurable)
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, measureReal_def] using
    (measureReal_le_one (μ := κ x) (s := {w}))

omit [Fintype W] in
lemma integral_kernel_atom (w : W) :
    ∫ x, (κ x).real {w} ∂μ = (μ ⊗ₘ κ).snd.real {w} := by
  rw [measureReal_def, Measure.snd_compProd,
    Measure.bind_apply (measurableSet_singleton w) κ.measurable.aemeasurable]
  simp only [measureReal_def]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    ((Kernel.measurable_coe κ (measurableSet_singleton w)).ennreal_toReal.aestronglyMeasurable)]
  congr 1
  apply lintegral_congr
  intro x
  exact ENNReal.ofReal_toReal (measure_ne_top (κ x) {w})

lemma klDiv_kernel_le_finiteEntropy :
    klDiv (μ ⊗ₘ κ) (μ.prod (μ ⊗ₘ κ).snd) ≤
      ENNReal.ofReal (finiteEntropy (μ ⊗ₘ κ).snd) := by
  rw [← Measure.compProd_const, klDiv_compProd_kernel]
  let ν := (μ ⊗ₘ κ).snd
  have hi : Integrable (fun x => ∑ w : W, (κ x).real {w} * (-Real.log (ν.real {w}))) μ := by
    apply integrable_finsetSum
    intro w _
    exact (integrable_kernel_atom μ κ w).mul_const _
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (∑ w : W, (κ x).real {w} * (-Real.log (ν.real {w}))) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_kernel_ac_marginal μ κ] with x hx
      exact finite_klDiv_le_crossEntropy (κ x) ν hx
    _ = ENNReal.ofReal (∫ x, ∑ w : W, (κ x).real {w} * (-Real.log (ν.real {w})) ∂μ) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => finite_crossEntropy_nonneg (κ x) ν)
    _ = _ := by
      rw [integral_finsetSum _ (fun w _ => (integrable_kernel_atom μ κ w).mul_const _)]
      simp_rw [integral_mul_const, integral_kernel_atom μ κ]
      congr 1
      unfold finiteEntropy
      apply Finset.sum_congr rfl
      intro w _
      ring

end Kernel

lemma mutualInformation_le_finiteEntropy {X W : Type*} [MeasurableSpace X]
    [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    [StandardBorelSpace W] [Nonempty W]
    (q : Measure (X × W)) [IsProbabilityMeasure q] :
    klDiv q (q.fst.prod q.snd) ≤ ENNReal.ofReal (finiteEntropy q.snd) := by
  have h := klDiv_kernel_le_finiteEntropy q.fst q.condKernel
  simpa only [Measure.disintegrate q q.condKernel] using h

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_GraphKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma klDiv_map_leftInverse {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : X → Y} {g : Y → X} (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) : klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le _ _ hf)
  have h := klDiv_map_le (μ.map f) (ν.map f) hg
  have he : g ∘ f = id := funext hgf
  simpa only [Measure.map_map hg hf, he, Measure.map_id] using h

lemma compProd_prod_right {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) [SFinite μ] (κ : Kernel Z X) [IsSFiniteKernel κ]
    (ν : Measure Y) [SFinite ν] :
    ((μ ⊗ₘ κ).prod ν).map MeasurableEquiv.prodAssoc = μ ⊗ₘ (κ ×ₖ Kernel.const Z ν) := by
  have hk : κ ×ₖ Kernel.const Z ν = κ ⊗ₖ Kernel.const (Z × X) ν := by
    ext z s hs
    rw [Kernel.prod_apply' _ _ _ hs, Kernel.compProd_apply hs]
    rfl
  rw [hk, ← Measure.compProd_const, Measure.compProd_assoc']

lemma attachSide_probability {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {g : X → Z} (hg : Measurable g) (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    IsProbabilityMeasure (attachSide g q) :=
  (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

lemma attachSide_first_pair {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {g : X → Z} (hg : Measurable g) (q : Measure (X × Y)) :
    (attachSide g q).map (fun z => (z.1,z.2.1)) = q.fst.map (fun x => (g x,x)) := by
  unfold attachSide Measure.fst
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) measurable_fst]
  rfl

lemma compProd_condKernel_fst {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    (q : Measure (Z × (X × Y))) [IsFiniteMeasure q] :
    q.fst ⊗ₘ q.condKernel.fst = q.map (fun z => (z.1,z.2.1)) := by
  rw [Kernel.fst_eq, Measure.compProd_map measurable_fst, Measure.disintegrate q q.condKernel]
  rfl

lemma attachSide_conditional_reference {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    {g : X → Z} (hg : Measurable g) (q : Measure (X × Y)) [IsProbabilityMeasure q]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    let r := attachSide g q
    r.fst ⊗ₘ (r.condKernel.fst ×ₖ Kernel.const Z ν) = attachSide g (q.fst.prod ν) := by
  let := attachSide_probability hg q
  dsimp only
  rw [← compProd_prod_right, compProd_condKernel_fst, attachSide_first_pair hg]
  have hp : (q.fst.map (fun x => (g x,x))).prod ν =
      (q.fst.prod ν).map (Prod.map (fun x => (g x,x)) id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map q.fst ν
      (show Measurable (fun x => (g x,x)) by fun_prop) measurable_id
  rw [hp]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma mutualInformation_attachSide_chain {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    {g : X → Z} (hg : Measurable g) (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    let r := attachSide g q
    klDiv q (q.fst.prod q.snd) = cmi r +
      klDiv (q.map (fun z => (g z.1,z.2))) ((q.fst.map g).prod q.snd) := by
  let := attachSide_probability hg q
  dsimp only
  have h := klDiv_conditional_chain (attachSide g q) q.snd
  rw [attachSide_conditional_reference hg] at h
  have he : klDiv (attachSide g q) (attachSide g (q.fst.prod q.snd)) = klDiv q (q.fst.prod q.snd) :=
    klDiv_map_leftInverse _ _ (by fun_prop) measurable_snd (fun _ => rfl)
  rw [he] at h
  have hf : (attachSide g q).fst = q.fst.map g := by
    unfold attachSide Measure.fst
    rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_map hg measurable_fst]
    rfl
  have hy : (attachSide g q).map (fun z => (z.1,z.2.2)) =
      q.map (fun z => (g z.1,z.2)) := by
    rw [attachSide, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rwa [hf,hy] at h

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_CmiKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section
variable {Z X Y : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
  (μ : Measure Z) [IsFiniteMeasure μ] (κ : Kernel Z (X × Y)) [IsMarkovKernel κ]

lemma cmi_compProd : cmi (μ ⊗ₘ κ) = klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
  unfold cmi
  rw [Measure.fst_compProd]
  congr 1
  apply Measure.compProd_congr
  filter_upwards [condKernel_compProd μ κ] with z hz
  simp only [Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply, hz]

lemma cmi_compProd_integral : cmi (μ ⊗ₘ κ) =
    ∫⁻ z, mutualInformation (κ z) ∂μ := by
  rw [cmi_compProd, klDiv_compProd_kernel]
  simp only [mutualInformation, Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply,
    Measure.fst, Measure.snd]
end

lemma kernel_compProd_eval {T Z V : Type*}
    [MeasurableSpace T] [MeasurableSpace Z] [MeasurableSpace V]
    (κ : Kernel T Z) [IsSFiniteKernel κ] (η : Kernel (T × Z) V) [IsSFiniteKernel η] (t : T) :
    (κ ⊗ₖ η) t = κ t ⊗ₘ η.comap (fun z => (t,z)) (by fun_prop) := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  rfl

section Tower
variable {T Z X Y : Type*} [MeasurableSpace T] [MeasurableSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Z] [StandardBorelSpace X] [StandardBorelSpace Y]
  [Nonempty X] [Nonempty Y]
  (μ : Measure T) [IsFiniteMeasure μ]
  (κ : Kernel T (Z × (X × Y))) [IsMarkovKernel κ]

lemma cmi_kernel_measurable : Measurable (fun t => cmi (κ t)) := by
  have he (t : T) : cmi (κ t) = klDiv (κ t)
      ((κ.fst ⊗ₖ (κ.condKernel.fst ×ₖ κ.condKernel.snd)) t) := by
    unfold cmi
    congr 1
    rw [kernel_compProd_eval]
    have hf : (κ t).fst = κ.fst t := (Kernel.fst_apply κ t).symm
    rw [hf]
    apply Measure.compProd_congr
    filter_upwards [κ.condKernel_apply_eq_condKernel t] with z hz
    simp only [Kernel.comap_apply, Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply]
    rw [hz]
  simp_rw [he]
  exact measurable_kernel_klDiv _ _

lemma cmi_compProd_assoc :
    cmi ((μ ⊗ₘ κ).map (MeasurableEquiv.prodAssoc.symm :
      T × (Z × (X × Y)) ≃ᵐ (T × Z) × (X × Y))) = ∫⁻ t, cmi (κ t) ∂μ := by
  have ha : (μ ⊗ₘ κ).map (MeasurableEquiv.prodAssoc.symm :
      T × (Z × (X × Y)) ≃ᵐ (T × Z) × (X × Y)) =
      (μ ⊗ₘ κ.fst) ⊗ₘ κ.condKernel := by
    conv_lhs => rw [← Kernel.disintegrate κ κ.condKernel]
    exact Measure.compProd_assoc
  simp only [ha]
  rw [cmi_compProd_integral, Measure.lintegral_compProd]
  · apply lintegral_congr
    intro t
    rw [cmi_eq_kernel_integral]
    have hf : (κ t).fst = κ.fst t := (Kernel.fst_apply κ t).symm
    rw [hf]
    apply lintegral_congr_ae
    filter_upwards [κ.condKernel_apply_eq_condKernel t] with z hz
    unfold mutualInformation
    rw [hz]
  · simpa only [mutualInformation, Kernel.prod_apply, Kernel.fst_apply, Kernel.snd_apply,
      Measure.fst, Measure.snd] using
      measurable_kernel_klDiv κ.condKernel (κ.condKernel.fst ×ₖ κ.condKernel.snd)
end Tower

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_FiniteEntropyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma sum_probability_atoms {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (q : Measure W) [IsProbabilityMeasure q] :
    ∑ w, q.real {w} = 1 := by
  simp

lemma log_le_tangent {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ Real.log a + x/a - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at h
  linarith

lemma finite_weighted_log_le {W : Type*} [Fintype W] (p x : W → ℝ)
    (hp : ∀ w, 0 ≤ p w) (hpsum : ∑ w, p w = 1) (hx : ∀ w, 0 < x w) :
    ∑ w, p w * Real.log (x w) ≤ Real.log (∑ w, p w*x w) := by
  have ha : 0 < ∑ w, p w*x w := by
    have he : ∃ w, 0 < p w := by
      by_contra! hh
      have hz : ∑ w, p w = 0 := Finset.sum_eq_zero (fun w _ => le_antisymm (hh w) (hp w))
      linarith
    obtain ⟨w,hw⟩ := he
    exact Finset.sum_pos' (fun w _ => mul_nonneg (hp w) (hx w).le)
      ⟨w,Finset.mem_univ w,mul_pos hw (hx w)⟩
  have h := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
    mul_le_mul_of_nonneg_left (log_le_tangent (hx w) ha) (hp w))
  simp only [mul_sub,mul_add,← mul_div_assoc,mul_one] at h
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_div,
    hpsum,one_mul,div_self ha.ne',add_sub_cancel_right] at h
  exact h

lemma finiteEntropy_log_average {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (q : Measure W) [IsProbabilityMeasure q]
    {a : ℝ} (ha : 0 < a) :
    ∑ w, q.real {w} * Real.log (a - Real.log (q.real {w})) ≤
      Real.log (a + finiteEntropy q) := by
  have hx (w : W) : 0 < a - Real.log (q.real {w}) := by
    have hlog := Real.log_nonpos (measureReal_nonneg (μ := q) (s := {w}))
      (measureReal_le_one (μ := q) (s := {w}))
    linarith
  have h := finite_weighted_log_le (fun w => q.real {w})
    (fun w => a - Real.log (q.real {w})) (fun _ => measureReal_nonneg)
    (sum_probability_atoms q) hx
  have he : ∑ w, q.real {w}*(a-Real.log (q.real {w})) = a+finiteEntropy q := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,sum_probability_atoms q,one_mul]
    simp only [finiteEntropy,neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg]
  rwa [he] at h

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_FiniteConditionalEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma neg_mul_log_product {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    -(p*q)*Real.log (p*q) = q*(-p*Real.log p)+p*(-q*Real.log q) := by
  rcases hp.eq_or_lt with hp0 | hp0
  · simp [← hp0]
  rcases hq.eq_or_lt with hq0 | hq0
  · simp [← hq0]
  rw [Real.log_mul (ne_of_gt hp0) (ne_of_gt hq0)]
  ring

section
variable {V W : Type*} [Fintype V] [Fintype W] [MeasurableSpace V] [MeasurableSpace W]
    [MeasurableSingletonClass V] [MeasurableSingletonClass W]
    (μ : Measure V) [IsProbabilityMeasure μ] (κ : Kernel V W) [IsMarkovKernel κ]

omit [Fintype W] [IsProbabilityMeasure μ] in
lemma compProd_real_singleton (v : V) (w : W) :
    (μ ⊗ₘ κ).real {(v,w)} = μ.real {v} * (κ v).real {w} := by
  rw [measureReal_def,← singleton_prod_singleton,
    Measure.compProd_apply_prod (measurableSet_singleton v) (measurableSet_singleton w),
    lintegral_singleton,ENNReal.toReal_mul]
  exact mul_comm _ _

omit [IsProbabilityMeasure μ] in
lemma finiteEntropy_compProd :
    finiteEntropy (μ ⊗ₘ κ) = finiteEntropy μ + ∑ v, μ.real {v} * finiteEntropy (κ v) := by
  unfold finiteEntropy
  rw [Fintype.sum_prod_type]
  simp_rw [compProd_real_singleton,neg_mul_log_product measureReal_nonneg measureReal_nonneg]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,
    sum_probability_atoms (κ v),one_mul]

omit [IsProbabilityMeasure μ] in
lemma finiteEntropy_compProd_conditional :
    finiteEntropy (μ ⊗ₘ κ) - finiteEntropy μ = ∑ v, μ.real {v} * finiteEntropy (κ v) := by
  rw [finiteEntropy_compProd]
  ring

end
end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_FiniteStateDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma atom_smul_kernel_le_snd {V X : Type*} [MeasurableSpace V] [MeasurableSpace X]
    [MeasurableSingletonClass V] (μ : Measure V) [IsProbabilityMeasure μ]
    (κ : Kernel V X) [IsMarkovKernel κ] (v : V) :
    μ {v} • κ v ≤ (μ ⊗ₘ κ).snd := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul,Measure.snd_compProd,
    Measure.bind_apply hs κ.measurable.aemeasurable]
  calc
    _ = ∫⁻ w in {v}, κ w s ∂μ := by rw [lintegral_singleton,mul_comm]
    _ ≤ ∫⁻ w, κ w s ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl

lemma finite_state_bounded_density {V X : Type*} [MeasurableSpace V] [MeasurableSpace X]
    [MeasurableSingletonClass V] (μ : Measure V) [IsProbabilityMeasure μ]
    (κ : Kernel V X) [IsMarkovKernel κ] (ν : Measure X) [IsProbabilityMeasure ν]
    (hν : (μ ⊗ₘ κ).snd = ν) (v : V) (hv : μ {v} ≠ 0) :
    ∃ f : X → ℝ≥0∞, Measurable f ∧ (∀ x, f x ≤ ENNReal.ofReal ((μ.real {v})⁻¹)) ∧
      ν.withDensity f = κ v := by
  let τ := μ {v} • κ v
  have hle : τ ≤ ν := hν ▸ atom_smul_kernel_le_snd μ κ v
  have : IsFiniteMeasure τ := isFiniteMeasure_of_le ν hle
  let g : X → ℝ≥0∞ := fun x => min (τ.rnDeriv ν x) 1
  have hg : Measurable g := (Measure.measurable_rnDeriv τ ν).min measurable_const
  have he : ν.withDensity g = τ := by
    rw [withDensity_congr_ae (show g =ᵐ[ν] τ.rnDeriv ν by
      filter_upwards [Measure.rnDeriv_le_one_of_le hle] with x hx
      exact min_eq_left hx)]
    exact Measure.withDensity_rnDeriv_eq τ ν (Measure.absolutelyContinuous_of_le hle)
  refine ⟨fun x => (μ {v})⁻¹*g x,measurable_const.mul hg,?_,?_⟩
  · intro x
    have ha : 0 < μ.real {v} := ENNReal.toReal_pos hv (measure_ne_top μ {v})
    rw [ENNReal.ofReal_inv_of_pos ha,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ {v})]
    calc
      _ ≤ (μ {v})⁻¹*1 := mul_le_mul le_rfl (min_le_right _ _) (by positivity) (by positivity)
      _ = _ := mul_one _
  · change ν.withDensity ((μ {v})⁻¹ • g) = κ v
    rw [withDensity_smul _ hg,he]
    change (μ {v})⁻¹ • (μ {v} • κ v) = _
    rw [smul_smul,ENNReal.inv_mul_cancel hv (measure_ne_top μ {v}),one_smul]

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
-- module Solutions.OAIQW_PosteriorReplicas.Information_ParametricKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section
variable {T U V : Type*} [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

lemma parametricMapKernel_markov (q : Measure U) [IsProbabilityMeasure q]
    (h : T × U → V) (hh : Measurable h) : IsMarkovKernel (parametricMapKernel q h) :=
  Kernel.IsMarkovKernel.map _ hh

lemma parametricMapKernel_apply (q : Measure U) [SFinite q]
    {h : T × U → V} (hh : Measurable h) (t : T) :
    parametricMapKernel q h t = q.map (fun u => h (t,u)) := by
  rw [parametricMapKernel, Kernel.map_apply _ hh, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map hh (by fun_prop)]
  rfl

lemma compProd_parametricMapKernel (μ : Measure T) [SFinite μ] (q : Measure U) [SFinite q]
    {h : T × U → V} (hh : Measurable h) :
    μ ⊗ₘ parametricMapKernel q h = (μ.prod q).map (fun z => (z.1,h z)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf, lintegral_map hf (by fun_prop),
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro t
  rw [parametricMapKernel_apply q hh, lintegral_map (by fun_prop) (by fun_prop)]
end

section RandomSide
variable {T X Y Z : Type*} [MeasurableSpace T] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace X] [StandardBorelSpace Y] [StandardBorelSpace Z]
  [Nonempty X] [Nonempty Y]

lemma cmi_randomSideLaw (μ : Measure T) [IsFiniteMeasure μ]
    {g : T × X → Z} (hg : Measurable g) (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    cmi (randomSideLaw μ g q) = ∫⁻ t, cmi (attachSide (fun x => g (t,x)) q) ∂μ := by
  let h : T × (X × Y) → Z × (X × Y) := fun z => (g (z.1,z.2.1),z.2)
  have hh : Measurable h := by fun_prop
  let κ := parametricMapKernel q h
  have : IsMarkovKernel κ := parametricMapKernel_markov q h hh
  have he : (μ ⊗ₘ κ).map (MeasurableEquiv.prodAssoc.symm :
      T × (Z × (X × Y)) ≃ᵐ (T × Z) × (X × Y)) = randomSideLaw μ g q := by
    rw [compProd_parametricMapKernel μ q hh, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have ht (t : T) : κ t = attachSide (fun x => g (t,x)) q := by
    rw [parametricMapKernel_apply q hh]
    rfl
  have hc := cmi_compProd_assoc μ κ
  simpa only [he, ht] using hc

lemma measurable_cmi_attachSide {g : T × X → Z} (hg : Measurable g)
    (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    Measurable (fun t => cmi (attachSide (fun x => g (t,x)) q)) := by
  let h : T × (X × Y) → Z × (X × Y) := fun z => (g (z.1,z.2.1),z.2)
  have hh : Measurable h := by fun_prop
  let κ := parametricMapKernel q h
  have : IsMarkovKernel κ := parametricMapKernel_markov q h hh
  have ht (t : T) : κ t = attachSide (fun x => g (t,x)) q := by
    rw [parametricMapKernel_apply q hh]
    rfl
  simpa only [ht] using cmi_kernel_measurable κ
end RandomSide

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_RandomProjectionInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma messageEntropy_eq_finiteEntropy {d N : ℕ} (q : Measure (Vec d × Fin N)) :
    messageEntropy q = finiteEntropy q.snd := rfl

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ReplicaInformationBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma finiteEntropy_nonneg {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (q : Measure W) [IsProbabilityMeasure q] : 0 ≤ finiteEntropy q := by
  simpa only [finiteEntropy, neg_mul, mul_neg] using finite_crossEntropy_nonneg q q

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

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_HaarInformationEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace PosteriorReplicas

lemma cmi_attachSide_equiv {X Y Z Z' : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace Z']
    [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
    [Fintype Y] [MeasurableSingletonClass Y]
    {g : X → Z} (hg : Measurable g) (e : Z ≃ᵐ Z')
    (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    cmi (attachSide (e ∘ g) q) = cmi (attachSide g q) := by
  have hh := mutualInformation_attachSide_chain hg q
  have hh' := mutualInformation_attachSide_chain (e.measurable.comp hg) q
  have hp : ((q.fst.map g).prod q.snd).map (Prod.map e id) =
      (q.fst.map (e ∘ g)).prod q.snd := by
    rw [← Measure.map_prod_map _ _ e.measurable measurable_id,Measure.map_id,
      Measure.map_map e.measurable hg]
  have hq : (q.map (fun z => (g z.1,z.2))).map (Prod.map e id) =
      q.map (fun z => ((e ∘ g) z.1,z.2)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have he := klDiv_map_leftInverse (q.map (fun z => (g z.1,z.2)))
    ((q.fst.map g).prod q.snd)
    (show Measurable (Prod.map e id : Z×Y → Z'×Y) by fun_prop)
    (show Measurable (Prod.map e.symm id : Z'×Y → Z×Y) by fun_prop)
    (by intro z; exact Prod.ext (e.symm_apply_apply z.1) rfl)
  rw [hp,hq] at he
  rw [he] at hh'
  have hfin : klDiv q (q.fst.prod q.snd) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (mutualInformation_le_finiteEntropy q)
  have hB : klDiv (q.map (fun z => (g z.1,z.2))) ((q.fst.map g).prod q.snd) ≠ ∞ := by
    apply ne_top_of_le_ne_top hfin
    rw [hh]
    exact le_add_left le_rfl
  exact (ENNReal.add_left_inj hB).mp (hh'.symm.trans hh)

lemma cmi_labels_gramSchmidtNormed {d ℓ N : ℕ} [NeZero N]
    {A : Rows d ℓ} (hA : LinearIndependent ℝ A)
    (q : Measure (Vec d × Fin N)) [IsProbabilityMeasure q] :
    cmi (attachSide (labels (gramSchmidtNormed ℝ A)) q) =
      cmi (attachSide (labels A) q) := by
  let e := (matrixLinearEquiv (pairingTriangular A).transpose
    (pairingTriangular_det_pos hA).ne').toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : labels A = e ∘ labels (gramSchmidtNormed ℝ A) := pairings_eq_triangular hA
  rw [he]
  exact (cmi_attachSide_equiv (by unfold labels; fun_prop) e q).symm

lemma cmi_haar_eq_gaussian {d ℓ N : ℕ} [NeZero N] (hℓ : ℓ ≤ d)
    (q : Measure (Vec d × Fin N)) [IsProbabilityMeasure q] :
    cmi (randomSideLaw (haarRows d ℓ) (fun z => labels z.1 z.2) q) =
      conditionalInformation (sideLaw ℓ q) := by
  change cmi (randomSideLaw (haarRows d ℓ) (fun z => labels z.1 z.2) q) =
    cmi (randomSideLaw (gaussianRows d ℓ) (fun z => labels z.1 z.2) q)
  rw [cmi_randomSideLaw _ measurable_labels,cmi_randomSideLaw _ measurable_labels]
  rw [haarRows,lintegral_map (measurable_cmi_attachSide measurable_labels q)
    measurable_gramSchmidtNormed_rows]
  apply lintegral_congr_ae
  have hfull := ae_gaussian_columns_independent (E := Vec d) ℓ (by simpa using hℓ)
  filter_upwards [hfull] with A hA
  exact cmi_labels_gramSchmidtNormed hA q

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_StateExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma initialStateKernel_marginal {d V : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q] :
    (q.snd ⊗ₘ initialStateKernel q).snd = q.fst := by
  have h : q.snd ⊗ₘ initialStateKernel q = q.map Prod.swap := by
    rw [initialStateKernel,← Measure.fst_map_swap (ρ := q),Measure.disintegrate]
  rw [h,Measure.snd_map_swap]

lemma lintegral_initialStateKernel {d V : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    {g : Vec d × Fin V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂q = ∫⁻ v, ∫⁻ s, g (s,v) ∂initialStateKernel q v ∂q.snd := by
  have h : q.snd ⊗ₘ initialStateKernel q = q.map Prod.swap := by
    rw [initialStateKernel,← Measure.fst_map_swap (ρ := q),Measure.disintegrate]
  calc
    _ = ∫⁻ z, g z.swap ∂q.map Prod.swap := by
      rw [lintegral_map (by fun_prop) measurable_swap]
      rfl
    _ = _ := by rw [← h,Measure.lintegral_compProd (by fun_prop)]; rfl

lemma stateOutputKernel_apply {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) (v : Fin V) :
    stateOutputKernel q κ v = signalMessageLaw (initialStateKernel q v) (stateBlockKernel κ v) := rfl

lemma signalMessageLaw_lintegral {d k W : ℕ} (p : Measure (Vec d)) [IsProbabilityMeasure p]
    (κ : Kernel (Data d k) (Fin W)) [IsMarkovKernel κ]
    {g : Vec d × Fin W → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂signalMessageLaw p κ =
      ∫⁻ s, ∫⁻ A, ∫⁻ w, g (s,w) ∂κ (A,labels A s) ∂gaussianRows d k ∂p := by
  have hm : Measurable (fun a : Vec d × Rows d k =>
      ∫⁻ w, g (a.1,w) ∂messageKernel κ a) :=
    (hg.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right'
  rw [signalMessageLaw,lintegral_map hg (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  exact lintegral_prod _ hm.aemeasurable

lemma stateMessageLaw_lintegral {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ]
    {g : (Vec d × Fin V) × Fin W → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z ∂stateMessageLaw q κ =
      ∫⁻ z, ∫⁻ A, ∫⁻ w, g (z,w) ∂κ (z.2,(A,labels A z.1)) ∂gaussianRows d k ∂q := by
  have hm : Measurable (fun a : (Vec d × Fin V) × Rows d k =>
      ∫⁻ w, g (a.1,w) ∂stateMessageKernel κ a) :=
    (hg.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right'
  rw [stateMessageLaw,lintegral_map hg (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  exact lintegral_prod _ hm.aemeasurable

lemma stateMessageLaw_eq_compProd {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    stateMessageLaw q κ = (q.snd ⊗ₘ stateOutputKernel q κ).map (fun z => ((z.2.1,z.1),z.2.2)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [stateMessageLaw_lintegral q κ hg,lintegral_map hg (by fun_prop),
    Measure.lintegral_compProd (by fun_prop),lintegral_initialStateKernel q (show Measurable (fun z : Vec d × Fin V =>
      ∫⁻ A, ∫⁻ w, g (z,w) ∂κ (z.2,(A,labels A z.1)) ∂gaussianRows d k) from
      ((hg.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right' (κ := stateMessageKernel κ)).lintegral_prod_right)]
  apply lintegral_congr
  intro v
  rw [stateOutputKernel_apply,signalMessageLaw_lintegral _ _ (by fun_prop)]
  rfl

lemma stateMessageLaw_state_terminal {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    (stateMessageLaw q κ).map (fun z => (z.1.2,z.2)) = q.snd ⊗ₘ (stateOutputKernel q κ).snd := by
  rw [stateMessageLaw_eq_compProd,Measure.map_map (by fun_prop) (by fun_prop),
    Kernel.snd_eq,Measure.compProd_map measurable_snd]
  rfl

lemma stateMessageLaw_initial {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    (stateMessageLaw q κ).map (fun z => z.1.2) = q.snd := by
  rw [stateMessageLaw_eq_compProd,Measure.map_map (by fun_prop) (by fun_prop)]
  change (q.snd ⊗ₘ stateOutputKernel q κ).fst = q.snd
  exact Measure.fst_compProd _ _

lemma terminalConditionalEntropy_average {d k V W : ℕ} (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    terminalConditionalEntropy (stateMessageLaw q κ) =
      ∑ v, q.snd.real {v} * finiteEntropy (stateOutputKernel q κ v).snd := by
  rw [terminalConditionalEntropy,stateMessageLaw_state_terminal,stateMessageLaw_initial,
    finiteEntropy_compProd_conditional]
  simp only [Kernel.snd_apply,Measure.snd]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_StateSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma stateSideKernel_apply {d k V W : ℕ} (ℓ : ℕ)
    (q : Measure (Vec d × Fin V)) [IsFiniteMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) (v : Fin V) :
    stateSideKernel ℓ q κ v = randomSideLaw (haarRows d ℓ)
      (fun z => labels z.1 z.2) (stateOutputKernel q κ v) := rfl

lemma stateHaarSideLaw_eq_compProd {d ℓ k V W : ℕ}
    (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    stateHaarSideLaw ℓ (stateMessageLaw q κ) =
      (q.snd ⊗ₘ stateSideKernel ℓ q κ).map
        (MeasurableEquiv.prodAssoc.symm :
          Fin V × (Data d ℓ × (Vec d × Fin W)) ≃ᵐ
            (Fin V × Data d ℓ) × (Vec d × Fin W)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  let F : Rows d ℓ × Fin V → ℝ≥0∞ := fun z =>
    ∫⁻ sw, g ((z.2,(z.1,labels z.1 sw.1)),sw) ∂stateOutputKernel q κ z.2
  have hF : Measurable F := by
    exact (show Measurable (fun z : (Rows d ℓ × Fin V) × (Vec d × Fin W) =>
      g ((z.1.2,(z.1.1,labels z.1.1 z.2.1)),z.2)) by unfold labels; fun_prop).lintegral_kernel_prod_right'
      (κ := (stateOutputKernel q κ).comap Prod.snd measurable_snd)
  rw [stateHaarSideLaw,lintegral_map hg (by unfold labels; fun_prop),
    lintegral_prod _ (by unfold labels; fun_prop),
    lintegral_map hg (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  calc
    _ = ∫⁻ B, ∫⁻ v, F (B,v) ∂q.snd ∂haarRows d ℓ := by
      apply lintegral_congr
      intro B
      rw [stateMessageLaw_eq_compProd,lintegral_map (by unfold labels; fun_prop) (by fun_prop),
        Measure.lintegral_compProd (by unfold labels; fun_prop)]
    _ = ∫⁻ v, ∫⁻ B, F (B,v) ∂haarRows d ℓ ∂q.snd :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro v
      rw [stateSideKernel_apply,randomSideLaw,lintegral_map (by fun_prop) (by unfold labels; fun_prop),
        lintegral_prod _ (by unfold labels; fun_prop)]
      rfl

lemma stateHaarInformation_average {d ℓ k V W : ℕ} [NeZero W]
    (hℓ : ℓ ≤ d) (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    cmi (stateHaarSideLaw ℓ (stateMessageLaw q κ)) =
      ∑ v, q.snd {v} * conditionalInformation (sideLaw ℓ (stateOutputKernel q κ v)) := by
  simp only [stateHaarSideLaw_eq_compProd]
  rw [cmi_compProd_assoc,lintegral_fintype]
  apply Finset.sum_congr rfl
  intro v _
  simp only [stateSideKernel_apply,cmi_haar_eq_gaussian hℓ,mul_comm]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_HaarStateBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma state_gaussian_information_bound {d ℓ k m V W : ℕ} [NeZero W]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k)
    (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (hq : q.fst = sphereLaw d)
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ]
    (v : Fin V) (hv : q.snd {v} ≠ 0) :
    conditionalInformation (sideLaw ℓ (stateOutputKernel q κ v)) ≤
      ENNReal.ofReal (finiteEntropy (stateOutputKernel q κ v).snd / ((m+1:ℕ):ℝ) +
        (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)-Real.log (q.snd.real {v}))) := by
  have : NeZero d := ⟨by omega⟩
  have : IsProbabilityMeasure (sphereLaw d) := by
    change IsProbabilityMeasure (BaseLaw.spherical.measure d)
    infer_instance
  obtain ⟨f,hf,hfL,hfp⟩ := finite_state_bounded_density q.snd (initialStateKernel q)
    (sphereLaw d) ((initialStateKernel_marginal q).trans hq) v hv
  have hpos : 0 < q.snd.real {v} := ENNReal.toReal_pos hv (measure_ne_top _ _)
  have hL : 1 ≤ (q.snd.real {v})⁻¹ := (one_le_inv₀ hpos).mpr measureReal_le_one
  have : IsProbabilityMeasure ((sphereLaw d).withDensity f) := hfp.symm ▸ inferInstance
  have hi := gaussian_replica_information hd hk hm hkm hdk hℓk hf hL hfL (stateBlockKernel κ v)
  simp only [hfp,messageEntropy_eq_finiteEntropy,Real.log_inv,← sub_eq_add_neg] at hi
  exact hi

lemma haar_state_information_bound {d ℓ k m V W : ℕ} [NeZero W]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k) (hℓ : ℓ≤d)
    (q : Measure (Vec d × Fin V)) [IsProbabilityMeasure q]
    (hq : q.fst = sphereLaw d)
    (κ : Kernel (Fin V × Data d k) (Fin W)) [IsMarkovKernel κ] :
    cmi (stateHaarSideLaw ℓ (stateMessageLaw q κ)) ≤
      ENNReal.ofReal (terminalConditionalEntropy (stateMessageLaw q κ) / ((m+1:ℕ):ℝ) +
        (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)+finiteEntropy q.snd)) := by
  let R : Fin V → ℝ := fun v =>
    finiteEntropy (stateOutputKernel q κ v).snd / ((m+1:ℕ):ℝ) +
      (100+Real.pi)*(d:ℝ) + Real.log (1+(d:ℝ)-Real.log (q.snd.real {v}))
  have hR (v : Fin V) : 0 ≤ R v := by
    have hE := finiteEntropy_nonneg (stateOutputKernel q κ v).snd
    have hlog : Real.log (q.snd.real {v}) ≤ 0 := Real.log_nonpos measureReal_nonneg measureReal_le_one
    have hl : 0 ≤ Real.log (1+(d:ℝ)-Real.log (q.snd.real {v})) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) d] : 1≤1+(d:ℝ)-Real.log (q.snd.real {v}))
    dsimp [R]
    positivity
  rw [stateHaarInformation_average hℓ q κ]
  calc
    _ ≤ ∑ v, q.snd {v} * ENNReal.ofReal (R v) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : q.snd {v} = 0
      · simp [hv]
      · exact mul_le_mul le_rfl (state_gaussian_information_bound hd hk hm hkm hdk hℓk q hq κ v hv) (by positivity) (by positivity)
    _ = ENNReal.ofReal (∑ v, q.snd.real {v} * R v) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun v _ => mul_nonneg measureReal_nonneg (hR v))]
      apply Finset.sum_congr rfl
      intro v _
      rw [ENNReal.ofReal_mul measureReal_nonneg,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have havg := finiteEntropy_log_average q.snd (a := 1+(d:ℝ)) (by positivity)
      have heq : ∑ v, q.snd.real {v} * R v =
          terminalConditionalEntropy (stateMessageLaw q κ) / ((m+1:ℕ):ℝ) +
            (100+Real.pi)*(d:ℝ) +
              ∑ v, q.snd.real {v} * Real.log (1+(d:ℝ)-Real.log (q.snd.real {v})) := by
        simp only [R,mul_add,← mul_div_assoc,Finset.sum_add_distrib,← Finset.sum_div,
          ← Finset.sum_mul,sum_probability_atoms q.snd,one_mul,
          terminalConditionalEntropy_average]
      rw [heq]
      linarith

theorem haarReplicaBlock_oai : HaarReplicaBlock := by
  refine ⟨200+Real.pi,by positivity,?_⟩
  intro d hd V W hV hW q hp hq κ hκ
  have hi := haar_state_information_bound (m := d/16) (ℓ := d/4)
    (by omega : 4*(d/16)+d/16+2≤d) (by omega) (by omega)
    (by omega : d/16+d/16≤d/4) (by omega) (by omega) (by omega) q hq κ
  apply hi.trans
  apply ENNReal.ofReal_le_ofReal
  have hE := finiteEntropy_nonneg q.snd
  have hdp : (1:ℝ)≤d := by exact_mod_cast (by omega : 1≤d)
  have hl := Real.log_le_log (by positivity : 0<1+(d:ℝ)+finiteEntropy q.snd)
    (show 1+(d:ℝ)+finiteEntropy q.snd ≤ 1+(200+Real.pi)*(d:ℝ)+finiteEntropy q.snd by
      nlinarith [Real.pi_pos])
  have hrem : 0 ≤ (200+Real.pi)*(finiteEntropy q.snd+Real.log (d:ℝ))/(d:ℝ)^2 :=
    div_nonneg (mul_nonneg (by positivity) (add_nonneg hE (Real.log_nonneg hdp))) (sq_nonneg _)
  nlinarith [Real.pi_pos]

end PosteriorReplicas
end

end OAI
end

theorem solution : type_of% @OAI.PosteriorReplicas.haarReplicaBlock_oai := @OAI.PosteriorReplicas.haarReplicaBlock_oai
