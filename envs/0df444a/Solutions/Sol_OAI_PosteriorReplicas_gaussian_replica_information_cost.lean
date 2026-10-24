-- Prove2me | solution 1 for OAI.PosteriorReplicas.gaussian_replica_information_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:48:25.671141+00:00
-- url     : https://prove2.me/submissions/14cf8e73-e839-44b6-bf6c-af2ae766ec3b

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000
import Theorems.Thm_OAI_PosteriorReplicas_equal_label_tilt_identity
import Theorems.Thm_OAI_PosteriorReplicas_replica_klDiv_ne_top
import Theorems.Thm_OAI_PosteriorReplicas_replica_lifted_loss

section
-- module Solutions.OAIQW_PosteriorReplicas.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

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
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GaussianDomination
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
section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma orthonormal_gaussian_map {n : ℕ} {u : Fin n → E} (hu : Orthonormal ℝ u) :
    (stdGaussian E).map (fun x => fun i => ⟪u i, x⟫) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let f : E → EuclideanSpace ℝ (Fin n) := fun x => WithLp.toLp 2 (fun i => ⟪u i, x⟫)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : (stdGaussian E).map f = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    apply Measure.ext_of_charFun
    ext t
    have hi (x : E) : ⟪f x, t⟫ = ⟪x, ∑ i, t i • u i⟫ := by
      simp [f, PiLp.inner_apply, inner_sum, inner_smul_right, real_inner_comm x]
    have hn : ‖∑ i, t i • u i‖ ^ 2 = ‖t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hu.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [pow_two]
    rw [charFun_apply, integral_map hf.aemeasurable (by fun_prop)]
    simp_rw [hi]
    change charFun (stdGaussian E) (∑ i, t i • u i) = _
    rw [charFun_stdGaussian, charFun_stdGaussian]
    congr 2
    exact_mod_cast congrArg Neg.neg hn
  have h := congrArg (Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))) he
  rw [← map_pi_eq_stdGaussian] at h
  simpa [Measure.map_map (WithLp.measurable_ofLp _ _) hf,
    Measure.map_map (WithLp.measurable_ofLp _ _) (WithLp.measurable_toLp _ _),
    Function.comp_def, f, WithLp.ofLp_toLp, Measure.map_id] using h

end GaussianDomination

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

lemma charFun_gaussian_starProjection (U : Submodule ℝ E) (t : E) :
    charFun ((stdGaussian E).map U.starProjection) t =
      Complex.exp (- ‖U.starProjection t‖ ^ 2 / 2) := by
  rw [charFun_apply, integral_map U.starProjection.continuous.measurable.aemeasurable
    (by fun_prop)]
  simp_rw [U.inner_starProjection_left_eq_right]
  change charFun (stdGaussian E) (U.starProjection t) = _
  exact charFun_stdGaussian _

lemma gaussian_orthogonal_sum (U : Submodule ℝ E) :
    (((stdGaussian E).map U.starProjection).prod
      ((stdGaussian E).map Uᗮ.starProjection)).map (fun z => z.1 + z.2) =
        stdGaussian E := by
  let : IsProbabilityMeasure ((stdGaussian E).map U.starProjection) :=
    (Measure.isProbabilityMeasure_map_iff
      U.starProjection.continuous.measurable.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure ((stdGaussian E).map Uᗮ.starProjection) :=
    (Measure.isProbabilityMeasure_map_iff
      Uᗮ.starProjection.continuous.measurable.aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_add_prod_eq_mul, Pi.mul_apply,
    charFun_gaussian_starProjection, charFun_gaussian_starProjection,
    charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection t U
  have hc : (‖t‖ : ℂ)^2 = (‖U.starProjection t‖ : ℂ)^2 +
      (‖Uᗮ.starProjection t‖ : ℂ)^2 := by exact_mod_cast h
  rw [hc]
  ring

lemma gaussian_orthogonal_pair (U : Submodule ℝ E) :
    (stdGaussian E).map (fun x => (U.starProjection x, Uᗮ.starProjection x)) =
      ((stdGaussian E).map U.starProjection).prod
        ((stdGaussian E).map Uᗮ.starProjection) := by
  have hP : Measurable (fun x : E => (U.starProjection x, Uᗮ.starProjection x)) :=
    U.starProjection.continuous.measurable.prodMk Uᗮ.starProjection.continuous.measurable
  conv_lhs => rw [← gaussian_orthogonal_sum U]
  rw [Measure.map_map hP (by fun_prop)]
  rw [Measure.map_prod_map _ _ U.starProjection.continuous.measurable
    Uᗮ.starProjection.continuous.measurable]
  rw [Measure.map_map (hP.comp (by fun_prop))
    (U.starProjection.continuous.measurable.prodMap
      Uᗮ.starProjection.continuous.measurable)]
  congr 1
  funext z
  dsimp [Function.comp_def]
  simp only [map_add]
  have h₁ : U.starProjection (U.starProjection z.1) = U.starProjection z.1 :=
    U.starProjection_eq_self_iff.mpr (by simp)
  have h₂ : Uᗮ.starProjection (Uᗮ.starProjection z.2) = Uᗮ.starProjection z.2 :=
    Uᗮ.starProjection_eq_self_iff.mpr (by simp)
  have h₃ : Uᗮ.starProjection (U.starProjection z.1) = 0 :=
    U.starProjection_orthogonal_apply_eq_zero (by simp)
  have h₄ : U.starProjection (Uᗮ.starProjection z.2) = 0 := by
    rw [← U.orthogonal_orthogonal]
    exact Uᗮ.starProjection_orthogonal_apply_eq_zero (by simp)
  rw [h₁, h₂, h₃, h₄, add_zero, zero_add]
  rfl

lemma gaussian_orthogonal_indep (U : Submodule ℝ E) :
    IndepFun U.starProjection Uᗮ.starProjection (stdGaussian E) := by
  exact (indepFun_iff_map_prod_eq_prod_map_map
    U.starProjection.continuous.measurable.aemeasurable
    Uᗮ.starProjection.continuous.measurable.aemeasurable).mpr (gaussian_orthogonal_pair U)

omit [MeasurableSpace E] [BorelSpace E] in
lemma pairing_starProjection (U : Submodule ℝ E) {v : E} (hv : v ∈ U) (x : E) :
    ⟪v, U.starProjection x⟫ = ⟪v, x⟫ := by
  rw [← U.inner_starProjection_left_eq_right, U.starProjection_eq_self_iff.mpr hv]

omit [MeasurableSpace E] [BorelSpace E] in
lemma orthonormal_starProjection {n : ℕ} {u : Fin n → E} (hu : Orthonormal ℝ u) (x : E) :
    (Submodule.span ℝ (Set.range u)).starProjection x = ∑ i, ⟪u i, x⟫ • u i := by
  let U := Submodule.span ℝ (Set.range u)
  have hmem (i : Fin n) : u i ∈ U := Submodule.subset_span (Set.mem_range_self i)
  apply U.eq_starProjection_of_mem_of_inner_eq_zero
  · exact U.sum_mem (fun i _ => U.smul_mem _ (hmem i))
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rcases hv with ⟨i, rfl⟩
      rw [inner_sub_left, hu.inner_left_fintype]
      simp [real_inner_comm x]
    | zero => simp
    | add v w hv hw ihv ihw => simp [inner_add_right, ihv, ihw]
    | smul a v hv ih => simp [inner_smul_right, ih]

lemma gaussian_pairings_residual_indep {n : ℕ} (v : Fin n → E) :
    IndepFun (fun x : E => fun i => ⟪v i, x⟫)
      (Submodule.span ℝ (Set.range v))ᗮ.starProjection (stdGaussian E) := by
  let U := Submodule.span ℝ (Set.range v)
  have h := (gaussian_orthogonal_indep U).comp
    (show Measurable (fun x : E => fun i => ⟪v i, x⟫) by fun_prop) measurable_id
  have heq : (fun x : E => fun i => ⟪v i, x⟫) ∘ U.starProjection =
      (fun x : E => fun i => ⟪v i, x⟫) := by
    funext x i
    apply pairing_starProjection U (Submodule.subset_span (Set.mem_range_self i))
  simpa only [heq, Function.id_comp] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pairingLift_mem {n : ℕ} (v : Fin n → E) (y : Fin n → ℝ) :
    pairingLift v y ∈ Submodule.span ℝ (Set.range v) := by
  unfold pairingLift
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma pairings_pairingLift {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (y : Fin n → ℝ) : (fun j => ⟪v j, pairingLift v y⟫) = y := by
  have hd : IsUnit (Matrix.gram ℝ v).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hv)
  calc
    _ = (Matrix.gram ℝ v) *ᵥ ((Matrix.gram ℝ v)⁻¹ *ᵥ y) := by
      ext j
      simp [pairingLift, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, mul_comm]
    _ = y := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

omit [MeasurableSpace E] [BorelSpace E] in
lemma starProjection_eq_pairingLift {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) (x : E) :
    (Submodule.span ℝ (Set.range v)).starProjection x =
      pairingLift v (fun i => ⟪v i, x⟫) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (pairingLift_mem _ _)
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨i, rfl⟩
    rw [inner_sub_left, real_inner_comm (v i) x, real_inner_comm (v i) (pairingLift _ _)]
    have h := congrFun (pairings_pairingLift hv (fun i => ⟪v i, x⟫)) i
    rw [h, sub_self]
  | zero => simp
  | add v w hv hw ihv ihw => simp [inner_add_right, ihv, ihw]
  | smul a v hv ih => simp [inner_smul_right, ih]

lemma gaussian_pairings_disintegration {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) :
    (((stdGaussian E).map (fun x => fun i => ⟪v i, x⟫)).prod
      ((stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection)).map
        (fun z => pairingLift v z.1 + z.2) = stdGaussian E := by
  rw [← (gaussian_pairings_residual_indep v).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop), Measure.map_map
      (by fun_prop)
      (by fun_prop)]
  convert (Measure.map_id (μ := stdGaussian E)) using 1
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [← starProjection_eq_pairingLift hv x,
    Submodule.starProjection_add_starProjection_orthogonal]
  rfl

lemma gaussian_pairings_integral {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂stdGaussian E =
      ∫⁻ y, ∫⁻ r, g (pairingLift v y + r)
        ∂((stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection)
        ∂((stdGaussian E).map (fun x => fun i => ⟪v i, x⟫)) := by
  conv_lhs => rw [← gaussian_pairings_disintegration hv]
  rw [lintegral_map hg
    (by fun_prop),
    lintegral_prod _ (by fun_prop)]

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

lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {T : α → β} (hT : Measurable T) {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ T)).map T = (μ.map T).withDensity f := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hT,
    lintegral_withDensity_eq_lintegral_mul _ (hf.comp hT)
      (show Measurable (fun a => g (T a)) from hg.comp hT),
    lintegral_withDensity_eq_lintegral_mul _ hf hg,
    lintegral_map (hf.mul hg) hT]
  rfl

lemma map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg e.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hf (show Measurable (fun a => g (e a)) from hg.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul _ (show Measurable (fun y => f (e.symm y)) from hf.comp e.symm.measurable) hg]
  simp only [Pi.mul_apply]
  rw [lintegral_map (show Measurable (fun y => f (e.symm y) * g y) from (hf.comp e.symm.measurable).mul hg) e.measurable]
  simp

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

lemma gaussian_linear_image_density {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hd : M.det ≠ 0) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (Matrix.toLin' M) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun y =>
        ENNReal.ofReal |M.det⁻¹| * ∏ i, gaussianPDF 0 1 ((M⁻¹ *ᵥ y) i)) := by
  let e := (matrixLinearEquiv M hd).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : (e : (Fin n → ℝ) → (Fin n → ℝ)) = Matrix.toLin' M := rfl
  have hi : (e.symm : (Fin n → ℝ) → (Fin n → ℝ)) = Matrix.toLin' M⁻¹ := rfl
  rw [pi_gaussian_density, ← he, map_withDensity_equiv _ e (by fun_prop), he,
    Real.map_matrix_volume_pi_eq_smul_volume_pi hd, withDensity_smul_measure,
    ← withDensity_smul _ (by fun_prop)]
  rfl

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

lemma gaussian_pairings_density_coordinates {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun y =>
        ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) *
          ∏ i, gaussianPDF 0 1 (((pairingTriangular v).transpose⁻¹ *ᵥ y) i)) := by
  rw [pairings_eq_triangular hv, ← Measure.map_map (by fun_prop) (by fun_prop),
    PosteriorRegression.orthonormal_gaussian_map (gramSchmidtNormed_orthonormal hv),
    gaussian_linear_image_density _ (ne_of_gt (pairingTriangular_det_pos hv)),
    abs_of_pos (inv_pos.mpr (pairingTriangular_det_pos hv)), pairingTriangular_det]

lemma orthonormal_pairings_eq_inverse {n : ℕ} {v : Fin n → E}
    (hv : LinearIndependent ℝ v) (x : E) :
    (fun i => ⟪gramSchmidtNormed ℝ v i, x⟫) =
      (pairingTriangular v).transpose⁻¹ *ᵥ (fun i => ⟪v i, x⟫) := by
  have he := congrFun (pairings_eq_triangular hv) x
  change (fun i => ⟪v i, x⟫) =
    (pairingTriangular v).transpose *ᵥ (fun i => ⟪gramSchmidtNormed ℝ v i, x⟫) at he
  rw [he, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt (pairingTriangular_det_pos hv))),
    Matrix.one_mulVec]

lemma pairingLift_energy {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (y : Fin n → ℝ) :
    ‖pairingLift v y‖^2 = ∑ i, (((pairingTriangular v).transpose⁻¹ *ᵥ y) i)^2 := by
  have hu := gramSchmidtNormed_orthonormal hv
  have hs : Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ v)) =
      Submodule.span ℝ (Set.range v) :=
    (span_gramSchmidtNormed_range v).trans (span_gramSchmidt ℝ v)
  have hexp := orthonormal_starProjection hu (pairingLift v y)
  rw [hs, (Submodule.span ℝ (Set.range v)).starProjection_eq_self_iff.mpr
    (pairingLift_mem v y)] at hexp
  have hc := orthonormal_pairings_eq_inverse hv (pairingLift v y)
  rw [pairings_pairingLift hv y] at hc
  simp_rw [congrFun hc] at hexp
  rw [hexp, ← real_inner_self_eq_norm_sq, hu.inner_sum]
  simp [pow_two]

lemma gaussian_pairings_density {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun y => ENNReal.ofReal
        ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖pairingLift v y‖^2 / 2) /
          Real.sqrt (Matrix.gram ℝ v).det)) := by
  rw [gaussian_pairings_density_coordinates hv]
  congr 1
  funext y
  rw [gaussian_density_product, ← pairingLift_energy hv,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma gaussian_fiber_integral {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂stdGaussian E = ∫⁻ y, ENNReal.ofReal
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖pairingLift v y‖^2 / 2) /
        Real.sqrt (Matrix.gram ℝ v).det) *
      ∫⁻ r, g (pairingLift v y + r)
        ∂((stdGaussian E).map (Submodule.span ℝ (Set.range v))ᗮ.starProjection) := by
  rw [gaussian_pairings_integral hv hg, gaussian_pairings_density hv,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  rfl

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

lemma stdGaussian_singleton_eq_zero [Nontrivial E] (x : E) : (stdGaussian E) {x} = 0 :=
  stdGaussian_absolutelyContinuous_volume (measure_singleton x)

lemma gaussian_polar [Nontrivial E] :
    ((stdGaussian E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map
      (homeomorphUnitSphereProd E) =
      (volume : Measure E).toSphere.prod (gaussianPolarRadius E) := by
  let e := (homeomorphUnitSphereProd E).toMeasurableEquiv
  let c : ({0}ᶜ : Set E) → E := Subtype.val
  have hc : MeasurableEmbedding c := MeasurableEmbedding.subtype_coe (measurableSet_singleton 0).compl
  have he : ((volume : Measure E).comap c).map e =
      (volume : Measure E).toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) :=
    (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)).map_eq
  have hcomap : (stdGaussian E).comap c = ((volume : Measure E).comap c).withDensity
      (fun x => gaussianRadialDensity (Module.finrank ℝ E) ‖(x : E)‖) := by
    apply hc.map_injective
    rw [hc.map_comap]
    have hd : (fun x : ({0}ᶜ : Set E) => gaussianRadialDensity (Module.finrank ℝ E) ‖(x : E)‖) =
        (fun x : E => gaussianRadialDensity (Module.finrank ℝ E) ‖x‖) ∘ c := rfl
    rw [hd, map_withDensity_comp _ hc.measurable (by fun_prop)]
    rw [hc.map_comap, stdGaussian_density, restrict_withDensity hc.measurableSet_range]
  change ((stdGaussian E).comap c).map e = _
  rw [hcomap, map_withDensity_equiv _ e (by fun_prop), he]
  have hn (z : sphere (0 : E) 1 × Ioi (0 : ℝ)) : ‖(e.symm z : E)‖ = z.2.1 := by
    change ‖z.2.1 • (z.1 : E)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos z.2.2, mem_sphere_zero_iff_norm.mp z.1.2, mul_one]
  simp_rw [hn]
  rw [gaussianPolarRadius, ← withDensity_one (μ := (volume : Measure E).toSphere),
    prod_withDensity (by fun_prop) (by fun_prop)]
  simp

lemma gaussian_polar_reconstruction [Nontrivial E] :
    (((volume : Measure E).toSphere).prod (gaussianPolarRadius E)).map
      (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => z.2.1 • (z.1 : E)) = stdGaussian E := by
  rw [← gaussian_polar, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : ((fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => z.2.1 • (z.1 : E)) ∘
      homeomorphUnitSphereProd E) = (Subtype.val : ({0}ᶜ : Set E) → E) := by
    funext x
    change ((homeomorphUnitSphereProd E).symm ((homeomorphUnitSphereProd E) x) : E) = _
    simp
  rw [he, (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl).map_comap]
  simp only [Subtype.range_coe]
  apply Measure.restrict_eq_self_of_ae_mem
  simpa using (measure_eq_zero_iff_ae_notMem.mp (stdGaussian_singleton_eq_zero (0 : E)))

lemma gaussian_polar_mass [Nontrivial E] :
    (volume : Measure E).toSphere univ * gaussianPolarRadius E univ = 1 := by
  have h := congrArg (fun μ : Measure E => μ univ) (gaussian_polar_reconstruction (E := E))
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] at h
  simpa only [preimage_univ, ← univ_prod_univ, Measure.prod_prod, measure_univ] using h

lemma gaussianPolarRadius_mass [Nontrivial E] :
    gaussianPolarRadius E univ = ((volume : Measure E).toSphere univ)⁻¹ := by
  have hs : (volume : Measure E).toSphere univ ≠ 0 :=
    (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume))
  have hf : (volume : Measure E).toSphere univ ≠ ∞ := measure_ne_top _ _
  apply (ENNReal.mul_right_inj hs hf).mp
  rw [gaussian_polar_mass, ENNReal.mul_inv_cancel hs hf]

instance instIsFiniteMeasureElemRealIoiOfNatGaussianPolarRadiusOfNontrivial [Nontrivial E] : IsFiniteMeasure (gaussianPolarRadius E) where
  measure_univ_lt_top := by
    rw [gaussianPolarRadius_mass]
    exact ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr
      (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalDirection_smul_sphere [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℝ} (hr : 0 < r) {x : E} (hx : ‖x‖ = 1) :
    normalDirection (r • x) = x := by
  simp [normalDirection, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx, smul_smul, hr.ne']

lemma gaussian_normalDirection [Nontrivial E] :
    (stdGaussian E).map normalDirection = uniformDirection E := by
  rw [← gaussian_polar_reconstruction (E := E), Measure.map_map (by fun_prop) (by fun_prop)]
  have he : normalDirection ∘
      (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => z.2.1 • (z.1 : E)) =
      Subtype.val ∘ Prod.fst := by
    funext z
    exact normalDirection_smul_sphere z.2.2 (mem_sphere_zero_iff_norm.mp z.1.2)
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map Subtype.val
    (((volume : Measure E).toSphere).prod (gaussianPolarRadius E)).fst = _
  rw [Measure.fst, Measure.map_fst_prod, gaussianPolarRadius_mass]
  rfl

instance instIsProbabilityMeasureUniformDirectionOfNontrivial [Nontrivial E] : IsProbabilityMeasure (uniformDirection E) := by
  rw [← gaussian_normalDirection]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Gaussian_RadialIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma lintegral_pos_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℝ} (hr : 0 < r) {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ENNReal.ofReal (r ^ Module.finrank ℝ E) * ∫⁻ x, f (r • x) := by
  have hm : ENNReal.ofReal (r ^ Module.finrank ℝ E) •
      (volume : Measure E).map (fun x => r • x) = volume := by
    rw [Measure.map_addHaar_smul _ hr.ne', smul_smul,
      abs_of_pos (inv_pos.mpr (pow_pos hr _)), ← ENNReal.ofReal_mul (by positivity),
      mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), ENNReal.ofReal_one, one_smul]
  conv_lhs => rw [← hm]
  rw [lintegral_smul_measure, lintegral_map hf (by fun_prop)]
  rfl

lemma lintegral_Ioi_pos_mul {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in Ioi (0 : ℝ), f x = ENNReal.ofReal r * ∫⁻ x in Ioi (0 : ℝ), f (r * x) := by
  have hp : (fun x : ℝ => r * x) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_preimage, mem_Ioi, mul_pos_iff_of_pos_left hr]
  have hm : ENNReal.ofReal r •
      ((volume : Measure ℝ).restrict (Ioi 0)).map (fun x => r * x) = volume.restrict (Ioi 0) := by
    rw [← hp, ← Measure.restrict_map (by fun_prop) measurableSet_Ioi,
      Real.map_volume_mul_left hr.ne', Measure.restrict_smul, smul_smul,
      abs_of_pos (inv_pos.mpr hr), ← ENNReal.ofReal_mul hr.le,
      mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one, one_smul]
    rw [hp]
  conv_lhs => rw [← hm]
  rw [lintegral_smul_measure, lintegral_map hf (by fun_prop)]
  rfl

lemma radial_lintegral_scale (n : ℕ) {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * f (c * r) =
      ENNReal.ofReal ((c⁻¹) ^ (n + 1)) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * f r := by
  rw [lintegral_Ioi_pos_mul (inv_pos.mpr hc) (by fun_prop)]
  have he (r : ℝ) : ENNReal.ofReal ((c⁻¹ * r)^n) * f (c * (c⁻¹ * r)) =
      ENNReal.ofReal ((c⁻¹)^n) * (ENNReal.ofReal (r^n) * f r) := by
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul,
      mul_assoc]
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [pow_succ']

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma gaussianPolarRadius_mass_integral [MeasurableSpace E] [BorelSpace E] :
    gaussianPolarRadius E univ =
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
      gaussianRadialDensity (Module.finrank ℝ E) r := by
  rw [gaussianPolarRadius, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, Measure.volumeIoiPow]
  rw [lintegral_withDensity_eq_lintegral_mul _
    (show Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1 ^ (Module.finrank ℝ E - 1))) by fun_prop)
    (show Measurable (fun r : Ioi (0 : ℝ) => gaussianRadialDensity (Module.finrank ℝ E) r.1) by fun_prop)]
  exact lintegral_subtype_comap (measurableSet_Ioi (a := (0 : ℝ)))
    (fun r : ℝ => ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
      gaussianRadialDensity (Module.finrank ℝ E) r)

omit [MeasurableSpace E] [BorelSpace E] in
lemma lintegral_gaussianPolarRadius [MeasurableSpace E] [BorelSpace E]
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ r : Ioi (0 : ℝ), g r.1 ∂gaussianPolarRadius E =
      ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
          gaussianRadialDensity (Module.finrank ℝ E) r * g r := by
  rw [gaussianPolarRadius, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  simpa only [Pi.mul_apply, mul_assoc] using
    lintegral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
      (fun r : ℝ => ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
        gaussianRadialDensity (Module.finrank ℝ E) r * g r)

lemma gaussianRadialDensity_mul (n q : ℕ) (r s : ℝ) :
    gaussianRadialDensity q r * gaussianRadialDensity n (r * s) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-((n + q : ℕ) : ℝ) / 2) *
        Real.exp (-(1 + s^2) * r^2 / 2)) := by
  unfold gaussianRadialDensity
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_mul_mul_comm, ← Real.rpow_add (by positivity), ← Real.exp_add]
  congr 1 <;> congr 1 <;> push_cast <;> ring

lemma radial_power_gaussian_product {n q d : ℕ} (hq : 1 ≤ q) (hd : n + q = d)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    ENNReal.ofReal (r ^ (q - 1)) * gaussianRadialDensity q r *
        (ENNReal.ofReal (r ^ n) * gaussianRadialDensity n (r * s)) =
      ENNReal.ofReal (r ^ (d - 1)) *
        ENNReal.ofReal ((2 * Real.pi) ^ (-(d : ℝ) / 2) *
          Real.exp (-(1 + s^2) * r^2 / 2)) := by
  rw [mul_mul_mul_comm, ← ENNReal.ofReal_mul (by positivity), ← pow_add,
    gaussianRadialDensity_mul, hd]
  have hn : q - 1 + n = d - 1 := by omega
  rw [hn]

lemma radial_gaussian_integral [Nontrivial E] {a : ℝ} (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
      ENNReal.ofReal ((2 * Real.pi) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2) *
        Real.exp (-a * r^2 / 2)) =
      ENNReal.ofReal (a ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2)) *
        ((volume : Measure E).toSphere univ)⁻¹ := by
  have he (r : ℝ) : ENNReal.ofReal ((2 * Real.pi) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2) *
      Real.exp (-a * r^2 / 2)) = gaussianRadialDensity (Module.finrank ℝ E) (Real.sqrt a * r) := by
    unfold gaussianRadialDensity
    rw [mul_pow, Real.sq_sqrt ha.le]
    ring_nf
  simp_rw [he]
  rw [radial_lintegral_scale _ (Real.sqrt_pos.mpr ha) (by fun_prop),
    ← gaussianPolarRadius_mass_integral, gaussianPolarRadius_mass]
  congr 2
  rw [Nat.sub_add_cancel Module.finrank_pos, Real.sqrt_eq_rpow,
    ← Real.rpow_neg ha.le, ← Real.rpow_natCast,
    ← Real.rpow_mul ha.le]
  congr 1
  ring

lemma sphere_area [Nontrivial E] : (volume : Measure E).toSphere univ =
    ENNReal.ofReal (2 * Real.pi ^ (((Module.finrank ℝ E : ℕ) : ℝ) / 2) /
      Real.Gamma (((Module.finrank ℝ E : ℕ) : ℝ) / 2)) := by
  have hd : 0 < ((Module.finrank ℝ E : ℕ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hp : Real.sqrt Real.pi ^ Module.finrank ℝ E =
      Real.pi ^ (((Module.finrank ℝ E : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    ring
  rw [Measure.toSphere_apply_univ, InnerProductSpace.volume_ball, ENNReal.ofReal_one,
    one_pow, one_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), hp, Real.Gamma_add_one (by positivity)]
  congr 1
  field_simp

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_BaseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

attribute [fun_prop] measurable_labels

lemma rowGram_eq_gram {d k : ℕ} (A : Rows d k) : rowGram A = Matrix.gram ℝ A := rfl

lemma kernelComponent_eq_starProjection {d k : ℕ} {A : Rows d k}
    (hA : LinearIndependent ℝ A) (x : Vec d) :
    kernelComponent A x = (Submodule.span ℝ (Set.range A))ᗮ.starProjection x := by
  rw [Submodule.starProjection_orthogonal_val, starProjection_eq_pairingLift hA]
  rfl

lemma labels_liftLabel {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A) (y : Labels k) :
    labels A (liftLabel A y) = y := pairings_pairingLift hA y

lemma labels_kernelComponent {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A) (x : Vec d) :
    labels A (kernelComponent A x) = 0 := by
  unfold kernelComponent
  ext i
  change ⟪A i, x - liftLabel A (labels A x)⟫ = 0
  rw [inner_sub_right]
  change labels A x i - labels A (liftLabel A (labels A x)) i = 0
  rw [labels_liftLabel hA, sub_self]

lemma labels_basePoint {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (base : BaseLaw) (y : Labels k) (x : Vec d) : labels A (basePoint base A y x) = y := by
  have h₁ := labels_liftLabel hA y
  have h₂ := labels_kernelComponent hA x
  cases base <;> ext i <;>
    simp only [basePoint, labels, inner_add_right, inner_smul_right,
      show ⟪A i, liftLabel A y⟫ = y i from congrFun h₁ i,
      show ⟪A i, kernelComponent A x⟫ = 0 from congrFun h₂ i, mul_zero, add_zero]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_BallJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

section Determinant
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

lemma det_id_add_smulRight (φ : E →ₗ[ℝ] ℝ) (v : E) :
    (LinearMap.id + φ.smulRight v).det = 1 + φ v := by
  classical
  let b := Module.finBasis ℝ E
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id, LinearMap.toMatrix_smulRight]
  have he : Matrix.vecMulVec (fun i => b.repr v i) (fun i => φ (b i)) =
      Matrix.replicateCol Unit (fun i => b.repr v i) *
        Matrix.replicateRow Unit (fun i => φ (b i)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec]
  change (1 + Matrix.vecMulVec (fun i => b.repr v i) (fun i => φ (b i))).det = _
  rw [he, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  have hφ := congrArg φ (b.sum_repr v)
  simpa only [dotProduct, map_sum, map_smul, smul_eq_mul, mul_comm] using hφ

end Determinant

section Ball
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma one_sub_norm_sq_pos {x : E} (hx : x ∈ ball (0 : E) 1) : 0 < 1 - ‖x‖^2 := by
  have h := mem_ball_zero_iff.mp hx
  nlinarith [norm_nonneg x]

omit [FiniteDimensional ℝ E] in
lemma ballStretch_eq : EqOn (ballStretch : E → E)
    OpenPartialHomeomorph.univUnitBall.symm (ball 0 1) := by
  intro x hx
  rw [ballStretch, OpenPartialHomeomorph.univUnitBall_symm_apply,
    neg_div, Real.rpow_neg (one_sub_norm_sq_pos hx).le, Real.sqrt_eq_rpow]

omit [FiniteDimensional ℝ E] in
lemma hasFDerivAt_ballStretch {x : E} (hx : x ∈ ball (0 : E) 1) :
    HasFDerivAt ballStretch (ballStretchDeriv x) x := by
  have hb := one_sub_norm_sq_pos hx
  have h := (((hasFDerivAt_id x).norm_sq.const_sub 1).rpow_const
    (p := -(1 : ℝ) / 2) (Or.inl hb.ne')).smul (hasFDerivAt_id x)
  apply h.congr_fderiv
  ext y
  simp only [ballStretchDeriv, _root_.smul_apply, _root_.add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    _root_.neg_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, id_eq]
  rw [Real.rpow_sub hb, Real.rpow_one]
  module

lemma det_ballStretchDeriv {x : E} (hx : x ∈ ball (0 : E) 1) :
    (ballStretchDeriv x).det =
      (1 - ‖x‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2 - 1) := by
  have hb := one_sub_norm_sq_pos hx
  change ((ballStretchDeriv x).toLinearMap).det = _
  have he : (ballStretchDeriv x).toLinearMap =
      (1 - ‖x‖^2) ^ (-(1 : ℝ) / 2) • (LinearMap.id +
        (((1 - ‖x‖^2)⁻¹ • innerSL ℝ x).toLinearMap).smulRight x) := by
    ext y
    simp [ballStretchDeriv, smul_smul, mul_assoc]
  rw [he, LinearMap.det_smul, det_id_add_smulRight]
  have hi : 1 + (((1 - ‖x‖^2)⁻¹ • innerSL ℝ x).toLinearMap) x = (1 - ‖x‖^2)⁻¹ := by
    simp only [ContinuousLinearMap.coe_coe, _root_.smul_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul]
    field_simp
    ring
  rw [hi, ← Real.rpow_natCast, ← Real.rpow_mul hb.le,
    ← Real.rpow_neg_one, ← Real.rpow_add hb]
  congr 1
  ring

omit [FiniteDimensional ℝ E] in
lemma ballStretch_eq_inv_sqrt {x : E} (hx : x ∈ ball (0 : E) 1) :
    ballStretch x = (Real.sqrt (1 - ‖x‖^2))⁻¹ • x := by
  rw [ballStretch, neg_div, Real.rpow_neg (one_sub_norm_sq_pos hx).le, Real.sqrt_eq_rpow]

omit [FiniteDimensional ℝ E] in
lemma one_add_norm_ballStretch_sq {x : E} (hx : x ∈ ball (0 : E) 1) :
    1 + ‖ballStretch x‖^2 = (1 - ‖x‖^2)⁻¹ := by
  have hb := one_sub_norm_sq_pos hx
  rw [ballStretch_eq_inv_sqrt hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hb)), mul_pow, inv_pow, Real.sq_sqrt hb.le]
  field_simp
  ring

omit [FiniteDimensional ℝ E] in
lemma ballStretch_weight {x : E} (hx : x ∈ ball (0 : E) 1) (q : ℕ) :
    ENNReal.ofReal ((1 - ‖x‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2 - 1)) *
        ENNReal.ofReal ((1 + ‖ballStretch x‖^2) ^
          (-((Module.finrank ℝ E + q : ℕ) : ℝ) / 2)) =
      ENNReal.ofReal ((1 - ‖x‖^2) ^ (((q : ℝ) - 2) / 2)) := by
  have hb := one_sub_norm_sq_pos hx
  rw [← ENNReal.ofReal_mul (by positivity), one_add_norm_ballStretch_sq hx,
    Real.inv_rpow hb.le, ← Real.rpow_neg hb.le, ← Real.rpow_add hb]
  congr 2
  push_cast
  ring

lemma lintegral_ballStretch [MeasurableSpace E] [BorelSpace E] (g : E → ℝ≥0∞) :
    ∫⁻ x, g x = ∫⁻ y in ball (0 : E) 1,
      ENNReal.ofReal ((1 - ‖y‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2 - 1)) *
        g (ballStretch y) := by
  have hi : InjOn (ballStretch : E → E) (ball 0 1) := by
    exact OpenPartialHomeomorph.univUnitBall.symm.injOn.congr ballStretch_eq.symm
  have he : (ballStretch : E → E) '' ball 0 1 = univ := by
    rw [ballStretch_eq.image_eq]
    exact OpenPartialHomeomorph.univUnitBall.symm.image_source_eq_target
  conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure E)), ← he]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball
    (fun x hx => (hasFDerivAt_ballStretch hx).hasFDerivWithinAt) hi g]
  apply setLIntegral_congr_fun measurableSet_ball
  intro x hx
  dsimp only
  rw [det_ballStretchDeriv hx, abs_of_pos (Real.rpow_pos_of_pos (one_sub_norm_sq_pos hx) _)]

end Ball
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

lemma gaussian_subspace_map (U : Submodule ℝ E) :
    (stdGaussian U).map (Subtype.val : U → E) = (stdGaussian E).map U.starProjection := by
  rw [← gaussian_orthogonalProjectionOnto U, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma gaussian_subspace_sum (U : Submodule ℝ E) :
    ((stdGaussian U).prod (stdGaussian Uᗮ)).map (fun z => (z.1 : E) + (z.2 : E)) =
      stdGaussian E := by
  rw [← gaussian_orthogonal_sum U, ← gaussian_subspace_map, ← gaussian_subspace_map,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma subspace_sum_norm_sq [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (U : Submodule ℝ E) (x : U) (z : Uᗮ) :
    ‖(x : E) + (z : E)‖^2 = ‖x‖^2 + ‖z‖^2 := by
  have ho : ⟪(x : E), (z : E)⟫ = 0 :=
    (real_inner_comm _ _).trans ((Submodule.mem_orthogonal' U (z : E)).mp z.2 _ x.2)
  simp [norm_add_sq_real, ho]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma normalDirection_pos_smul [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℝ} (hr : 0 < r) (x : E) :
    normalDirection (r • x) = normalDirection x := by
  simp [normalDirection, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    _root_.mul_inv_rev, smul_smul, hr.ne']

lemma sphere_subspace_gaussian_integral (U : Submodule ℝ E) [Nontrivial E]
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂uniformDirection E =
      ∫⁻ x : U, ∫⁻ z : Uᗮ, g (normalDirection ((x : E) + (z : E)))
        ∂stdGaussian Uᗮ ∂stdGaussian U := by
  rw [← gaussian_normalDirection, lintegral_map hg (by fun_prop),
    ← gaussian_subspace_sum U, lintegral_map (by fun_prop) (by fun_prop),
    lintegral_prod _ (by fun_prop)]

lemma sphere_subspace_polar_integral (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ]
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂uniformDirection E =
      ∫⁻ z : sphere (0 : Uᗮ) 1, ∫⁻ r : Ioi (0 : ℝ), ∫⁻ x : U,
        gaussianRadialDensity (Module.finrank ℝ U) ‖x‖ *
          g (normalDirection ((x : E) + r.1 • ((z : Uᗮ) : E)))
          ∂volume ∂gaussianPolarRadius Uᗮ ∂(volume : Measure Uᗮ).toSphere := by
  rw [sphere_subspace_gaussian_integral U hg]
  have hp (x : U) : (∫⁻ z : Uᗮ, g (normalDirection ((x : E) + (z : E))) ∂stdGaussian Uᗮ) =
      ∫⁻ z : sphere (0 : Uᗮ) 1, ∫⁻ r : Ioi (0 : ℝ),
        g (normalDirection ((x : E) + r.1 • ((z : Uᗮ) : E)))
          ∂gaussianPolarRadius Uᗮ ∂(volume : Measure Uᗮ).toSphere := by
    rw [← gaussian_polar_reconstruction (E := Uᗮ), lintegral_map (by fun_prop) (by fun_prop),
      lintegral_prod _ (by fun_prop)]
    rfl
  simp_rw [hp]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro z
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro r
  rw [stdGaussian_density, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  rfl

lemma radial_subspace_integral (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ] (s : ℝ) :
    ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1 ^ Module.finrank ℝ U) *
        gaussianRadialDensity (Module.finrank ℝ U) (r.1 * s) ∂gaussianPolarRadius Uᗮ =
      ENNReal.ofReal ((1 + s^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2)) *
        ((volume : Measure E).toSphere univ)⁻¹ := by
  rw [lintegral_gaussianPolarRadius (E := Uᗮ) (g := fun r : ℝ =>
    ENNReal.ofReal (r ^ Module.finrank ℝ U) *
      gaussianRadialDensity (Module.finrank ℝ U) (r * s)) (by fun_prop)]
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) *
        ENNReal.ofReal ((2 * Real.pi) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2) *
          Real.exp (-(1 + s^2) * r^2 / 2)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact radial_power_gaussian_product Module.finrank_pos U.finrank_add_finrank_orthogonal hr.le s
    _ = _ := radial_gaussian_integral (by positivity)

lemma scaled_subspace_integral (U : Submodule ℝ E) (z : sphere (0 : Uᗮ) 1)
    (r : Ioi (0 : ℝ)) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x : U, gaussianRadialDensity (Module.finrank ℝ U) ‖x‖ *
        g (normalDirection ((x : E) + r.1 • ((z : Uᗮ) : E))) =
      ∫⁻ x : U, ENNReal.ofReal (r.1 ^ Module.finrank ℝ U) *
        gaussianRadialDensity (Module.finrank ℝ U) (r.1 * ‖x‖) *
          g (normalDirection ((x : E) + ((z : Uᗮ) : E))) := by
  rw [lintegral_pos_smul r.2 (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.2]
  have he : ((r.1 • x : U) : E) + r.1 • ((z : Uᗮ) : E) =
      r.1 • ((x : E) + ((z : Uᗮ) : E)) := by simp [smul_add]
  rw [he, normalDirection_pos_smul r.2, mul_assoc]

lemma sphere_subspace_slope_integral (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ]
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂uniformDirection E =
      ((volume : Measure E).toSphere univ)⁻¹ *
        ∫⁻ z : sphere (0 : Uᗮ) 1, ∫⁻ x : U,
          ENNReal.ofReal ((1 + ‖x‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2)) *
            g (normalDirection ((x : E) + ((z : Uᗮ) : E)))
          ∂volume ∂(volume : Measure Uᗮ).toSphere := by
  rw [sphere_subspace_polar_integral U hg, ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro z
  simp_rw [scaled_subspace_integral U z _ hg]
  rw [lintegral_lintegral_swap (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [lintegral_mul_const _ (by fun_prop), radial_subspace_integral]
  ac_rfl

lemma normalDirection_ballStretch (U : Submodule ℝ E) {x : U}
    (hx : x ∈ ball (0 : U) 1) (z : sphere (0 : Uᗮ) 1) :
    normalDirection (((ballStretch x : U) : E) + ((z : Uᗮ) : E)) =
      (x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E) := by
  have hb := one_sub_norm_sq_pos hx
  have hs := Real.sqrt_pos.mpr hb
  have hz : ‖(z : Uᗮ)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hn : ‖(x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E)‖ = 1 := by
    have h := subspace_sum_norm_sq U x (Real.sqrt (1 - ‖x‖^2) • (z : Uᗮ))
    simp only [Submodule.coe_smul_of_tower, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs, hz, mul_one, Real.sq_sqrt hb.le] at h
    nlinarith [norm_nonneg ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E))]
  have he : ((ballStretch x : U) : E) + ((z : Uᗮ) : E) =
      (Real.sqrt (1 - ‖x‖^2))⁻¹ •
        ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E)) := by
    rw [ballStretch_eq_inv_sqrt hx]
    change (Real.sqrt (1 - ‖x‖^2))⁻¹ • (x : E) + ((z : Uᗮ) : E) = _
    rw [smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  rw [he, normalDirection_smul_sphere (inv_pos.mpr hs) hn]

lemma sphere_subspace_surface_integral (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ]
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂uniformDirection E =
      ((volume : Measure E).toSphere univ)⁻¹ *
        ∫⁻ x : U in ball 0 1,
          ENNReal.ofReal ((1 - ‖x‖^2) ^ ((((Module.finrank ℝ Uᗮ : ℕ) : ℝ) - 2) / 2)) *
            ∫⁻ z : sphere (0 : Uᗮ) 1,
              g ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E))
              ∂(volume : Measure Uᗮ).toSphere := by
  rw [sphere_subspace_slope_integral U hg]
  congr 1
  have ht (z : sphere (0 : Uᗮ) 1) :
      (∫⁻ x : U, ENNReal.ofReal ((1 + ‖x‖^2) ^ (-((Module.finrank ℝ E : ℕ) : ℝ) / 2)) *
        g (normalDirection ((x : E) + ((z : Uᗮ) : E)))) =
      ∫⁻ x : U in ball 0 1,
        ENNReal.ofReal ((1 - ‖x‖^2) ^ ((((Module.finrank ℝ Uᗮ : ℕ) : ℝ) - 2) / 2)) *
          g ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((z : Uᗮ) : E)) := by
    rw [lintegral_ballStretch]
    apply setLIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [normalDirection_ballStretch U hx z, ← mul_assoc,
      ← U.finrank_add_finrank_orthogonal, ballStretch_weight hx]
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply setLIntegral_congr_fun measurableSet_ball
  intro x hx
  dsimp only
  rw [lintegral_const_mul _ (by fun_prop)]

lemma surface_lintegral_eq_gaussian [Nontrivial E] {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z : sphere (0 : E) 1, g (z : E) ∂(volume : Measure E).toSphere =
      (volume : Measure E).toSphere univ * ∫⁻ x, g (normalDirection x) ∂stdGaussian E := by
  have he : (∫⁻ x, g (normalDirection x) ∂stdGaussian E) = ∫⁻ x, g x ∂uniformDirection E := by
    rw [← gaussian_normalDirection, lintegral_map hg (by fun_prop)]
  rw [he, uniformDirection, lintegral_map hg (by fun_prop), lintegral_smul_measure]
  change _ = (volume : Measure E).toSphere univ *
    (((volume : Measure E).toSphere univ)⁻¹ *
      ∫⁻ z : sphere (0 : E) 1, g (z : E) ∂(volume : Measure E).toSphere)
  rw [← mul_assoc, ENNReal.mul_inv_cancel
    (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume)) (measure_ne_top _ _), one_mul]

lemma sphere_subspace_gaussian_fiber_integral (U : Submodule ℝ E)
    [Nontrivial E] [Nontrivial Uᗮ] {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂uniformDirection E =
      ((volume : Measure E).toSphere univ)⁻¹ * (volume : Measure Uᗮ).toSphere univ *
        ∫⁻ x : U in ball 0 1,
          ENNReal.ofReal ((1 - ‖x‖^2) ^ ((((Module.finrank ℝ Uᗮ : ℕ) : ℝ) - 2) / 2)) *
            ∫⁻ z : E, g ((x : E) + Real.sqrt (1 - ‖x‖^2) •
              normalDirection (Uᗮ.starProjection z)) ∂stdGaussian E := by
  rw [sphere_subspace_surface_integral U hg, mul_assoc]
  congr 1
  rw [← lintegral_const_mul _ (by fun_prop)]
  apply setLIntegral_congr_fun measurableSet_ball
  intro x hx
  dsimp only
  rw [surface_lintegral_eq_gaussian (E := Uᗮ) (g := fun z =>
    g ((x : E) + Real.sqrt (1 - ‖x‖^2) • (z : E))) (by fun_prop)]
  have he : (∫⁻ z : Uᗮ, g ((x : E) + Real.sqrt (1 - ‖x‖^2) • ((normalDirection z : Uᗮ) : E))
      ∂stdGaussian Uᗮ) = ∫⁻ z : E, g ((x : E) + Real.sqrt (1 - ‖x‖^2) •
        normalDirection (Uᗮ.starProjection z)) ∂stdGaussian E := by
    rw [← gaussian_orthogonalProjectionOnto Uᗮ, lintegral_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he]
  ac_rfl

lemma sphere_area_ratio (U : Submodule ℝ E) [Nontrivial E] [Nontrivial Uᗮ] :
    ((volume : Measure E).toSphere univ)⁻¹ * (volume : Measure Uᗮ).toSphere univ =
      ENNReal.ofReal (Real.Gamma (((Module.finrank ℝ E : ℕ) : ℝ) / 2) /
        (Real.pi ^ (((Module.finrank ℝ U : ℕ) : ℝ) / 2) *
          Real.Gamma (((Module.finrank ℝ Uᗮ : ℕ) : ℝ) / 2))) := by
  have hd : 0 < ((Module.finrank ℝ E : ℕ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hq : 0 < ((Module.finrank ℝ Uᗮ : ℕ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have he : ((Module.finrank ℝ E : ℕ) : ℝ) =
      ((Module.finrank ℝ U : ℕ) : ℝ) + ((Module.finrank ℝ Uᗮ : ℕ) : ℝ) := by
    exact_mod_cast U.finrank_add_finrank_orthogonal.symm
  have hp : Real.pi ^ (((Module.finrank ℝ E : ℕ) : ℝ) / 2) =
      Real.pi ^ (((Module.finrank ℝ U : ℕ) : ℝ) / 2) *
        Real.pi ^ (((Module.finrank ℝ Uᗮ : ℕ) : ℝ) / 2) := by
    rw [he, add_div, Real.rpow_add Real.pi_pos]
  rw [sphere_area, sphere_area, ← ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hp]
  field_simp

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_SphereDensity
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

lemma volume_pairings_on_span {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v) :
    let U := Submodule.span ℝ (Set.range v)
    (volume : Measure U).map (fun x : U => fun i => ⟪v i, (x : E)⟫) =
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) • volume := by
  let U := Submodule.span ℝ (Set.range v)
  let F : U → Fin n → ℝ := fun x i => ⟪v i, (x : E)⟫
  let h : (Fin n → ℝ) → ℝ≥0∞ := fun y => gaussianRadialDensity n ‖pairingLift v y‖
  have hF : Measurable F := by unfold F; fun_prop
  have hh : Measurable h := by unfold h; fun_prop
  have hj : 0 < Real.sqrt (Matrix.gram ℝ v).det :=
    Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  have hU : Module.finrank ℝ U = n := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hv
  have hl (x : U) : pairingLift v (F x) = (x : E) := by
    rw [← starProjection_eq_pairingLift hv]
    exact U.starProjection_eq_self_iff.mpr x.2
  have hg : (stdGaussian U).map F = (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) := by
    rw [← gaussian_orthogonalProjectionOnto U, Measure.map_map hF (by fun_prop)]
    congr 1
    funext x i
    exact pairing_starProjection U (Submodule.subset_span (Set.mem_range_self i)) x
  have hd : (stdGaussian U) = (volume : Measure U).withDensity (h ∘ F) := by
    rw [stdGaussian_density, hU]
    congr 1
    funext x
    simp only [Function.comp_apply, h, hl, Submodule.norm_coe]
  have he : ((volume : Measure U).map F).withDensity h =
      (ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) •
        (volume : Measure (Fin n → ℝ))).withDensity h := by
    rw [← map_withDensity_comp _ hF hh, ← hd, hg, gaussian_pairings_density hv,
      withDensity_smul_measure, ← withDensity_smul _ hh]
    congr 1
    funext y
    change ENNReal.ofReal _ = ENNReal.ofReal _ * gaussianRadialDensity n ‖pairingLift v y‖
    rw [gaussianRadialDensity, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hz (y : Fin n → ℝ) : h y ≠ 0 := by
    dsimp [h, gaussianRadialDensity]
    positivity
  have ht (y : Fin n → ℝ) : h y ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv := congrArg (fun μ : Measure (Fin n → ℝ) => μ.withDensity (fun y => (h y)⁻¹)) he
  rw [withDensity_inv_same hh (Filter.Eventually.of_forall hz) (Filter.Eventually.of_forall ht),
    withDensity_inv_same hh (Filter.Eventually.of_forall hz) (Filter.Eventually.of_forall ht)] at hinv
  exact hinv

lemma lintegral_pairingLift {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    {g : E → ℝ≥0∞} (hg : Measurable g) :
    let U := Submodule.span ℝ (Set.range v)
    ∫⁻ x : U, g (x : E) ∂volume =
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) * ∫⁻ y, g (pairingLift v y) := by
  let U := Submodule.span ℝ (Set.range v)
  have he := congrArg (fun μ : Measure (Fin n → ℝ) => ∫⁻ y, g (pairingLift v y) ∂μ)
    (volume_pairings_on_span hv)
  rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_smul_measure] at he
  change _ = ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) *
    ∫⁻ y, g (pairingLift v y) at he
  convert he using 1
  apply lintegral_congr
  intro x
  rw [← starProjection_eq_pairingLift hv, U.starProjection_eq_self_iff.mpr x.2]

lemma sphere_fiber_integral {n : ℕ} {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hn : n < Module.finrank ℝ E) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂uniformDirection E = ∫⁻ y, sphericalPairingsDensity v y *
      ∫⁻ z, g (pairingLift v y + Real.sqrt (1 - ‖pairingLift v y‖^2) •
        normalDirection ((Submodule.span ℝ (Set.range v))ᗮ.starProjection z)) ∂stdGaussian E := by
  let U := Submodule.span ℝ (Set.range v)
  have hU : Module.finrank ℝ U = n := by
    simpa only [Fintype.card_fin] using finrank_span_eq_card hv
  have hV : Module.finrank ℝ Uᗮ = Module.finrank ℝ E - n := by
    have ha := U.finrank_add_finrank_orthogonal
    omega
  have hVr : ((Module.finrank ℝ Uᗮ : ℕ) : ℝ) = ((Module.finrank ℝ E : ℕ) : ℝ) - n := by
    rw [hV, Nat.cast_sub hn.le]
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  let : Nontrivial Uᗮ := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ Uᗮ)
  let C : ℝ := Real.Gamma (((Module.finrank ℝ E : ℕ) : ℝ) / 2) /
    (Real.pi ^ ((n : ℝ) / 2) * Real.Gamma ((((Module.finrank ℝ E : ℕ) : ℝ) - n) / 2))
  let β : ℝ := (((Module.finrank ℝ E : ℕ) : ℝ) - n - 2) / 2
  let G : E → ℝ≥0∞ := fun x => ENNReal.ofReal ((1 - ‖x‖^2)^β) *
    ∫⁻ z, g (x + Real.sqrt (1 - ‖x‖^2) • normalDirection (Uᗮ.starProjection z)) ∂stdGaussian E
  have hG : Measurable G := by unfold G; fun_prop
  have hJ : 0 < Real.sqrt (Matrix.gram ℝ v).det :=
    Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hv).det_pos
  have hC : 0 < C := by
    dsimp [C]
    have hd : 0 < ((Module.finrank ℝ E : ℕ) : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
    have hq : 0 < ((Module.finrank ℝ E : ℕ) : ℝ) - n := by
      rw [← hVr]
      exact Nat.cast_pos.mpr Module.finrank_pos
    positivity
  rw [sphere_subspace_gaussian_fiber_integral U hg, sphere_area_ratio, hU, hVr]
  change ENNReal.ofReal C * (∫⁻ x : U in ball 0 1, G (x : E)) = _
  have hi : (∫⁻ x : U in ball 0 1, G (x : E)) =
      ENNReal.ofReal ((Real.sqrt (Matrix.gram ℝ v).det)⁻¹) *
        ∫⁻ y, (ball (0 : E) 1).indicator G (pairingLift v y) := by
    have he := lintegral_pairingLift hv (g := (ball (0 : E) 1).indicator G)
      (hG.indicator measurableSet_ball)
    convert he using 1
    rw [← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro x
    rfl
  have hI : Measurable (fun y => (ball (0 : E) 1).indicator G (pairingLift v y)) :=
    (hG.indicator measurableSet_ball).comp (continuous_pairingLift v).measurable
  rw [hi, ← mul_assoc, ← lintegral_const_mul _ hI]
  apply lintegral_congr
  intro y
  by_cases hy : ‖pairingLift v y‖ < 1
  · rw [Set.indicator_of_mem (mem_ball_zero_iff.mpr hy)]
    dsimp [G, sphericalPairingsDensity]
    rw [ite_eq_left hy, ← mul_assoc, ← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    congr 1
    dsimp [C, β]
    ring
  · rw [Set.indicator_of_notMem (mt mem_ball_zero_iff.mp hy)]
    simp [sphericalPairingsDensity, hy]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_BaseDisintegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma baseDensity_lt_top {d k : ℕ} (base : BaseLaw) (A : Rows d k) (y : Labels k) :
    baseDensity base A y < ∞ := by
  cases base <;> dsimp only [baseDensity] <;> split_ifs <;> simp

lemma baseDensity_spherical {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (y : Labels k) : baseDensity .spherical A y = sphericalPairingsDensity A y := by
  simp only [baseDensity, ite_eq_left hA, sphericalPairingsDensity,
    finrank_euclideanSpace, Fintype.card_fin]
  rfl

lemma base_lintegral {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {g : Vec d → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂base.measure d = ∫⁻ y, baseDensity base A y *
      ∫⁻ x, g x ∂baseFiber base A y := by
  simp_rw [baseFiber_eq_map, lintegral_map hg (measurable_basePoint_fixed base A _)]
  cases base
  · change (∫⁻ x, g x ∂uniformDirection (Vec d)) = _
    rw [sphere_fiber_integral hA (by simpa using hk) hg]
    apply lintegral_congr
    intro y
    rw [baseDensity_spherical hA]
    congr 1
    apply lintegral_congr
    intro x
    congr 1
    simp only [basePoint, kernelComponent_eq_starProjection hA, normalDirection,
      smul_smul, div_eq_mul_inv]
    rfl
  · change (∫⁻ x, g x ∂stdGaussian (Vec d)) = _
    rw [gaussian_fiber_integral hA hg]
    apply lintegral_congr
    intro y
    rw [baseDensity, ite_eq_left hA]
    congr 1
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    apply lintegral_congr
    intro x
    rw [basePoint, kernelComponent_eq_starProjection hA]
    rfl

lemma weighted_base_lintegral {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f g : Vec d → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(base.measure d).withDensity f =
      ∫⁻ y, baseDensity base A y * ∫⁻ x, f x * g x ∂baseFiber base A y := by
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]
  exact base_lintegral hA hk base (hf.mul hg)

lemma tiltMass_le {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞}
    (hL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) : tiltMass base f A y ≤ L := by
  unfold tiltMass
  calc
    _ ≤ ∫⁻ _, L ∂baseFiber base A y := lintegral_mono hL
    _ = L := by simp

lemma tiltMass_ne_top {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞}
    (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    tiltMass base f A y ≠ ∞ := ne_top_of_le_ne_top hL (tiltMass_le base hfL A y)

lemma projectedDensity_ne_top {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    projectedDensity base f A y ≠ ∞ :=
  ENNReal.mul_ne_top (baseDensity_lt_top base A y).ne (tiltMass_ne_top base hL hfL A y)

lemma weighted_fiber_labels {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (base : BaseLaw) (y : Labels k) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {g : Labels k → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, f x * g (labels A x) ∂baseFiber base A y = tiltMass base f A y * g y := by
  have hfg : Measurable (fun x => f x * g (labels A x)) := by fun_prop
  rw [baseFiber_eq_map, lintegral_map hfg (measurable_basePoint_fixed base A y)]
  simp_rw [labels_basePoint hA]
  rw [lintegral_mul_const _ (show Measurable (fun x => f (basePoint base A y x)) from
    hf.comp (measurable_basePoint_fixed base A y))]
  congr 1
  rw [tiltMass, baseFiber_eq_map, lintegral_map hf (measurable_basePoint_fixed base A y)]

lemma projected_measure {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    ((base.measure d).withDensity f).map (labels A) =
      volume.withDensity (projectedDensity base f A) := by
  have hl : Measurable (labels A) := by unfold labels; fun_prop
  have hp0 := (measurable_projectedDensity (d := d) (k := k) base hf).comp
    (show Measurable (fun y : Labels k => (A,y)) from measurable_const.prodMk measurable_id)
  simp only [Function.comp_def] at hp0
  have hp : Measurable (projectedDensity base f A) := hp0
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hl]
  rw [weighted_base_lintegral hA hk base hf (g := fun x => g (labels A x)) (hg.comp hl)]
  rw [lintegral_withDensity_eq_lintegral_mul _ hp hg]
  simp only [Pi.mul_apply, weighted_fiber_labels hA base _ hf hg, projectedDensity, mul_assoc]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_FrameTubes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Metric EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma baseProjectionConstant_pos {d k : ℕ} (hk : k < d) (base : BaseLaw) :
    0 < baseProjectionConstant base d k := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hdk : 0 < (d : ℝ) - k := sub_pos.mpr (by exact_mod_cast hk)
  cases base <;> unfold baseProjectionConstant <;> positivity

lemma baseDensity_le_sup {d k : ℕ} (hk : k + 2 ≤ d) (base : BaseLaw)
    (A : Rows d k) (y : Labels k) : baseDensity base A y ≤
      ENNReal.ofReal (baseProjectionConstant base d k / Real.sqrt (rowGram A).det) := by
  have hC := (baseProjectionConstant_pos (by omega : k < d) base).le
  by_cases hA : LinearIndependent ℝ A
  · rw [baseDensity.eq_def, ite_eq_left hA]
    cases base
    · dsimp only [baseProjectionConstant] at hC ⊢
      split_ifs with hy
      · apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        have hb : 0 ≤ 1 - ‖liftLabel A y‖^2 := by nlinarith [norm_nonneg (liftLabel A y)]
        have he : 0 ≤ ((d : ℝ) - k - 2) / 2 := by
          have : (k : ℝ) + 2 ≤ d := by exact_mod_cast hk
          linarith
        exact mul_le_of_le_one_right hC (Real.rpow_le_one hb (by nlinarith [sq_nonneg ‖liftLabel A y‖]) he)
      · exact bot_le
    · dsimp only [baseProjectionConstant] at hC ⊢
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)))
  · rw [baseDensity.eq_def, ite_eq_right hA]
    exact bot_le

lemma baseDensity_le_orthonormal {d k : ℕ} (hk : k + 2 ≤ d) (base : BaseLaw)
    {A : Rows d k} (hA : Orthonormal ℝ A) (y : Labels k) :
    baseDensity base A y ≤ ENNReal.ofReal (baseProjectionConstant base d k) := by
  simpa only [rowGram_eq_gram, Matrix.gram_eq_one_iff_orthonormal.mpr hA,
    Matrix.det_one, Real.sqrt_one, div_one] using baseDensity_le_sup hk base A y

lemma projected_base_measure {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) : (base.measure d).map (labels A) =
      volume.withDensity (baseDensity base A) := by
  have h := projected_measure hA hk base (f := fun _ => 1) measurable_const
  have hμ : (base.measure d).withDensity (fun _ => 1) = base.measure d := by
    exact withDensity_one
  have hp : projectedDensity base (fun _ => 1) A = baseDensity base A := by
    funext y
    simp only [projectedDensity, tiltMass, lintegral_one, measure_univ, mul_one]
  rw [hμ, hp] at h
  exact h

lemma orthonormal_in_orthogonal {d q : ℕ} (U : Submodule ℝ (Vec d))
    (hq : q ≤ Module.finrank ℝ Uᗮ) :
    ∃ v : Fin q → Vec d, Orthonormal ℝ v ∧ ∀ i, v i ∈ Uᗮ := by
  let b := stdOrthonormalBasis ℝ Uᗮ
  let v : Fin q → Uᗮ := fun i => b (Fin.castLE hq i)
  refine ⟨fun i => (v i : Vec d), ?_, fun i => (v i).2⟩
  exact (b.orthonormal.comp (Fin.castLE hq) (Fin.castLE_injective hq)).comp_linearIsometry Uᗮ.subtypeₗᵢ

lemma pairing_le_infDist {d : ℕ} (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    {p v : Vec d} (hp : p ∈ L) (hv : v ∈ L.directionᗮ) (hvnorm : ‖v‖ = 1) (x : Vec d) :
    |⟪v, x - p⟫| ≤ Metric.infDist x L := by
  have ho : ⟪v, (orthogonalProjection L x : Vec d) - p⟫ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (L.vsub_mem_direction (orthogonalProjection_mem x) hp) hv
  have he : ⟪v, x - p⟫ = ⟪v, x - (orthogonalProjection L x : Vec d)⟫ := by
    rw [inner_sub_right] at ho
    simp only [inner_sub_right]
    linarith
  rw [he, ← dist_orthogonalProjection_eq_infDist, dist_eq_norm]
  simpa only [hvnorm, one_mul] using abs_real_inner_le_norm v (x - (orthogonalProjection L x : Vec d))

lemma base_affine_tube {d q : ℕ} (hq : q + 2 ≤ d) (base : BaseLaw)
    (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    (hL : Module.finrank ℝ L.direction + q ≤ d) {r : ℝ} (hr : 0 < r) :
    (base.measure d) {x | Metric.infDist x L ≤ r} ≤
      (ENNReal.ofReal (baseProjectionConstant base d q) * 2^q) * ENNReal.ofReal (r^q) := by
  have hdim : q ≤ Module.finrank ℝ L.directionᗮ := by
    have he := L.direction.finrank_add_finrank_orthogonal
    simp only [finrank_euclideanSpace_fin] at he
    omega
  obtain ⟨v, hv, hvin⟩ := orthonormal_in_orthogonal L.direction hdim
  obtain ⟨p, hp⟩ := Set.nonempty_coe_sort.mp (inferInstance : Nonempty L)
  let c := labels v p
  let s : Set (Labels q) := Set.pi univ (fun i => Icc (c i - r) (c i + r))
  have hs : MeasurableSet s := MeasurableSet.univ_pi (fun i => measurableSet_Icc)
  have hsub : {x | Metric.infDist x L ≤ r} ⊆ (labels v) ⁻¹' s := by
    intro x hx
    simp only [Set.mem_preimage, s, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have hi := (pairing_le_infDist L hp (hvin i) (hv.norm_eq_one i) x).trans hx
    rw [inner_sub_right, abs_le] at hi
    exact ⟨by dsimp [c, labels]; linarith [hi.1], by dsimp [c, labels]; linarith [hi.2]⟩
  calc
    _ ≤ (base.measure d) ((labels v) ⁻¹' s) := measure_mono hsub
    _ = ((base.measure d).map (labels v)) s :=
      (Measure.map_apply (by unfold labels; fun_prop) hs).symm
    _ = ∫⁻ y in s, baseDensity base v y := by
      rw [projected_base_measure hv.linearIndependent (by omega) base, withDensity_apply _ hs]
    _ ≤ ∫⁻ _y in s, ENNReal.ofReal (baseProjectionConstant base d q) :=
      setLIntegral_mono' hs (fun y _ => baseDensity_le_orthonormal hq base hv y)
    _ = ENNReal.ofReal (baseProjectionConstant base d q) * ENNReal.ofReal (2*r)^q := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      congr 1
      change (Measure.pi (fun _ : Fin q => volume)) s = _
      rw [Measure.pi_pi]
      simp only [Real.volume_Icc, show ∀ i, c i + r - (c i - r) = 2*r from fun _ => by ring]
      simp
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num), mul_pow, ENNReal.ofReal_ofNat,
        ENNReal.ofReal_pow hr.le, mul_assoc]

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

lemma base_affine_null {d : ℕ} (hd : 3 ≤ d) (base : BaseLaw)
    (L : AffineSubspace ℝ (Vec d)) [Nonempty L]
    (hL : Module.finrank ℝ L.direction < d) : (base.measure d) L = 0 := by
  let C := ENNReal.ofReal (baseProjectionConstant base d 1) * 2
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hb (n : ℕ) : (base.measure d) L ≤ C * ENNReal.ofReal ((1/2 : ℝ)^n) := by
    calc
      _ ≤ (base.measure d) {x | Metric.infDist x L ≤ (1/2 : ℝ)^n} := by
        apply measure_mono
        intro x hx
        simp only [Set.mem_ofPred_eq, Metric.infDist_zero_of_mem hx]
        positivity
      _ ≤ _ := by simpa [C] using base_affine_tube hd base L (by omega) (r := (1/2 : ℝ)^n) (by positivity)
  have hlim : Tendsto (fun n : ℕ => C * ENNReal.ofReal ((1/2 : ℝ)^n)) atTop (nhds 0) := by
    have h := ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1))
    simpa using ENNReal.Tendsto.const_mul h (Or.inr hC)
  exact le_antisymm (ge_of_tendsto' hlim hb) bot_le

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_PiTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma ae_pi_cons {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    {n : ℕ} {P : (Fin (n+1) → E) → Prop} (hP : MeasurableSet {v | P v}) :
    (∀ᵐ v ∂Measure.pi (fun _ => μ), P v) ↔
      ∀ᵐ p ∂μ, ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => μ), P (Fin.cons p v) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E) 0).symm
  have he (z : E × (Fin n → E)) : e z = Fin.cons z.1 z.2 := by
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  rw [← hm.map_eq, MeasurableEmbedding.ae_map_iff e.measurableEmbedding]
  have hPe : MeasurableSet {z | P (e z)} := hP.preimage e.measurable
  rw [Measure.ae_prod_iff_ae_ae hPe]
  simp_rw [he]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_TupleMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma measurableSet_row_independent {d k : ℕ} :
    MeasurableSet {A : Rows d k | LinearIndependent ℝ A} := by
  have he : {A : Rows d k | LinearIndependent ℝ A} = {A | (rowGram A).det ≠ 0} := by
    ext A
    exact ⟨fun h => (Matrix.posDef_gram_of_linearIndependent h).det_pos.ne',
      fun h => Matrix.linearIndependent_of_det_gram_ne_zero (show (Matrix.gram ℝ A).det ≠ 0 from h)⟩
  rw [he]
  exact (isClosed_eq continuous_rowGram.matrix_det continuous_const).isOpen_compl.measurableSet

lemma measurableSet_affine_independent {d m : ℕ} :
    MeasurableSet {u : Tuple d m | LinearIndependent ℝ (differences u)} :=
  measurableSet_row_independent.preimage continuous_differences.measurable

lemma ae_base_tuple_full_rank {d m : ℕ} (hd : 3 ≤ d) (hm : m < d) (base : BaseLaw) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => base.measure d),
      LinearIndependent ℝ (differences u) := by
  have : NeZero d := ⟨by omega⟩
  rw [ae_pi_cons (base.measure d) measurableSet_affine_independent]
  apply Filter.Eventually.of_forall
  intro p
  simpa only [differences_cons] using
    ae_replica_independent_of_affine_null p m
      (fun L _ hL => base_affine_null hd base L (by omega))

lemma ae_gaussian_rows_full_rank {d k : ℕ} (hd : 3 ≤ d) (hk : k < d) :
    ∀ᵐ A ∂gaussianRows d k, LinearIndependent ℝ A := by
  have h := ae_replica_independent_of_affine_null (ν := stdGaussian (Vec d)) (0 : Vec d) k
    (fun L _ hL => base_affine_null hd .gaussian L (by omega))
  simpa only [sub_zero, gaussianRows] using h

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
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_KernelPi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma piKernel_apply {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} (κ : Fin n → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] (x : X) :
    piKernel κ x = Measure.pi (fun i => κ i x) := by
  induction n with
  | zero =>
    rw [piKernel, Kernel.deterministic_apply, Measure.pi_of_empty _ (fun i => Fin.elim0 i)]
  | succ n ih =>
    have hκ : ∀ i : Fin n, IsMarkovKernel (κ i.succ) := inferInstance
    rw [piKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, ih]
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0).symm
    have he : (fun z : Y × (Fin n → Y) => Fin.cons z.1 z.2) = e := by
      funext z
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
    rw [he]
    exact (measurePreserving_piFinSuccAbove (fun i : Fin (n+1) => κ i x) 0).symm.map_eq

@[fun_prop] lemma measurable_piKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} (κ : Fin n → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] :
    Measurable (fun x => Measure.pi (fun i => κ i x)) := by
  simpa only [← piKernel_apply] using (piKernel κ).measurable

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_PiKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma probability_measure_eq_of_subsingleton {X : Type*} [MeasurableSpace X] [Subsingleton X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s hs
  by_cases h : s.Nonempty
  · have he : s = univ := by
      obtain ⟨x,hx⟩ := h
      apply eq_univ_of_forall
      intro y
      simpa only [Subsingleton.elim y x] using hx
    simp [he]
  · simp [Set.not_nonempty_iff_eq_empty.mp h]

lemma piFinSucc_fst {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin (n+1) → Y)) :
    (q.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0)).fst =
      coordinateMarginal q 0 := by
  rw [Measure.fst, Measure.map_map measurable_fst (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0).measurable]
  rfl

lemma piFinSucc_tail_marginal {Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (q : Measure (Fin (n+1) → Y)) (i : Fin n) :
    coordinateMarginal (q.map (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n+1) => Y) 0)).snd i = coordinateMarginal q i.succ := by
  unfold coordinateMarginal Measure.snd
  rw [Measure.map_map measurable_snd (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0).measurable,
    Measure.map_map (measurable_pi_apply i) (measurable_snd.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0).measurable)]
  rfl

lemma klDiv_pi_decomposition {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {n : ℕ} (q : Measure (Fin n → Y)) [IsProbabilityMeasure q]
    (ρ : Fin n → Measure Y) [∀ i, IsProbabilityMeasure (ρ i)] :
    klDiv q (Measure.pi ρ) = klDiv q (marginalProduct q) + ∑ i, klDiv (coordinateMarginal q i) (ρ i) := by
  induction n with
  | zero =>
    have h1 := probability_measure_eq_of_subsingleton q (Measure.pi ρ)
    have h2 := probability_measure_eq_of_subsingleton q (marginalProduct q)
    simp only [← h1, ← h2, klDiv_self, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Y) 0
    let r := q.map e
    have : IsProbabilityMeasure r := Measure.isProbabilityMeasure_map (by fun_prop)
    have hρ : (Measure.pi ρ).map e = (ρ 0).prod (Measure.pi (fun i : Fin n => ρ i.succ)) :=
      (measurePreserving_piFinSuccAbove ρ 0).map_eq
    have ho : (marginalProduct q).map e = r.fst.prod (marginalProduct r.snd) := by
      rw [marginalProduct, (measurePreserving_piFinSuccAbove (coordinateMarginal q) 0).map_eq]
      congr 1
      · exact (piFinSucc_fst q).symm
      · unfold marginalProduct
        congr 1
        funext i
        exact (piFinSucc_tail_marginal q i).symm
    have hD : klDiv q (Measure.pi ρ) =
        klDiv r.fst (ρ 0) + klDiv r.snd (Measure.pi (fun i : Fin n => ρ i.succ)) +
          klDiv r (r.fst.prod r.snd) := by
      rw [← klDiv_map_equiv _ _ e, hρ]
      exact klDiv_prod_decomposition r (ρ 0) _
    have hC : klDiv q (marginalProduct q) =
        klDiv r.snd (marginalProduct r.snd) + klDiv r (r.fst.prod r.snd) := by
      rw [← klDiv_map_equiv _ _ e, ho, klDiv_prod_decomposition r r.fst _, klDiv_self, zero_add]
    rw [hD, hC, ih r.snd (fun i : Fin n => ρ i.succ), Fin.sum_univ_succ]
    have hf : r.fst = coordinateMarginal q 0 := piFinSucc_fst q
    have ht : ∀ i : Fin n, coordinateMarginal r.snd i = coordinateMarginal q i.succ :=
      piFinSucc_tail_marginal q
    simp_rw [hf, ht]
    ac_rfl

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ConditionalPiKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section ConditionalPi
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace Y] [Nonempty Y] {n : ℕ}
  (μ : Measure X) [IsProbabilityMeasure μ]
  (κ : Kernel X (Fin n → Y)) [IsMarkovKernel κ]

omit [StandardBorelSpace Y] [Nonempty Y] [IsMarkovKernel κ] in
lemma coordKernel_apply (i : Fin n) (x : X) : coordKernel κ i x = coordinateMarginal (κ x) i :=
  Kernel.map_apply _ (measurable_pi_apply i) _

omit [Nonempty Y] in
lemma conditionalTotalCorrelation_integral :
    conditionalTotalCorrelation μ κ = ∫⁻ x, klDiv (κ x) (marginalProduct (κ x)) ∂μ := by
  rw [conditionalTotalCorrelation, klDiv_compProd_kernel]
  apply lintegral_congr
  intro x
  rw [piKernel_apply]
  simp_rw [coordKernel_apply, marginalProduct]

lemma klDiv_conditional_pi_decomposition (ρ : Fin n → Measure Y) [∀ i, IsProbabilityMeasure (ρ i)] :
    klDiv (μ ⊗ₘ κ) (μ.prod (Measure.pi ρ)) = conditionalTotalCorrelation μ κ +
      ∑ i, klDiv (μ ⊗ₘ coordKernel κ i) (μ.prod (ρ i)) := by
  simp_rw [← Measure.compProd_const, klDiv_compProd_kernel]
  rw [conditionalTotalCorrelation_integral]
  calc
    _ = ∫⁻ x, klDiv (κ x) (marginalProduct (κ x)) +
        ∑ i, klDiv (coordinateMarginal (κ x) i) (ρ i) ∂μ := by
      exact lintegral_congr fun x => klDiv_pi_decomposition (κ x) ρ
    _ = _ := by
      have hc : Measurable (fun x => klDiv (κ x) (marginalProduct (κ x))) := by
        simpa only [piKernel_apply, coordKernel_apply, marginalProduct] using
          (measurable_kernel_klDiv κ (piKernel (coordKernel κ)))
      have hi : ∀ i, Measurable (fun x => klDiv (coordinateMarginal (κ x) i) (ρ i)) := by
        intro i
        simpa only [coordKernel_apply, Kernel.const_apply] using
          (measurable_kernel_klDiv (coordKernel κ i) (Kernel.const X (ρ i)))
      rw [lintegral_add_aux hc (Finset.measurable_sum _ (fun i _ => hi i)),
        lintegral_finsetSum _ (fun i _ => hi i)]
      simp_rw [coordKernel_apply, Kernel.const_apply]

lemma conditionalTotalCorrelation_identity [StandardBorelSpace X] [Nonempty X] :
    conditionalTotalCorrelation μ κ +
      ∑ i, klDiv (μ ⊗ₘ coordKernel κ i)
        (μ.prod (coordinateMarginal (μ ⊗ₘ κ).snd i)) =
      klDiv (μ ⊗ₘ κ).snd (marginalProduct (μ ⊗ₘ κ).snd) +
      klDiv (μ ⊗ₘ κ) (μ.prod (μ ⊗ₘ κ).snd) := by
  rw [← klDiv_conditional_pi_decomposition]
  rw [klDiv_prod_decomposition, Measure.fst_compProd, klDiv_self, zero_add]
  rfl

end ConditionalPi

section Projection
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z]
  {n : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
  (κ : Kernel X (Fin n → Y)) [IsMarkovKernel κ]
  {g : Y → Z} (hg : Measurable g)
include hg

omit [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z] in
lemma marginalProduct_map (ν : Measure (Fin n → Y)) [IsProbabilityMeasure ν] :
    marginalProduct (ν.map (fun u i => g (u i))) =
      (marginalProduct ν).map (fun u i => g (u i)) := by
  unfold marginalProduct coordinateMarginal
  have he : (fun i : Fin n => (ν.map (fun u j => g (u j))).map (fun u => u i)) =
      fun i => (ν.map (fun u => u i)).map g := by
    funext i
    rw [Measure.map_map (measurable_pi_apply i) (by fun_prop),
      Measure.map_map hg (measurable_pi_apply i)]
    rfl
  rw [he]
  exact (Measure.pi_map_pi (fun _ : Fin n => hg.aemeasurable)).symm

omit [Nonempty Y] [Nonempty Z] in
lemma conditionalTotalCorrelation_map_le :
    conditionalTotalCorrelation μ (κ.map (fun u i => g (u i))) ≤ conditionalTotalCorrelation μ κ := by
  let : IsMarkovKernel (κ.map (fun u i => g (u i))) := Kernel.IsMarkovKernel.map _ (by fun_prop)
  rw [conditionalTotalCorrelation_integral, conditionalTotalCorrelation_integral]
  apply lintegral_mono
  intro x
  dsimp only
  rw [Kernel.map_apply _ (show Measurable (fun u : Fin n → Y => fun i => g (u i)) by fun_prop), marginalProduct_map hg]
  exact klDiv_map_le _ _ (by fun_prop)

end Projection
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
-- module Solutions.OAIQW_PosteriorReplicas.Information_ReplicaInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma snd_compProd_map {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) [SFinite μ] (κ : Kernel X Y) [IsSFiniteKernel κ]
    {g : Y → Z} (hg : Measurable g) :
    (μ ⊗ₘ κ.map g).snd = (μ ⊗ₘ κ).snd.map g := by
  rw [Measure.compProd_map hg, Measure.snd, Measure.map_map measurable_snd (by fun_prop),
    Measure.snd, Measure.map_map hg measurable_snd]
  rfl

lemma mutualInformation_swap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : Measure (X × Y)) [IsProbabilityMeasure q] :
    mutualInformation (q.map Prod.swap) = mutualInformation q := by
  unfold mutualInformation
  rw [Measure.fst_map_swap, Measure.snd_map_swap, ← Measure.prod_swap, klDiv_swap]

section Coordinates
variable {W Y : Type*} [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] {n : ℕ}
  (μ : Measure W) [IsProbabilityMeasure μ] (κ : Kernel W (Fin n → Y)) [IsMarkovKernel κ]

omit [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace Y] [Nonempty Y] in
lemma coordinateJoint_information (i : Fin n) :
    mutualInformation (coordinateJoint μ κ i) =
      klDiv (μ ⊗ₘ coordKernel κ i) (μ.prod (coordinateMarginal (μ ⊗ₘ κ).snd i)) := by
  rw [coordinateJoint, mutualInformation_swap, mutualInformation, Measure.fst_compProd,
    coordKernel, snd_compProd_map _ _ (measurable_pi_apply i)]
  rfl

lemma tuple_information_decomposition :
    conditionalTotalCorrelation μ κ + ∑ i, mutualInformation (coordinateJoint μ κ i) =
      totalCorrelation (μ ⊗ₘ κ).snd + mutualInformation (μ ⊗ₘ κ) := by
  simp_rw [coordinateJoint_information]
  simpa only [totalCorrelation, mutualInformation, Measure.fst_compProd] using
    conditionalTotalCorrelation_identity μ κ

end Coordinates

section Projection
variable {W Y Z : Type*} [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] {n : ℕ}
  (μ : Measure W) [IsProbabilityMeasure μ] (κ : Kernel W (Fin n → Y)) [IsMarkovKernel κ]
  {g : Y → Z} (hg : Measurable g)
include hg

omit [StandardBorelSpace W] [Nonempty W] [StandardBorelSpace Y] [Nonempty Y]
  [StandardBorelSpace Z] [Nonempty Z] in
lemma coordinateJoint_projection (i : Fin n) :
    coordinateJoint μ (κ.map (fun u j => g (u j))) i =
      (coordinateJoint μ κ i).map (fun z => (g z.1,z.2)) := by
  unfold coordinateJoint coordKernel
  rw [Measure.compProd_map (measurable_pi_apply i),
    Measure.compProd_map (show Measurable (fun u : Fin n → Y => fun j => g (u j)) by fun_prop),
    Measure.compProd_map (measurable_pi_apply i)]
  repeat rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

omit [StandardBorelSpace Z] [Nonempty Z] in
lemma coordinate_information_chain (i : Fin n) :
    mutualInformation (coordinateJoint μ κ i) =
      cmi (attachSide g (coordinateJoint μ κ i)) +
      mutualInformation (coordinateJoint μ (κ.map (fun u j => g (u j))) i) := by
  have h := mutualInformation_attachSide_chain hg (coordinateJoint μ κ i)
  dsimp only at h
  rw [coordinateJoint_projection μ κ hg]
  unfold mutualInformation
  have hfst : ((coordinateJoint μ κ i).map (fun z => (g z.1,z.2))).fst =
      (coordinateJoint μ κ i).fst.map g := by
    rw [Measure.fst, Measure.map_map measurable_fst (by fun_prop),
      Measure.fst, Measure.map_map hg measurable_fst]
    rfl
  have hsnd : ((coordinateJoint μ κ i).map (fun z => (g z.1,z.2))).snd =
      (coordinateJoint μ κ i).snd := by
    rw [Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
    rfl
  rwa [hfst, hsnd]

lemma replica_information_inequality :
    (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
      totalCorrelation ((μ ⊗ₘ κ).snd.map (fun u i => g (u i))) ≤
      totalCorrelation (μ ⊗ₘ κ).snd + mutualInformation (μ ⊗ₘ κ) := by
  let κ' := κ.map (fun u i => g (u i))
  have : IsMarkovKernel κ' := Kernel.IsMarkovKernel.map _ (by fun_prop)
  have hc := conditionalTotalCorrelation_map_le μ κ hg
  have h := tuple_information_decomposition μ κ
  have h' := tuple_information_decomposition μ κ'
  have hm : (μ ⊗ₘ κ').snd = (μ ⊗ₘ κ).snd.map (fun u i => g (u i)) :=
    snd_compProd_map _ _ (by fun_prop)
  rw [← hm, ← h]
  have hs : (∑ i, mutualInformation (coordinateJoint μ κ i)) =
      (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
      ∑ i, mutualInformation (coordinateJoint μ κ' i) := by
    simp_rw [coordinate_information_chain μ κ hg, Finset.sum_add_distrib]
    rfl
  rw [hs]
  calc
    _ ≤ (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
        (totalCorrelation (μ ⊗ₘ κ').snd + mutualInformation (μ ⊗ₘ κ')) :=
      add_le_add le_rfl le_self_add
    _ = (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
        (conditionalTotalCorrelation μ κ' + ∑ i, mutualInformation (coordinateJoint μ κ' i)) := by
      rw [h']
    _ ≤ (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
        (conditionalTotalCorrelation μ κ + ∑ i, mutualInformation (coordinateJoint μ κ' i)) :=
      add_le_add le_rfl (add_le_add hc le_rfl)
    _ = _ := by ac_rfl

lemma replica_information_le_entropy [Fintype W] [MeasurableSingletonClass W] :
    (∑ i, cmi (attachSide g (coordinateJoint μ κ i))) +
      totalCorrelation ((μ ⊗ₘ κ).snd.map (fun u i => g (u i))) ≤
      totalCorrelation (μ ⊗ₘ κ).snd + ENNReal.ofReal (finiteEntropy μ) := by
  apply (replica_information_inequality μ κ hg).trans
  refine add_le_add le_rfl ?_
  have : IsProbabilityMeasure ((μ ⊗ₘ κ).map Prod.swap) := Measure.isProbabilityMeasure_map (by fun_prop)
  have h := mutualInformation_le_finiteEntropy ((μ ⊗ₘ κ).map Prod.swap)
  change mutualInformation ((μ ⊗ₘ κ).map Prod.swap) ≤ _ at h
  simpa only [mutualInformation_swap, Measure.snd_map_swap, Measure.fst_compProd] using h

end Projection
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
-- module Solutions.OAIQW_PosteriorReplicas.Measures_EqualRightMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma constrainedRows_eq_residualRows {d k m : ℕ} {u : Tuple d m}
    (hu : LinearIndependent ℝ (differences u)) :
    constrainedRows k u = (gaussianRows d k).map (residualRows u) := by
  unfold constrainedRows residualRows differenceSpan
  simp_rw [kernelComponent_eq_starProjection hu]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_TiltNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma bounded_withDensity_finite {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ≥0∞} {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    IsFiniteMeasure (μ.withDensity f) := by
  apply isFiniteMeasure_withDensity
  exact ne_top_of_le_ne_top (by simpa using ENNReal.mul_ne_top hL (measure_ne_top μ univ))
    (lintegral_mono hfL)

lemma tiltedFiber_probability {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    IsProbabilityMeasure (tiltedFiber base f A y) := by
  unfold tiltedFiber
  split_ifs with ha
  · infer_instance
  · constructor
    rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    change (tiltMass base f A y)⁻¹ * tiltMass base f A y = 1
    exact ENNReal.inv_mul_cancel ha (tiltMass_ne_top base hL hfL A y)

lemma tiltMass_smul_tiltedFiber {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    (A : Rows d k) (y : Labels k) :
    tiltMass base f A y • tiltedFiber base f A y = (baseFiber base A y).withDensity f := by
  by_cases ha : tiltMass base f A y = 0
  · have hz : f =ᵐ[baseFiber base A y] 0 := (lintegral_eq_zero_iff hf).mp ha
    rw [ha, zero_smul, withDensity_congr_ae hz, withDensity_zero]
  · rw [tiltedFiber, ite_eq_right ha, smul_smul,
      ENNReal.mul_inv_cancel ha (tiltMass_ne_top base hL hfL A y), one_smul]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_EqualLabelTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma ae_tilt_tuple_full_rank {d m : ℕ} (hd : 3 ≤ d) (hm : m < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (base.measure d).withDensity f),
      LinearIndependent ℝ (differences u) := by
  have : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hL hfL
  rw [pi_withDensity _ _ (fun _ => hf)]
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards [ae_base_tuple_full_rank hd hm base] with u hu
  exact fun _ => hu

lemma equalLabelRight_residual {d k m : ℕ} (hd : 3 ≤ d) (hm : m < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    equalLabelRight base f H = equalConstant k m *
      ∫⁻ u : Tuple d m, (ENNReal.ofReal (affineVolume u))⁻¹ ^ k *
        ∫⁻ A, H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k
        ∂Measure.pi (fun _ => (base.measure d).withDensity f) := by
  unfold equalLabelRight equalConstant
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_tilt_tuple_full_rank hd hm base hf hL hfL] with u hu
  rw [constrainedRows_eq_residualRows hu, lintegral_map (by fun_prop) (by unfold residualRows; fun_prop)]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_ReplicaMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

lemma equalReference_lintegral {d k m : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂equalReference ν = ∫⁻ u : Tuple d m, ∫⁻ A,
      H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k
      ∂Measure.pi (fun _ => ν) := by
  rw [equalReference, lintegral_map hH measurable_rightBasePoint,
    lintegral_prod _ (show AEMeasurable (fun z => H (rightBasePoint z)) _ from
      (hH.comp measurable_rightBasePoint).aemeasurable)]
  rfl

lemma density_power_cancel (m : ℕ) {a : ℝ≥0∞} (ha : a ≠ ∞) :
    a^(m+1) * a⁻¹^m = a := by
  by_cases h0 : a = 0
  · simp [h0]
  · rw [pow_succ, mul_comm (a^m) a, mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel h0 ha,
      one_pow, mul_one]

lemma replicaLaw_lintegral {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z, H z ∂replicaLaw base f =
      ∫⁻ A, ∫⁻ y, projectedDensity base f A y *
        ∫⁻ u, H (A,y,u) ∂Measure.pi (fun _ : Fin (m+1) => tiltedFiber base f A y)
        ∂volume ∂gaussianRows d k := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  have hG : Measurable (fun z : EqualSpace d k m =>
      (projectedDensity base f z.1 z.2.1)⁻¹^m * H z) := by fun_prop
  have he := equal_label_tilt_identity hd hk hm base hf hLt hfL hG
  rw [equalLabelRight_residual (by omega) (by omega) base hf hLt hfL hG] at he
  have hrep : (∫⁻ z, H z ∂replicaLaw base f) = equalLabelLeft base f
      (fun z : EqualSpace d k m => (projectedDensity base f z.1 z.2.1)⁻¹^m * H z) := by
    rw [he]
    rw [replicaLaw, lintegral_withDensity_eq_lintegral_mul _ (measurable_replicaDensity base hf) hH]
    simp only [Pi.mul_apply]
    rw [equalReference_lintegral (base.measure d |>.withDensity f) (by fun_prop)]
    unfold replicaDensity
    simp only
    rw [← lintegral_const_mul _ (show Measurable (fun u : Tuple d m =>
      (ENNReal.ofReal (affineVolume u))⁻¹^k *
      ∫⁻ A, (projectedDensity base f (residualRows u A)
        (labels (residualRows u A) (u 0)))⁻¹^m *
        H (residualRows u A, labels (residualRows u A) (u 0), u) ∂gaussianRows d k) by
      unfold residualRows; fun_prop)]
    apply lintegral_congr
    intro u
    rw [← mul_assoc, ← lintegral_const_mul _ (show Measurable (fun A =>
      (projectedDensity base f (residualRows u A)
        (labels (residualRows u A) (u 0)))⁻¹^m *
        H (residualRows u A, labels (residualRows u A) (u 0), u)) by unfold residualRows; fun_prop)]
    apply lintegral_congr
    intro A
    ring
  rw [hrep]
  unfold equalLabelLeft
  apply lintegral_congr
  intro A
  apply lintegral_congr
  intro y
  dsimp only
  rw [lintegral_const_mul _ (show Measurable (fun u : Tuple d m => H (A,y,u)) by fun_prop),
    ← mul_assoc, density_power_cancel m (projectedDensity_ne_top base hLt hfL A y)]

lemma lintegral_projectedDensity {d k : ℕ} {A : Rows d k} (hA : LinearIndependent ℝ A)
    (hk : k < d) (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, projectedDensity base f A y) = (base.measure d).withDensity f univ := by
  have h := congrArg (fun μ : Measure (Labels k) => μ univ) (projected_measure hA hk base hf)
  rw [Measure.map_apply (by unfold labels; fun_prop) MeasurableSet.univ,
    preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using h.symm

lemma replicaLaw_mass {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    replicaLaw (k := k) (m := m) base f univ = (base.measure d).withDensity f univ := by
  rw [← lintegral_one, replicaLaw_lintegral hd hk hm base hf hLt hfL measurable_const]
  have (A : Rows d k) (y : Labels k) := tiltedFiber_probability base hLt hfL A y
  simp only [lintegral_one, measure_univ, mul_one]
  calc
    _ = ∫⁻ (_ : Rows d k), (base.measure d).withDensity f univ ∂gaussianRows d k := by
      apply lintegral_congr_ae
      filter_upwards [ae_gaussian_rows_full_rank (by omega : 3 ≤ d) (by omega : k < d)] with A hA
      exact lintegral_projectedDensity hA (by omega) base hf
    _ = _ := by simp

lemma replicaLaw_probability {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)] :
    IsProbabilityMeasure (replicaLaw (k := k) (m := m) base f) := by
  constructor
  rw [replicaLaw_mass hd hk hm base hf hLt hfL, measure_univ]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ObservableLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma equalReference_tuple {d k m : ℕ} (ν : Measure (Vec d)) [IsProbabilityMeasure ν] :
    (equalReference (k := k) (m := m) ν).map (fun z => z.2.2) = Measure.pi (fun _ => ν) := by
  rw [equalReference,Measure.map_map (by fun_prop) measurable_rightBasePoint]
  change ((Measure.pi (fun _ : Fin (m+1) => ν)).prod (gaussianRows d k)).map Prod.fst = _
  simp only [Measure.map_fst_prod,measure_univ,one_smul]

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
-- module Solutions.OAIQW_PosteriorReplicas.Information_RandomCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma klDiv_random_tuple_observation {T Y Z : Type*}
    [MeasurableSpace T] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z]
    {n : ℕ} (β : Measure T) [IsProbabilityMeasure β]
    (Q : Measure (Fin n → Y)) [IsProbabilityMeasure Q]
    {g : T × Y → Z} (hg : Measurable g) :
    klDiv ((β.prod Q).map (fun z => (z.1,fun i => g (z.1,z.2 i))))
      ((β.prod (marginalProduct Q)).map (fun z => (z.1,fun i => g (z.1,z.2 i)))) =
      ∫⁻ b, totalCorrelation (Q.map (fun u i => g (b,u i))) ∂β := by
  let h : T × (Fin n → Y) → (Fin n → Z) := fun z i => g (z.1,z.2 i)
  have hh : Measurable h := by unfold h; fun_prop
  let κ := parametricMapKernel Q h
  let η := parametricMapKernel (marginalProduct Q) h
  have : IsMarkovKernel κ := parametricMapKernel_markov Q h hh
  have : IsMarkovKernel η := parametricMapKernel_markov (marginalProduct Q) h hh
  rw [← compProd_parametricMapKernel β Q hh,← compProd_parametricMapKernel β (marginalProduct Q) hh]
  change klDiv (β ⊗ₘ κ) (β ⊗ₘ η) = _
  rw [klDiv_compProd_kernel]
  apply lintegral_congr
  intro b
  simp only [κ,η,parametricMapKernel_apply _ hh,h]
  rw [totalCorrelation,marginalProduct_map (ν := Q) (g := fun y => g (b,y)) (by fun_prop)]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_PosteriorKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma posteriorKernel_markov {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    IsMarkovKernel (@posteriorKernel d k base f hf) :=
  ⟨fun z => tiltedFiber_probability base hLt hfL z.1 z.2⟩

lemma posterior_disintegration_lintegral {d k : ℕ} {A : Rows d k}
    (hA : LinearIndependent ℝ A) (hk : k < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞)
    (hfL : ∀ x, f x ≤ L) {H : Labels k × Vec d → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ x, H (labels A x,x) ∂(base.measure d).withDensity f) =
      ∫⁻ y, projectedDensity base f A y *
        ∫⁻ x, H (y,x) ∂tiltedFiber base f A y := by
  rw [weighted_base_lintegral hA hk base hf (show Measurable (fun x => H (labels A x,x)) by
    unfold labels; fun_prop)]
  apply lintegral_congr
  intro y
  by_cases hb : baseDensity base A y = 0
  · simp [projectedDensity,hb]
  have he : (∫⁻ x, f x * H (labels A x,x) ∂baseFiber base A y) =
      ∫⁻ x, H (y,x) ∂(baseFiber base A y).withDensity f := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hf (show Measurable (fun x => H (y,x)) by fun_prop)]
    simp only [Pi.mul_apply]
    rw [baseFiber_eq_map,
      lintegral_map (show Measurable (fun x => f x * H (labels A x,x)) by unfold labels; fun_prop)
        (measurable_basePoint_fixed base A y),
      lintegral_map (show Measurable (fun x => f x * H (y,x)) by fun_prop)
        (measurable_basePoint_fixed base A y)]
    simp only [labels_basePoint hA]
  rw [he, ← tiltMass_smul_tiltedFiber base hf hLt hfL A y, lintegral_smul_measure]
  simp only [projectedDensity, smul_eq_mul, mul_assoc]

lemma dataLaw_density {d k : ℕ} (hd : 3 ≤ d) (hk : k < d) (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞)
    (hfL : ∀ x, f x ≤ L) :
    dataLaw (k := k) ((base.measure d).withDensity f) =
      ((gaussianRows d k).prod volume).withDensity (fun z => projectedDensity base f z.1 z.2) := by
  let : NeZero d := ⟨by omega⟩
  have := bounded_withDensity_finite (base.measure d) hLt hfL
  apply Measure.ext_of_lintegral
  intro H hH
  rw [dataLaw, lintegral_map hH (by unfold labels; fun_prop), lintegral_prod _ (by unfold labels; fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_projectedDensity base hf) hH,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_gaussian_rows_full_rank hd hk] with A hA
  have h := posterior_disintegration_lintegral hA hk base hf hLt hfL
    (H := fun z : Labels k × Vec d => H (A,z.1)) (by fun_prop)
  have (y : Labels k) := tiltedFiber_probability base hLt hfL A y
  simpa using h

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

section
variable {T Y Z : Type*} [MeasurableSpace T] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace Y] [StandardBorelSpace Z] [Nonempty Y] [Nonempty Z]
  {n : ℕ}

omit [StandardBorelSpace Y] [Nonempty Y] [Nonempty Z] in
lemma measurable_projected_totalCorrelation (ν : Measure (Fin n → Y)) [IsProbabilityMeasure ν]
    {g : T × Y → Z} (hg : Measurable g) :
    Measurable (fun b => totalCorrelation (ν.map (fun u i => g (b,u i)))) := by
  let h : T × (Fin n → Y) → (Fin n → Z) := fun z i => g (z.1,z.2 i)
  have hh : Measurable h := by fun_prop
  let κ := parametricMapKernel ν h
  have : IsMarkovKernel κ := parametricMapKernel_markov ν h hh
  have hc := measurable_kernel_klDiv κ (piKernel (coordKernel κ))
  simp only [piKernel_apply, coordKernel_apply] at hc
  change Measurable (fun b => totalCorrelation (κ b)) at hc
  simpa only [κ, parametricMapKernel_apply ν hh, h] using hc
end

section
variable {T W Y Z : Type*} [MeasurableSpace T] [MeasurableSpace W]
  [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace W] [Nonempty W] [Fintype W] [MeasurableSingletonClass W]
  [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z]
  {n : ℕ} (β : Measure T) [IsProbabilityMeasure β]
  (μ : Measure W) [IsProbabilityMeasure μ]
  (κ : Kernel W (Fin n → Y)) [IsMarkovKernel κ]
  {g : T × Y → Z} (hg : Measurable g)
include hg

lemma random_replica_information_le_entropy :
    (∑ i, cmi (randomSideLaw β g (coordinateJoint μ κ i))) +
      (∫⁻ b, totalCorrelation ((μ ⊗ₘ κ).snd.map (fun u i => g (b,u i))) ∂β) ≤
      totalCorrelation (μ ⊗ₘ κ).snd + ENNReal.ofReal (finiteEntropy μ) := by
  have hi (i : Fin n) := measurable_cmi_attachSide hg (coordinateJoint μ κ i)
  have ht := measurable_projected_totalCorrelation (μ ⊗ₘ κ).snd hg
  have h := lintegral_mono (μ := β) (fun b =>
    replica_information_le_entropy μ κ (g := fun y => g (b,y)) (by fun_prop))
  rw [lintegral_add_aux (Finset.measurable_sum _ (fun i _ => hi i)) ht,
    lintegral_finsetSum _ (fun i _ => hi i)] at h
  simp only [lintegral_const, measure_univ, mul_one] at h
  simpa only [cmi_randomSideLaw β hg] using h

lemma random_replica_information_identical (q : Measure (Y × W)) [IsProbabilityMeasure q]
    (hq : ∀ i, coordinateJoint μ κ i = q) :
    (n : ℝ≥0∞) * cmi (randomSideLaw β g q) +
      (∫⁻ b, totalCorrelation ((μ ⊗ₘ κ).snd.map (fun u i => g (b,u i))) ∂β) ≤
      totalCorrelation (μ ⊗ₘ κ).snd + ENNReal.ofReal (finiteEntropy μ) := by
  have h := random_replica_information_le_entropy β μ κ hg
  have hs : (∑ i, cmi (randomSideLaw β g (coordinateJoint μ κ i))) =
      (n : ℝ≥0∞) * cmi (randomSideLaw β g q) := by
    calc
      _ = ∑ _i : Fin n, cmi (randomSideLaw β g q) := by
        apply Finset.sum_congr rfl
        intro i _
        cases hq i
        rfl
      _ = _ := by simp
  rw [hs] at h
  exact h
end

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ReplicaMeasureInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma random_replica_measure_information {T W Y Z : Type*}
    [MeasurableSpace T] [MeasurableSpace W] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace W] [Nonempty W] [Fintype W] [MeasurableSingletonClass W]
    [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z]
    {n : ℕ} (β : Measure T) [IsProbabilityMeasure β]
    (Q : Measure ((Fin n → Y) × W)) [IsProbabilityMeasure Q]
    (q : Measure (Y × W)) [IsProbabilityMeasure q]
    (hq : ∀ i, Q.map (fun z => (z.1 i,z.2)) = q)
    {g : T × Y → Z} (hg : Measurable g) :
    (n : ℝ≥0∞)*cmi (randomSideLaw β g q) +
      (∫⁻ b, totalCorrelation (Q.fst.map (fun u i => g (b,u i))) ∂β) ≤
      totalCorrelation Q.fst + ENNReal.ofReal (finiteEntropy Q.snd) := by
  let R := Q.map Prod.swap
  have : IsProbabilityMeasure R := by dsimp [R]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hl (i : Fin n) : coordinateJoint R.fst R.condKernel i = q := by
    rw [coordinateJoint, coordKernel, Measure.compProd_map (measurable_pi_apply i),
      Measure.disintegrate R R.condKernel]
    change ((Q.map Prod.swap).map (fun z => (z.1,z.2 i))).map Prod.swap = q
    rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    exact hq i
  have h := random_replica_information_identical β R.fst R.condKernel hg q hl
  rw [Measure.disintegrate R R.condKernel] at h
  simpa only [R,Measure.fst_map_swap,Measure.snd_map_swap] using h

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_PosteriorExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma replicaLaw_eq_dataKernel {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    replicaLaw (k := k) (m := m) base f =
      (dataLaw (k := k) ((base.measure d).withDensity f) ⊗ₘ
        piKernel (fun _ : Fin (m+1) => posteriorKernel base hf)).map
        (fun z => (z.1.1,z.1.2,z.2)) := by
  let : NeZero d := ⟨by omega⟩
  let := bounded_withDensity_finite (base.measure d) hLt hfL
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  let : IsFiniteMeasure (dataLaw (k := k) ((base.measure d).withDensity f)) := by
    unfold dataLaw
    infer_instance
  apply Measure.ext_of_lintegral
  intro H hH
  rw [replicaLaw_lintegral hd hk hm base hf hLt hfL hH,
    lintegral_map hH (by fun_prop), Measure.lintegral_compProd (by fun_prop),
    dataLaw_density (by omega) (by omega) base hf hLt hfL,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_projectedDensity base hf) (by fun_prop),
    lintegral_prod _ (by fun_prop)]
  simp only [Pi.mul_apply]
  simp_rw [piKernel_apply]
  rfl

lemma dataSignal_lintegral {d k : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : Data d k × Vec d → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ z, ∫⁻ x, H (z,x) ∂posteriorKernel base hf z
      ∂dataLaw (k := k) ((base.measure d).withDensity f)) =
      ∫⁻ A, ∫⁻ x, H ((A,labels A x),x) ∂(base.measure d).withDensity f ∂gaussianRows d k := by
  let : NeZero d := ⟨by omega⟩
  let := bounded_withDensity_finite (base.measure d) hLt hfL
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  rw [dataLaw_density hd hk base hf hLt hfL,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_projectedDensity base hf) (by fun_prop),
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_gaussian_rows_full_rank hd hk] with A hA
  exact (posterior_disintegration_lintegral hA hk base hf hLt hfL
    (H := fun z => H ((A,z.1),z.2)) (by fun_prop)).symm

lemma posteriorMessageLaw_probability {d k m N : ℕ} (base : BaseLaw)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    IsProbabilityMeasure (posteriorMessageLaw (m := m) base hf κ) := by
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  unfold posteriorMessageLaw
  infer_instance

lemma posteriorMessageLaw_coordinate {d k m N : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] (i : Fin (m+1)) :
    (posteriorMessageLaw (m := m) base hf κ).map (fun z => (z.1 i,z.2)) =
      signalMessageLaw ((base.measure d).withDensity f) κ := by
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  have (z : Data d k) := tiltedFiber_probability base hLt hfL z.1 z.2
  apply Measure.ext_of_lintegral
  intro H hH
  rw [posteriorMessageLaw, Measure.snd, Measure.map_map (by fun_prop) measurable_snd,
    lintegral_map hH (by fun_prop), Measure.lintegral_compProd (by fun_prop)]
  simp only [Kernel.prod_apply, piKernel_apply]
  have hp (z : Data d k) :
      (∫⁻ uw, H (uw.1 i,uw.2) ∂(Measure.pi (fun _ : Fin (m+1) => posteriorKernel base hf z)).prod (κ z)) =
      ∫⁻ x, ∫⁻ w, H (x,w) ∂κ z ∂posteriorKernel base hf z := by
    rw [lintegral_prod _ (by fun_prop)]
    exact (measurePreserving_eval (fun _ : Fin (m+1) => posteriorKernel base hf z) i).lintegral_comp
      (show Measurable (fun x : Vec d => ∫⁻ w, H (x,w) ∂κ z) by fun_prop)
  change (∫⁻ z, ∫⁻ uw, H (uw.1 i,uw.2)
    ∂(Measure.pi (fun _ : Fin (m+1) => posteriorKernel base hf z)).prod (κ z)
    ∂dataLaw ((base.measure d).withDensity f)) = _
  simp_rw [hp]
  have hK : Measurable (fun z : Data d k × Vec d => ∫⁻ w, H (z.2,w) ∂κ z.1) := by
    exact (hH.comp (show Measurable (fun z : (Data d k × Vec d) × Fin N => (z.1.2,z.2)) by fun_prop)).lintegral_kernel_prod_right'
      (κ := κ.comap Prod.fst measurable_fst)
  rw [dataSignal_lintegral hd hk base hf hLt hfL hK]
  rw [signalMessageLaw, lintegral_map hH (by fun_prop), Measure.lintegral_compProd (by fun_prop)]
  have hK' : Measurable (fun a : Vec d × Rows d k => ∫⁻ w, H (a.1,w) ∂messageKernel κ a) := by
    exact (hH.comp (show Measurable (fun z : (Vec d × Rows d k) × Fin N => (z.1.1,z.2)) by fun_prop)).lintegral_kernel_prod_right'
      (κ := messageKernel κ)
  rw [lintegral_prod _ (show AEMeasurable (fun a : Vec d × Rows d k =>
    ∫⁻ w, H (a.1,w) ∂messageKernel κ a) _ from hK'.aemeasurable)]
  simp only [messageKernel, Kernel.comap_apply]
  exact lintegral_lintegral_swap
    ((hK.comp (show Measurable (fun z : Rows d k × Vec d => ((z.1,labels z.1 z.2),z.2)) by
      unfold labels; fun_prop)).aemeasurable)

lemma posteriorMessageLaw_tuple {d k m N : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    (posteriorMessageLaw (m := m) base hf κ).fst = (replicaLaw (k := k) (m := m) base f).map (fun z => z.2.2) := by
  let := posteriorKernel_markov (k := k) base hf hLt hfL
  let := posteriorMessageLaw_probability (m := m) base hf hLt hfL κ
  rw [replicaLaw_eq_dataKernel hd hk hm base hf hLt hfL,
    Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.ext_of_lintegral
  intro H hH
  rw [posteriorMessageLaw, Measure.fst, Measure.snd,
    Measure.map_map measurable_fst measurable_snd,
    lintegral_map hH (by fun_prop), lintegral_map hH (by fun_prop),
    Measure.lintegral_compProd (by fun_prop), Measure.lintegral_compProd (by fun_prop)]
  apply lintegral_congr
  intro z
  rw [Kernel.prod_apply, lintegral_prod _ (by fun_prop)]
  simp

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Kernels_ReplicaTupleMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma signalMessageLaw_fst {d k N : ℕ} (p : Measure (Vec d)) [IsProbabilityMeasure p]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] : (signalMessageLaw p κ).fst = p := by
  rw [signalMessageLaw,Measure.fst,Measure.map_map measurable_fst (by fun_prop)]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop),Measure.lintegral_compProd (by fun_prop)]
  simp only [Function.comp_def,lintegral_const,measure_univ,mul_one]
  rw [lintegral_prod _ (by fun_prop)]
  simp

lemma posteriorMessageLaw_message {d k m N : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    (posteriorMessageLaw (m := m) base hf κ).snd = (signalMessageLaw ((base.measure d).withDensity f) κ).snd := by
  rw [← posteriorMessageLaw_coordinate hd hk base hf hLt hfL κ (0 : Fin (m+1)),
    Measure.snd,Measure.snd,Measure.map_map measurable_snd (by fun_prop)]
  rfl

lemma posteriorMessageLaw_coordinateMarginal {d k m N : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] (i : Fin (m+1)) :
    coordinateMarginal (posteriorMessageLaw (m := m) base hf κ).fst i =
      (base.measure d).withDensity f := by
  rw [← signalMessageLaw_fst ((base.measure d).withDensity f) κ,
    ← posteriorMessageLaw_coordinate hd hk base hf hLt hfL κ i]
  rw [coordinateMarginal,Measure.fst,Measure.map_map (measurable_pi_apply i) measurable_fst,
    Measure.fst,Measure.map_map measurable_fst (by fun_prop)]
  rfl

lemma posteriorMessageLaw_marginalProduct {d k m N : ℕ} (hd : 3 ≤ d) (hk : k < d)
    (base : BaseLaw) {f : Vec d → ℝ≥0∞} (hf : Measurable f)
    {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((base.measure d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    marginalProduct (posteriorMessageLaw (m := m) base hf κ).fst =
      Measure.pi (fun _ : Fin (m+1) => (base.measure d).withDensity f) := by
  unfold marginalProduct
  congr 1
  funext i
  exact posteriorMessageLaw_coordinateMarginal hd hk base hf hLt hfL κ i

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Information_ObservationCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma observe_law {d ℓ k m : ℕ} (μ : Measure (EqualSpace d k m)) [SFinite μ] :
    (μ.prod (auxLaw d ℓ k)).map observe =
      ((auxLaw d ℓ k).prod (μ.map (fun z => z.2.2))).map
        (fun z => (z.1,projectedTuple z.1.1 z.2)) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (by fun_prop),lintegral_map hH (by fun_prop),
    lintegral_prod _ (by fun_prop),lintegral_prod _ (by fun_prop)]
  calc
    _ = ∫⁻ b, ∫⁻ z, H (b,projectedTuple b.1 z.2.2) ∂μ ∂auxLaw d ℓ k :=
      lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      apply lintegral_congr
      intro b
      rw [lintegral_map (by fun_prop) (by fun_prop)]

lemma totalCorrelation_projectedTuple {d ℓ m : ℕ} (Q : Measure (Tuple d m)) [IsProbabilityMeasure Q]
    (B : Rows d ℓ) : totalCorrelation (Q.map (projectedTuple B)) =
      totalCorrelation (Q.map (fun u i => labels B (u i))) := by
  let h : (Fin (m+1) → Labels ℓ) → Tuple ℓ m := fun y i => WithLp.toLp 2 (y i)
  let h' : Tuple ℓ m → (Fin (m+1) → Labels ℓ) := fun y i => WithLp.ofLp (y i)
  have hh : Measurable h := by unfold h; fun_prop
  have hh' : Measurable h' := by unfold h'; fun_prop
  have he : Q.map (projectedTuple B) = (Q.map (fun u i => labels B (u i))).map h := by
    rw [Measure.map_map hh (by unfold labels; fun_prop)]
    rfl
  rw [he]
  change totalCorrelation ((Q.map (fun u i => labels B (u i))).map (fun y i => WithLp.toLp 2 (y i))) = _
  simp only [totalCorrelation]
  have : IsProbabilityMeasure (Q.map (fun u i => labels B (u i))) := by exact Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by unfold labels; fun_prop))
  rw [marginalProduct_map (ν := Q.map (fun u i => labels B (u i))) (g := WithLp.toLp 2) (by fun_prop)]
  exact klDiv_map_leftInverse _ _ hh hh' (fun _ => rfl)

lemma observe_klDiv_eq_correlation {d ℓ k m : ℕ} (μ ν : Measure (EqualSpace d k m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν.map (fun z => z.2.2) = marginalProduct (μ.map (fun z => z.2.2))) :
    klDiv ((μ.prod (auxLaw d ℓ k)).map observe) ((ν.prod (auxLaw d ℓ k)).map observe) =
      ∫⁻ B, totalCorrelation ((μ.map (fun z => z.2.2)).map (fun u i => labels B (u i))) ∂gaussianRows d ℓ := by
  have : IsProbabilityMeasure (μ.map (fun z => z.2.2)) := by exact Measure.isProbabilityMeasure_map (by fun_prop)
  rw [observe_law,observe_law,hν]
  change klDiv (((auxLaw d ℓ k).prod (μ.map (fun z => z.2.2))).map
      (fun z => (z.1,fun i => WithLp.toLp 2 (labels z.1.1 (z.2 i)))))
    (((auxLaw d ℓ k).prod (marginalProduct (μ.map (fun z => z.2.2)))).map
      (fun z => (z.1,fun i => WithLp.toLp 2 (labels z.1.1 (z.2 i))))) = _
  rw [klDiv_random_tuple_observation (auxLaw d ℓ k) (μ.map (fun z => z.2.2)) (g := fun z : AuxSpace d ℓ k × Vec d => WithLp.toLp 2 (labels z.1.1 z.2)) (by unfold labels; fun_prop)]
  have he (b : AuxSpace d ℓ k) : totalCorrelation ((μ.map (fun z => z.2.2)).map
      (fun u i => WithLp.toLp 2 (labels b.1 (u i)))) =
      totalCorrelation ((μ.map (fun z => z.2.2)).map (fun u i => labels b.1 (u i))) :=
    totalCorrelation_projectedTuple _ b.1
  simp_rw [he]
  rw [auxLaw,lintegral_prod _ (by
    exact ((measurable_projected_totalCorrelation (μ.map (fun z => z.2.2)) measurable_labels).comp measurable_fst).aemeasurable)]
  simp only [lintegral_const,measure_univ,mul_one]

lemma replica_tuple_klDiv_le {d k m N : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    totalCorrelation (posteriorMessageLaw (m := m) .spherical hf κ).fst ≤
      klDiv (replicaLaw (k := k) (m := m) .spherical f) (equalReference ((sphereLaw d).withDensity f)) := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := posteriorMessageLaw_probability (m := m) .spherical hf hLt hfL κ
  have := replicaLaw_probability hd hk hm .spherical hf hLt hfL
  rw [totalCorrelation,posteriorMessageLaw_marginalProduct (by omega) (by omega) .spherical hf hLt hfL κ,
    posteriorMessageLaw_tuple hd hk hm .spherical hf hLt hfL κ]
  change klDiv _ (Measure.pi (fun _ => (sphereLaw d).withDensity f)) ≤ _
  rw [← equalReference_tuple (k := k) ((sphereLaw d).withDensity f)]
  exact klDiv_map_le _ _ (by fun_prop)

lemma replica_observe_klDiv_eq {d ℓ k m N : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    klDiv (((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)).map observe)
      (((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)).map observe) =
      ∫⁻ B, totalCorrelation ((posteriorMessageLaw (m := m) .spherical hf κ).fst.map
        (fun u i => labels B (u i))) ∂gaussianRows d ℓ := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := posteriorMessageLaw_probability (m := m) .spherical hf hLt hfL κ
  have := replicaLaw_probability hd hk hm .spherical hf hLt hfL
  rw [posteriorMessageLaw_tuple hd hk hm .spherical hf hLt hfL κ]
  apply observe_klDiv_eq_correlation
  rw [← posteriorMessageLaw_tuple hd hk hm .spherical hf hLt hfL κ,
    posteriorMessageLaw_marginalProduct (by omega) (by omega) .spherical hf hLt hfL κ,
    equalReference_tuple]
  rfl

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

lemma information_of_correlation_loss {t : ℕ} (ht : 0<t) {I B D : ℝ≥0∞} {H C : ℝ}
    (hD : D ≠ ∞) (hH : 0 ≤ H) (hinfo : (t:ℝ≥0∞)*I+B ≤ D+ENNReal.ofReal H)
    (hloss : D.toReal ≤ B.toReal+C) : I ≤ ENNReal.ofReal ((H+C)/(t:ℝ)) := by
  have hR : D+ENNReal.ofReal H ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hD,ENNReal.ofReal_ne_top⟩
  have hB : B ≠ ∞ := ne_top_of_le_ne_top hR ((le_add_left le_rfl).trans hinfo)
  have hM : (t:ℝ≥0∞)*I ≠ ∞ := ne_top_of_le_ne_top hR ((le_add_right le_rfl).trans hinfo)
  have htn : (t:ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
  have hI : I ≠ ∞ := by intro h; simp [h,htn] at hM
  have hr := ENNReal.toReal_mono hR hinfo
  rw [ENNReal.toReal_add hM hB,ENNReal.toReal_add hD ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hH] at hr
  have htr : 0 < (t:ℝ) := by exact_mod_cast ht
  have hi : I.toReal ≤ (H+C)/(t:ℝ) := by
    apply (le_div_iff₀ htr).mpr
    nlinarith
  rw [← ENNReal.ofReal_toReal hI]
  exact ENNReal.ofReal_le_ofReal hi

lemma gaussian_replica_information_cost_oai {d ℓ k m N : ℕ} [NeZero N]
    (hd : 4*k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m≤ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] (J : ℕ)
    (hcut : (L*ENNReal.ofReal ((72:ℝ)^d))*ENNReal.ofReal ((1/2:ℝ)^J)*
      (1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    conditionalInformation (sideLaw ℓ (signalMessageLaw ((sphereLaw d).withDensity f) κ)) ≤
      ENNReal.ofReal ((messageEntropy (signalMessageLaw ((sphereLaw d).withDensity f) κ)+
        comparisonCost d ℓ k m J)/((m+1:ℕ):ℝ)) := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have hd' : k+m+2 ≤ d := by omega
  have := posteriorMessageLaw_probability (m := m) .spherical hf hLt hfL κ
  have := replicaLaw_probability hd' hk hm .spherical hf hLt hfL
  let Q := posteriorMessageLaw (m := m) .spherical hf κ
  let q := signalMessageLaw ((sphereLaw d).withDensity f) κ
  have hinfo := random_replica_measure_information (gaussianRows d ℓ) Q q
    (fun i => posteriorMessageLaw_coordinate (by omega) (by omega) .spherical hf hLt hfL κ i)
    (g := fun z => labels z.1 z.2) measurable_labels
  have hQ : Q.snd = q.snd := posteriorMessageLaw_message (by omega) (by omega) .spherical hf hLt hfL κ
  rw [hQ] at hinfo
  have hTC := replica_tuple_klDiv_le hd' hk hm hf hLt hfL κ
  have hinfo' := hinfo.trans (add_le_add hTC le_rfl)
  have hloss := replica_lifted_loss hd hk hm hkm hf hLt hfL J hcut
  rw [replica_observe_klDiv_eq hd' hk hm hf hLt hfL κ] at hloss
  exact information_of_correlation_loss (by omega : 0 < m + 1)
    (replica_klDiv_ne_top hd hk hm hf hLt hfL) (finiteEntropy_nonneg q.snd) hinfo' hloss

end PosteriorReplicas
end

end OAI
end

theorem solution : type_of% @OAI.PosteriorReplicas.gaussian_replica_information_cost_oai := @OAI.PosteriorReplicas.gaussian_replica_information_cost_oai
