-- Prove2me | solution 1 for OAI.PosteriorReplicas.ae_expectedDensity_le_inverse
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:37:39.967753+00:00
-- url     : https://prove2.me/submissions/00b85389-f976-48da-96dc-2f1373d11815

import Mathlib
import Definitions.Def_PosteriorReplicas
import Definitions.Def_OAIQWPR000
import Theorems.Thm_OAI_PosteriorReplicas_equalLabelVersions

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
-- module Solutions.OAIQW_PosteriorReplicas.Regression_GaussianNoise
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
section GaussianNoise
lemma pi_gaussian_map_scale (m : ℕ) (δ : ℝ) :
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
      (fun u => fun j => δ * u j) =
      Measure.pi (fun _ : Fin m => gaussianReal 0 (NNReal.mk (δ^2) (sq_nonneg δ))) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : ℝ => δ * x)
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => δ * x)).aemeasurable)]
  simp_rw [gaussianReal_map_const_mul, mul_zero, mul_one]

end GaussianNoise

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
    exact (OuterMeasure.pi_pi_le _ s).trans (Finset.prod_le_prod' fun i _ => h i (s i))
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi_def, Measure.pi_def, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  exact ho s

lemma pi_gaussianReal_le_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≤ (volume : Measure (Fin n → ℝ)) :=
  measure_pi_mono (fun _ => gaussianReal_le_volume)
end GaussianDomination

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
-- module Solutions.OAIQW_PosteriorReplicas.Regression_SupportVolume
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
section SupportVolume
open scoped Pointwise

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_inner_map (u : E) :
    (stdGaussian E).map (fun x => ⟪u, x⟫) =
      gaussianReal 0 (NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖)) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ u)
  have he : (⇑(innerSL ℝ u)) = (fun x => ⟪u, x⟫) := by
    ext x
    exact innerSL_apply_apply ℝ u x
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  rw [he] at h
  have hh : (‖u‖^2).toNNReal = NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖) := by
    ext
    simp
  simpa only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hh] using h

lemma rows_inner_map (u : E) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j => ⟪u, A j⟫) =
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun x => ‖u‖ • x) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : E => ⟪u, x⟫)
    (fun _ => (by fun_prop : Measurable (fun x : E => ⟪u, x⟫)).aemeasurable)]
  simp_rw [stdGaussian_inner_map]
  exact (pi_gaussian_map_scale m ‖u‖).symm

end Rows

end SupportVolume

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

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_EuclideanLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

lemma euclidean_label_ball_volume {k : ℕ} (y : Labels k) (r : ℝ) :
    (volume : Measure (Vec k)) (ball (WithLp.toLp 2 y) r) =
      (volume : Measure (Labels k)) {v | labelNorm v < r} := by
  rw [Measure.addHaar_ball_center]
  rw [← (PiLp.volume_preserving_toLp (Fin k)).measure_preimage (by measurability)]
  congr 1
  ext v
  simp only [mem_preimage, mem_ball, dist_zero_right]
  rfl

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Measures_ConstrainedDensityExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma volume_labels_smul {k : ℕ} {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Labels k)).map (fun x => r • x) =
      ENNReal.ofReal (r⁻¹^k) • (volume : Measure (Labels k)) := by
  have he : (fun x : Labels k => r • x) = Matrix.toLin' (r • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
    funext x
    simp
  rw [he, Real.map_matrix_volume_pi_eq_smul_volume_pi (by simp [hr.ne'])]
  simp [inv_pow, abs_of_pos hr]

lemma gaussian_rows_inner_le_volume {d k : ℕ} {v : Vec d} (hv : v ≠ 0) :
    (gaussianRows d k).map (fun A => fun i => ⟪v, A i⟫) ≤
      ENNReal.ofReal (‖v‖⁻¹^k) • (volume : Measure (Labels k)) := by
  rw [gaussianRows, PosteriorRegression.rows_inner_map]
  calc
    _ ≤ (volume : Measure (Labels k)).map (fun x => ‖v‖ • x) :=
      Measure.map_mono (PosteriorRegression.pi_gaussianReal_le_volume k) (by fun_prop)
    _ = _ := volume_labels_smul (norm_pos_iff.mpr hv)

lemma projected_rows_ball_bound {d k : ℕ} (U : Submodule ℝ (Vec d)) (p x : Vec d)
    (hx : U.starProjection (x-p) ≠ 0) (r : ℝ) :
    gaussianRows d k {A | labelNorm (labels (fun i => U.starProjection (A i)) x -
      labels (fun i => U.starProjection (A i)) p) < r} ≤
        ENNReal.ofReal (‖U.starProjection (x-p)‖⁻¹^k) *
          volume {y : Labels k | labelNorm y < r} := by
  have hl (A : Rows d k) :
      labels (fun i => U.starProjection (A i)) x - labels (fun i => U.starProjection (A i)) p =
        fun i => ⟪U.starProjection (x-p), A i⟫ := by
    ext i
    change ⟪U.starProjection (A i), x⟫ - ⟪U.starProjection (A i), p⟫ = _
    rw [← inner_sub_right, U.inner_starProjection_left_eq_right, real_inner_comm]
  simp_rw [hl]
  have h := gaussian_rows_inner_le_volume (k := k) hx {y : Labels k | labelNorm y < r}
  rw [Measure.map_apply (by fun_prop) (measurableSet_lt (by fun_prop) measurable_const),
    Measure.smul_apply, smul_eq_mul] at h
  exact h

lemma label_ball_pos {k : ℕ} {r : ℝ} (hr : 0 < r) :
    0 < (volume : Measure (Labels k)) {y | labelNorm y < r} := by
  rw [← euclidean_label_ball_volume (0 : Labels k) r]
  exact (isOpen_ball.measure_pos volume) (⟨0, mem_ball_self hr⟩)

lemma label_ball_ne_top {k : ℕ} (r : ℝ) :
    (volume : Measure (Labels k)) {y | labelNorm y < r} ≠ ∞ := by
  have he := euclidean_label_ball_volume (0 : Labels k) r
  rw [← he]
  exact (measure_ball_lt_top).ne

lemma expected_ballDensityVersion_le {d k : ℕ} (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (U : Submodule ℝ (Vec d)) (p : Vec d)
    (hnull : ∀ᵐ x ∂ν, U.starProjection (x-p) ≠ 0) :
    (∫⁻ A, ballDensityVersion ν (fun i => U.starProjection (A i))
      (labels (fun i => U.starProjection (A i)) p) ∂gaussianRows d k) ≤
        ∫⁻ x, ENNReal.ofReal (‖U.starProjection (x-p)‖⁻¹^k) ∂ν := by
  let f : ℕ → Rows d k → ℝ≥0∞ := fun n A =>
    ((volume : Measure (Labels k)) {y | labelNorm y < (n+1:ℝ)⁻¹})⁻¹ *
      ν {x | labelNorm (labels (fun i => U.starProjection (A i)) x -
        labels (fun i => U.starProjection (A i)) p) < (n+1:ℝ)⁻¹}
  have hf (n : ℕ) : Measurable (f n) := by
    apply Measurable.const_mul
    exact measurable_measure_prodMk_left (show MeasurableSet
      {z : Rows d k × Vec d | labelNorm (labels (fun i => U.starProjection (z.1 i)) z.2 -
        labels (fun i => U.starProjection (z.1 i)) p) < (n+1:ℝ)⁻¹} by
      apply measurableSet_lt _ measurable_const
      exact continuous_labelNorm.measurable.comp (by fun_prop))
  change (∫⁻ A, liminf (fun n => f n A) atTop ∂gaussianRows d k) ≤ _
  apply (lintegral_liminf_le hf).trans
  apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro n
  let r : ℝ := (n+1:ℝ)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  let S : Set (Rows d k × Vec d) := {z | labelNorm (labels (fun i => U.starProjection (z.1 i)) z.2 -
    labels (fun i => U.starProjection (z.1 i)) p) < r}
  have hS : MeasurableSet S := by
    apply measurableSet_lt _ measurable_const
    exact continuous_labelNorm.measurable.comp (by fun_prop)
  have hs : (∫⁻ A, ν {x | (A,x) ∈ S} ∂gaussianRows d k) =
      ∫⁻ x, gaussianRows d k {A | (A,x) ∈ S} ∂ν := by
    exact (Measure.prod_apply (μ := gaussianRows d k) (ν := ν) hS).symm.trans
      (Measure.prod_apply_symm (μ := gaussianRows d k) (ν := ν) hS)
  calc
    _ = ((volume : Measure (Labels k)) {y | labelNorm y < r})⁻¹ *
        ∫⁻ x, gaussianRows d k {A | (A,x) ∈ S} ∂ν := by
      rw [← hs]
      change (∫⁻ A, ((volume : Measure (Labels k)) {y | labelNorm y < r})⁻¹ *
        ν (Prod.mk A ⁻¹' S) ∂gaussianRows d k) = _
      exact lintegral_const_mul _ (measurable_measure_prodMk_left hS)
    _ ≤ ((volume : Measure (Labels k)) {y | labelNorm y < r})⁻¹ *
        ∫⁻ x, ENNReal.ofReal (‖U.starProjection (x-p)‖⁻¹^k) *
          volume {y : Labels k | labelNorm y < r} ∂ν := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [hnull] with x hx
      exact projected_rows_ball_bound U p x hx r
    _ = _ := by
      rw [lintegral_mul_const _ (by fun_prop), mul_comm (∫⁻ x, _ ∂ν), ← mul_assoc,
        ENNReal.inv_mul_cancel (label_ball_pos hr).ne' (label_ball_ne_top r), one_mul]

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_DensityBinsGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma affine_infDist_orthogonal {d : ℕ} (p x : Vec d) (U : Submodule ℝ (Vec d)) :
    Metric.infDist x (AffineSubspace.mk' p U : Set (Vec d)) = ‖Uᗮ.starProjection (x-p)‖ := by
  rw [PosteriorRegression.infDist_affine_mk', Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

lemma tupleDistance_eq_infDist {d m : ℕ} (u : Tuple d m) (x : Vec d) :
    tupleDistance u x = Metric.infDist x (AffineSubspace.mk' (u 0) (differenceSpan u) : Set (Vec d)) :=
  (affine_infDist_orthogonal _ _ _).symm

lemma differenceSpan_finrank_le {d m : ℕ} (u : Tuple d m) :
    Module.finrank ℝ (differenceSpan u) ≤ m := by
  change Module.finrank ℝ (Submodule.span ℝ (range (differences u))) ≤ m
  simpa only [Set.finrank, Fintype.card_fin] using
    finrank_range_le_card (R := ℝ) (differences u)

lemma tupleDistance_pos_ae {d m : ℕ} (hd : 3 ≤ d) (hm : m < d) (u : Tuple d m)
    (f : Vec d → ℝ≥0∞) :
    ∀ᵐ x ∂(sphereLaw d).withDensity f, 0 < tupleDistance u x := by
  let S := AffineSubspace.mk' (u 0) (differenceSpan u)
  have hz : sphereLaw d S = 0 := by
    apply base_affine_null hd .spherical S
    rw [AffineSubspace.direction_mk']
    exact (differenceSpan_finrank_le u).trans_lt hm
  have hn : ∀ᵐ x ∂sphereLaw d, x ∉ S := by
    rw [ae_iff]
    simp only [not_not]
    convert hz using 2
    ext x
    rfl
  filter_upwards [(withDensity_absolutelyContinuous (sphereLaw d) f).ae_le hn] with x hx
  rw [tupleDistance_eq_infDist]
  exact (S.closed_of_finiteDimensional.notMem_iff_infDist_pos
    ⟨u 0, AffineSubspace.self_mem_mk' _ _⟩).mp hx

end PosteriorReplicas
end

end OAI
end

section
-- module Solutions.OAIQW_PosteriorReplicas.Geometry_DensityBinEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma ae_expectedDensity_le_inverse_oai {d k m : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    ∀ᵐ u : Tuple d m ∂Measure.pi (fun _ => (sphereLaw d).withDensity f),
      expectedDensity (k := k) f u ≤ ∫⁻ x, ENNReal.ofReal ((tupleDistance u x)⁻¹^k)
        ∂(sphereLaw d).withDensity f := by
  let : NeZero d := ⟨by omega⟩
  have : IsProbabilityMeasure (sphereLaw d) := by
    change IsProbabilityMeasure (BaseLaw.spherical.measure d); infer_instance
  have := bounded_withDensity_finite (sphereLaw d) hLt hfL
  have h := (equalLabelVersions d k m hk hm (by omega) .spherical f hf ⟨L,hLt,hfL⟩).2.2.2.2
  filter_upwards [h] with u hu
  have hu' : LinearIndependent ℝ (differences u) := hu.1
  have he : (fun A : Rows d k => residualRows u A) =
      fun A i => (differenceSpan u)ᗮ.starProjection (A i) := by
    funext A i
    exact kernelComponent_eq_starProjection hu' _
  have hv : (fun A : Rows d k => projectedDensity .spherical f A (labels A (u 0))) =ᵐ[constrainedRows k u]
      (fun A => ballDensityVersion ((sphereLaw d).withDensity f) A (labels A (u 0))) := by
    filter_upwards [hu.2] with A hA
    exact hA.2.2.2.2.2.1
  rw [constrainedRows_eq_residualRows hu'] at hv
  have hv' := (ae_map_iff (show Measurable (residualRows u) by fun_prop).aemeasurable
    (measurableSet_eq_fun (by unfold labels; fun_prop) (by unfold labels; fun_prop))).mp hv
  unfold expectedDensity
  rw [lintegral_congr_ae hv']
  simp_rw [he]
  apply expected_ballDensityVersion_le _ _ _
  filter_upwards [tupleDistance_pos_ae (by omega) (by omega) u f] with x hx
  exact norm_ne_zero_iff.mp (ne_of_gt hx)

end PosteriorReplicas
end

end OAI
end

theorem solution : type_of% @OAI.PosteriorReplicas.ae_expectedDensity_le_inverse_oai := @OAI.PosteriorReplicas.ae_expectedDensity_le_inverse_oai
