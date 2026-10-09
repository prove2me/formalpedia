-- Prove2me | solution 1 for InputSparsity.Regress.fact_35
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T17:13:46.074103+00:00
-- url     : https://prove2.me/submissions/9bf96225-4b47-4f81-a682-4c2cb621b35d

import Mathlib
import Definitions.Def_InputSparsity_Regress_Basic

set_option autoImplicit false
namespace SketchedRegressionPenrose
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
noncomputable def leastNormInverse (f : E →ₗ[ℝ] F) : F →ₗ[ℝ] E :=
  f.kerᗮ.subtype.comp
    ((f.ker.quotientEquivOfIsCompl f.kerᗮ f.ker.isCompl_orthogonal).toLinearMap.comp
      (f.quotKerEquivRange.symm.toLinearMap.comp f.range.orthogonalProjectionOnto.toLinearMap))
lemma inverse_mem_orthogonal (f : E →ₗ[ℝ] F) (y : F) : leastNormInverse f y ∈ f.kerᗮ := by
  exact Subtype.coe_prop _
lemma forward_inverse (f : E →ₗ[ℝ] F) (y : F) :
    f (leastNormInverse f y) = f.range.starProjection y := by
  let q := f.quotKerEquivRange.symm (f.range.orthogonalProjectionOnto y)
  let z := f.ker.quotientEquivOfIsCompl f.kerᗮ f.ker.isCompl_orthogonal q
  change f (z : E) = f.range.starProjection y
  have hz : (Submodule.Quotient.mk (z : E) : E ⧸ f.ker) = q :=
    Submodule.mk_quotientEquivOfIsCompl_apply _ _
  calc
    _ = (f.quotKerEquivRange (Submodule.Quotient.mk (z : E)) : F) :=
      (f.quotKerEquivRange_apply_mk (z : E)).symm
    _ = (f.quotKerEquivRange q : F) := by rw [hz]
    _ = (f.range.orthogonalProjectionOnto y : F) := by simp only [q,LinearEquiv.apply_symm_apply]
    _ = _ := rfl
lemma inverse_forward (f : E →ₗ[ℝ] F) (x : E) :
    leastNormInverse f (f x) = f.kerᗮ.starProjection x := by
  apply Eq.symm
  apply f.kerᗮ.eq_starProjection_of_mem_orthogonal (inverse_mem_orthogonal f (f x))
  apply f.ker.le_orthogonal_orthogonal
  change f (x-leastNormInverse f (f x)) = 0
  rw [map_sub,forward_inverse,f.range.starProjection_eq_self_iff.mpr ⟨x,rfl⟩,sub_self]
lemma forward_inverse_forward (f : E →ₗ[ℝ] F) :
    f.comp ((leastNormInverse f).comp f) = f := by
  ext x
  change f (leastNormInverse f (f x)) = f x
  rw [forward_inverse,f.range.starProjection_eq_self_iff.mpr ⟨x,rfl⟩]
lemma inverse_forward_inverse (f : E →ₗ[ℝ] F) :
    (leastNormInverse f).comp (f.comp (leastNormInverse f)) = leastNormInverse f := by
  ext y
  change leastNormInverse f (f (leastNormInverse f y)) = leastNormInverse f y
  rw [inverse_forward,f.kerᗮ.starProjection_eq_self_iff.mpr (inverse_mem_orthogonal f y)]
lemma forward_inverse_symmetric (f : E →ₗ[ℝ] F) : (f.comp (leastNormInverse f)).IsSymmetric := by
  have he : f.comp (leastNormInverse f) = f.range.starProjection.toLinearMap := by
    ext y
    exact forward_inverse f y
  rw [he]
  exact f.range.starProjection_isSymmetric
lemma inverse_forward_symmetric (f : E →ₗ[ℝ] F) : ((leastNormInverse f).comp f).IsSymmetric := by
  have he : (leastNormInverse f).comp f = f.kerᗮ.starProjection.toLinearMap := by
    ext x
    exact inverse_forward f x
  rw [he]
  exact f.kerᗮ.starProjection_isSymmetric
end SketchedRegressionPenrose
#print axioms SketchedRegressionPenrose.inverse_mem_orthogonal
#print axioms SketchedRegressionPenrose.forward_inverse
#print axioms SketchedRegressionPenrose.inverse_forward
#print axioms SketchedRegressionPenrose.forward_inverse_forward
#print axioms SketchedRegressionPenrose.inverse_forward_inverse
#print axioms SketchedRegressionPenrose.forward_inverse_symmetric
#print axioms SketchedRegressionPenrose.inverse_forward_symmetric

set_option autoImplicit false
open Matrix InputSparsity.Regress SketchedRegressionPenrose
namespace SketchedRegressionMatrixPenrose
lemma euclideanLin_mul {n d k : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin k) ℝ) :
    Matrix.toEuclideanLin (A*B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  apply LinearMap.ext
  intro x
  change WithLp.toLp 2 ((A*B) *ᵥ WithLp.ofLp x) =
    WithLp.toLp 2 (A *ᵥ WithLp.ofLp (WithLp.toLp 2 (B *ᵥ WithLp.ofLp x)))
  rw [WithLp.ofLp_toLp,Matrix.mulVec_mulVec]
noncomputable def matrixInverse {n d : ℕ} (C : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin d) (Fin n) ℝ :=
  Matrix.toEuclideanLin.symm (leastNormInverse (Matrix.toEuclideanLin C))
lemma matrixInverse_map {n d : ℕ} (C : Matrix (Fin n) (Fin d) ℝ) :
    Matrix.toEuclideanLin (matrixInverse C) = leastNormInverse (Matrix.toEuclideanLin C) :=
  LinearEquiv.apply_symm_apply _ _
lemma matrixInverse_penrose {n d : ℕ} (C : Matrix (Fin n) (Fin d) ℝ) :
    IsMoorePenrose C (matrixInverse C) := by
  refine ⟨?_,?_,?_,?_⟩
  · apply Matrix.toEuclideanLin.injective
    simp only [euclideanLin_mul,matrixInverse_map,LinearMap.comp_assoc]
    exact forward_inverse_forward (Matrix.toEuclideanLin C)
  · apply Matrix.toEuclideanLin.injective
    simp only [euclideanLin_mul,matrixInverse_map,LinearMap.comp_assoc]
    exact inverse_forward_inverse (Matrix.toEuclideanLin C)
  · have hs : (Matrix.toEuclideanLin (C*matrixInverse C)).IsSymmetric := by
      rw [euclideanLin_mul,matrixInverse_map]
      exact forward_inverse_symmetric (Matrix.toEuclideanLin C)
    have hh := Matrix.isSymmetric_toEuclideanLin_iff.mp hs
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  · have hs : (Matrix.toEuclideanLin (matrixInverse C*C)).IsSymmetric := by
      rw [euclideanLin_mul,matrixInverse_map]
      exact inverse_forward_symmetric (Matrix.toEuclideanLin C)
    have hh := Matrix.isSymmetric_toEuclideanLin_iff.mp hs
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hh
lemma exists_penrose {n d : ℕ} (C : Matrix (Fin n) (Fin d) ℝ) :
    ∃ G : Matrix (Fin d) (Fin n) ℝ, IsMoorePenrose C G :=
  ⟨matrixInverse C,matrixInverse_penrose C⟩
end SketchedRegressionMatrixPenrose
#print axioms SketchedRegressionMatrixPenrose.euclideanLin_mul
#print axioms SketchedRegressionMatrixPenrose.matrixInverse_map
#print axioms SketchedRegressionMatrixPenrose.matrixInverse_penrose
#print axioms SketchedRegressionMatrixPenrose.exists_penrose

set_option autoImplicit false
open Matrix InputSparsity.Embed InputSparsity.Regress
namespace SketchedRegressionQuadratic
def pair {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, C i j * D i j
lemma pair_self {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) : pair C C = frobSq C := by
  simp only [pair,frobSq,pow_two]
lemma pair_comm {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) : pair C D = pair D C := by
  simp only [pair,mul_comm]
lemma frobSq_add_smul {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) (t : ℝ) :
    frobSq (C + t • D) = frobSq C + 2 * t * pair C D + t^2 * frobSq D := by
  unfold frobSq pair
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  calc
    _ = ∑ i, ∑ j, (C i j ^ 2 + (2*t)*(C i j*D i j) + t^2*D i j^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum]
lemma linear_coefficient_zero (a b : ℝ) (h : ∀ t : ℝ, 0 ≤ a*(t*t) + 2*b*t + 0) : b = 0 := by
  have hd := discrim_le_zero h
  simp only [discrim,mul_zero,sub_zero] at hd
  nlinarith [sq_nonneg b]
lemma minimizer_pair_zero {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (hX : IsLSMinimizer C D Xstar) (Z : Matrix (Fin d) (Fin m) ℝ) :
    pair (C * Xstar - D) (C * Z) = 0 := by
  apply linear_coefficient_zero (frobSq (C*Z))
  intro t
  have hh := hX (Xstar + t • Z)
  have he : C * (Xstar + t • Z) - D = (C*Xstar-D) + t • (C*Z) := by
    rw [Matrix.mul_add,Matrix.mul_smul]
    module
  rw [he,frobSq_add_smul] at hh
  nlinarith
lemma pair_mul_left {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (Z : Matrix (Fin d) (Fin m) ℝ) (R : Matrix (Fin n) (Fin m) ℝ) :
    pair (C*Z) R = pair Z (Cᵀ*R) := by
  unfold pair
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun (i : Fin n) (j : Fin m) => ∑ k, C i k * Z k j * R i j),
    Finset.sum_comm (f := fun (k : Fin d) (j : Fin m) => ∑ i, Z k j * (C i k * R i j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  ring
lemma frobSq_zero_iff {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) : frobSq C = 0 ↔ C = 0 := by
  constructor
  · intro h
    ext i j
    have hi : (∑ j, C i j ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _)).mp h i (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg (C i j))).mp hi j (Finset.mem_univ _)
    simpa only [Matrix.zero_apply] using (sq_eq_zero_iff.mp hij)
  · rintro rfl
    simp [frobSq]
lemma normal_equations {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (hX : IsLSMinimizer C D Xstar) : Cᵀ*(C*Xstar-D) = 0 := by
  apply (frobSq_zero_iff _).mp
  have hh := minimizer_pair_zero C D Xstar hX (Cᵀ*(C*Xstar-D))
  rw [pair_comm,pair_mul_left,pair_self] at hh
  exact hh
lemma frobSq_nonneg {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) : 0 ≤ frobSq C := by
  exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _
lemma residual_column_orthogonal {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (hX : IsLSMinimizer C D Xstar) (x : Fin d → ℝ) :
    (C *ᵥ x) ᵥ* (C*Xstar-D) = 0 := by
  rw [Matrix.vecMul_mulVec,normal_equations C D Xstar hX,Matrix.vecMul_zero]
lemma error_decomposition {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (hX : IsLSMinimizer C D Xstar) (X : Matrix (Fin d) (Fin m) ℝ) :
    frobSq (C*X-D) = frobSq (C*(X-Xstar)) + frobSq (C*Xstar-D) := by
  have he : C*X-D = (C*Xstar-D) + (1 : ℝ) • (C*(X-Xstar)) := by
    rw [Matrix.mul_sub,one_smul]
    module
  rw [he,frobSq_add_smul,minimizer_pair_zero C D Xstar hX (X-Xstar)]
  ring
lemma normal_equations_minimizer {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (Xstar : Matrix (Fin d) (Fin m) ℝ)
    (h : Cᵀ*(C*Xstar-D) = 0) : IsLSMinimizer C D Xstar := by
  intro X
  have hz : pair (C*Xstar-D) (C*(X-Xstar)) = 0 := by
    rw [pair_comm,pair_mul_left,h]
    simp [pair]
  have he : C*X-D = (C*Xstar-D) + (1 : ℝ) • (C*(X-Xstar)) := by
    rw [Matrix.mul_sub,one_smul]
    module
  rw [he,frobSq_add_smul,hz]
  nlinarith [frobSq_nonneg (C*(X-Xstar))]
lemma penrose_normal_equations {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (G : Matrix (Fin d) (Fin n) ℝ)
    (hG : IsMoorePenrose C G) : Cᵀ*(C*(G*D)-D) = 0 := by
  have hc : Cᵀ*(C*G) = Cᵀ := by
    have ht := congrArg Matrix.transpose hG.1
    rw [Matrix.transpose_mul,hG.2.2.1] at ht
    exact ht
  rw [Matrix.mul_sub,← Matrix.mul_assoc C G D,← Matrix.mul_assoc,hc,sub_self]
lemma penrose_minimizer {n d m : ℕ} (C : Matrix (Fin n) (Fin d) ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (G : Matrix (Fin d) (Fin n) ℝ)
    (hG : IsMoorePenrose C G) : IsLSMinimizer C D (G*D) :=
  normal_equations_minimizer C D (G*D) (penrose_normal_equations C D G hG)
end SketchedRegressionQuadratic
#print axioms SketchedRegressionQuadratic.pair_self
#print axioms SketchedRegressionQuadratic.pair_comm
#print axioms SketchedRegressionQuadratic.frobSq_add_smul
#print axioms SketchedRegressionQuadratic.linear_coefficient_zero
#print axioms SketchedRegressionQuadratic.minimizer_pair_zero
#print axioms SketchedRegressionQuadratic.pair_mul_left
#print axioms SketchedRegressionQuadratic.frobSq_zero_iff
#print axioms SketchedRegressionQuadratic.normal_equations
#print axioms SketchedRegressionQuadratic.frobSq_nonneg
#print axioms SketchedRegressionQuadratic.residual_column_orthogonal
#print axioms SketchedRegressionQuadratic.error_decomposition
#print axioms SketchedRegressionQuadratic.normal_equations_minimizer
#print axioms SketchedRegressionQuadratic.penrose_normal_equations
#print axioms SketchedRegressionQuadratic.penrose_minimizer

set_option autoImplicit false
open Matrix InputSparsity.Regress
theorem solution {n d d' : ℕ} (C : Matrix (Fin n) (Fin d) ℝ) (D : Matrix (Fin n) (Fin d') ℝ) :
    (∃ G : Matrix (Fin d) (Fin n) ℝ, IsMoorePenrose C G) ∧
    (∀ G : Matrix (Fin d) (Fin n) ℝ, IsMoorePenrose C G → IsLSMinimizer C D (G * D)) ∧
    (∀ Xstar : Matrix (Fin d) (Fin d') ℝ, IsLSMinimizer C D Xstar →
      Cᵀ * (C * Xstar - D) = 0 ∧
      (∀ x : Fin d → ℝ, (C *ᵥ x) ᵥ* (C * Xstar - D) = 0) ∧
      (∀ X : Matrix (Fin d) (Fin d') ℝ,
        InputSparsity.Embed.frobSq (C * X - D) = InputSparsity.Embed.frobSq (C * (X - Xstar)) + InputSparsity.Embed.frobSq (C * Xstar - D))) := by
  refine ⟨SketchedRegressionMatrixPenrose.exists_penrose C, ?_, ?_⟩
  · intro G hG
    exact SketchedRegressionQuadratic.penrose_minimizer C D G hG
  · intro Xstar hX
    exact ⟨SketchedRegressionQuadratic.normal_equations C D Xstar hX,
      fun x => SketchedRegressionQuadratic.residual_column_orthogonal C D Xstar hX x,
      fun X => SketchedRegressionQuadratic.error_decomposition C D Xstar hX X⟩

#print axioms solution
namespace InputSparsity.Regress
open Matrix

example {n d d' : ℕ} (C : Matrix (Fin n) (Fin d) ℝ) (D : Matrix (Fin n) (Fin d') ℝ) :
    (∃ G : Matrix (Fin d) (Fin n) ℝ, IsMoorePenrose C G) ∧
    (∀ G : Matrix (Fin d) (Fin n) ℝ, IsMoorePenrose C G → IsLSMinimizer C D (G * D)) ∧
    (∀ Xstar : Matrix (Fin d) (Fin d') ℝ, IsLSMinimizer C D Xstar →
      Cᵀ * (C * Xstar - D) = 0 ∧
      (∀ x : Fin d → ℝ, (C *ᵥ x) ᵥ* (C * Xstar - D) = 0) ∧
      (∀ X : Matrix (Fin d) (Fin d') ℝ,
        InputSparsity.Embed.frobSq (C * X - D) = InputSparsity.Embed.frobSq (C * (X - Xstar)) + InputSparsity.Embed.frobSq (C * Xstar - D))) := by
  exact solution C D

end InputSparsity.Regress

#print axioms solution
