-- Prove2me | solution 1 for MinRankRecovery.Recovery.nuclear_norm_recovery
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-16T22:53:16.67935+00:00
-- url     : https://prove2.me/submissions/55ae4f77-6fc3-4abf-9df4-1ca18bd89b44

-- Licensed under Apache 2.0. Full exact deterministic nuclear-norm recovery theorem.
import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst


noncomputable section

namespace MinRankRecoveryResearch

open HighDimStat.MatrixRank
open scoped RealInnerProductSpace

variable {m n : ℕ}

def matrixVector (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin m × Fin n) := WithLp.toLp 2 (fun ij => A ij.1 ij.2)

theorem frobenius_eq_norm (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A = ‖matrixVector A‖ := by
  simp [frobeniusNorm, matrixVector, EuclideanSpace.norm_eq, Fintype.sum_prod_type]

theorem traceInner_eq_inner (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A B = ⟪matrixVector A, matrixVector B⟫ := by
  simp [traceInner, matrixVector, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fintype.sum_prod_type, mul_comm]

theorem frobenius_nonneg (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobeniusNorm A :=
  Real.sqrt_nonneg _

theorem frobenius_sq (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ^ 2 = traceInner A A := by
  rw [frobenius_eq_norm, traceInner_eq_inner, real_inner_self_eq_norm_sq]

theorem frobenius_eq_zero_iff (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A = 0 ↔ A = 0 := by
  rw [frobenius_eq_norm, norm_eq_zero]
  constructor
  · intro h
    ext i j
    exact congrArg (fun x : EuclideanSpace ℝ (Fin m × Fin n) => x (i, j)) h
  · rintro rfl
    rfl

theorem frobenius_add_le (A B : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (A + B) ≤ frobeniusNorm A + frobeniusNorm B := by
  have h : matrixVector (A+B) = matrixVector A + matrixVector B := by
    ext i; simp [matrixVector]
  simpa only [frobenius_eq_norm, h] using norm_add_le (matrixVector A) (matrixVector B)

theorem frobenius_neg (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (-A) = frobeniusNorm A := by
  have h : matrixVector (-A) = -matrixVector A := by
    ext i; simp [matrixVector]
  simpa only [frobenius_eq_norm, h] using norm_neg (matrixVector A)

theorem traceInner_add_left (A B C : Matrix (Fin m) (Fin n) ℝ) :
    traceInner (A+B) C = traceInner A C + traceInner B C := by
  simp [traceInner, add_mul, Finset.sum_add_distrib]

theorem traceInner_add_right (A B C : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A (B+C) = traceInner A B + traceInner A C := by
  simp [traceInner, mul_add, Finset.sum_add_distrib]

theorem traceInner_comm (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A B = traceInner B A := by
  simp [traceInner, mul_comm]

theorem traceInner_le_frobenius (A B : Matrix (Fin m) (Fin n) ℝ) :
    |traceInner A B| ≤ frobeniusNorm A * frobeniusNorm B := by
  rw [traceInner_eq_inner, frobenius_eq_norm, frobenius_eq_norm]
  exact abs_real_inner_le_norm _ _

theorem matrix_rank_eq (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank = Module.finrank ℝ (Matrix.toEuclideanLin A).range := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact A.rank_eq_finrank_range_toLin _ _

theorem matrix_pairing_basis (A B : Matrix (Fin m) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    traceInner A B = ∑ i, ⟪Matrix.toEuclideanLin A (b i),
      Matrix.toEuclideanLin B (b i)⟫ := by
  have ht : (A.transpose * B).trace = traceInner A B := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.transpose_apply, traceInner]
    exact Finset.sum_comm
  have hm : (Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin B =
      Matrix.toEuclideanLin (A.transpose * B) := by
    rw [Matrix.toLpLin_mul_same]
    congr 1
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  have htr := LinearMap.trace_eq_sum_inner
    ((Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin B) b
  have he : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (Matrix.toEuclideanLin (A.transpose * B)) = (A.transpose * B).trace := by
    change LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (A.transpose * B)) = _
    exact Matrix.trace_toLin_eq _ _
  have hl : LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      ((Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin B) = traceInner A B := by
    rw [hm, he, ht]
  rw [hl] at htr
  simpa only [LinearMap.comp_apply, LinearMap.adjoint_inner_right] using htr

theorem matrix_rank_add_le (A B : Matrix (Fin m) (Fin n) ℝ) :
    (A+B).rank ≤ A.rank+B.rank := by
  rw [matrix_rank_eq, matrix_rank_eq A, matrix_rank_eq B]
  have he : Matrix.toEuclideanLin (A+B) = Matrix.toEuclideanLin A + Matrix.toEuclideanLin B := map_add _ _ _
  rw [he]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

end MinRankRecoveryResearch

end


noncomputable section
namespace MinRankRecoveryResearch
open Matrix Module

variable {m n : ℕ}

def columnProjection (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.toEuclideanLin.symm (Matrix.toEuclideanLin A).range.starProjection.toLinearMap

theorem columnProjection_map (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.toEuclideanLin (columnProjection A) =
      (Matrix.toEuclideanLin A).range.starProjection.toLinearMap := by
  simp [columnProjection]

theorem columnProjection_mul_self (A : Matrix (Fin m) (Fin n) ℝ) :
    columnProjection A * A = A := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, columnProjection_map]
  apply LinearMap.ext
  intro x
  exact (LinearMap.range (Matrix.toEuclideanLin A)).starProjection_eq_self_iff.mpr
    (LinearMap.mem_range_self _ x)

theorem columnProjection_transpose (A : Matrix (Fin m) (Fin n) ℝ) :
    (columnProjection A).transpose = columnProjection A := by
  apply Matrix.toEuclideanLin.injective
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (columnProjection A)
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [h, columnProjection_map]
  exact (LinearMap.range (Matrix.toEuclideanLin A)).starProjection_isSymmetric.adjoint_eq

theorem columnProjection_idempotent (A : Matrix (Fin m) (Fin n) ℝ) :
    columnProjection A * columnProjection A = columnProjection A := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, columnProjection_map]
  apply LinearMap.ext
  intro x
  exact (LinearMap.range (Matrix.toEuclideanLin A)).starProjection_eq_self_iff.mpr
    (by exact (LinearMap.range (Matrix.toEuclideanLin A)).starProjection_apply_mem x)

theorem columnProjection_rank (A : Matrix (Fin m) (Fin n) ℝ) :
    (columnProjection A).rank = A.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin (columnProjection A)
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis,
    Matrix.rank_eq_finrank_range_toLin A
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  change finrank ℝ (Matrix.toEuclideanLin (columnProjection A)).range = _
  rw [columnProjection_map, Submodule.range_starProjection]
  rfl

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank Matrix MinRankRecovery.Recovery
variable {m n : ℕ}

def normalPart (A R : Matrix (Fin m) (Fin n) ℝ) :=
  (1 - columnProjection A) * R * (1 - columnProjection A.transpose)

def tangentPart (A R : Matrix (Fin m) (Fin n) ℝ) :=
  columnProjection A * R + (1 - columnProjection A) * R * columnProjection A.transpose

theorem tangent_normal_sum (A R : Matrix (Fin m) (Fin n) ℝ) :
    tangentPart A R + normalPart A R = R := by
  unfold tangentPart normalPart
  rw [add_assoc, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one,
    Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]

theorem tangent_rank (A R : Matrix (Fin m) (Fin n) ℝ) :
    (tangentPart A R).rank ≤ 2 * A.rank := by
  unfold tangentPart
  calc
    _ ≤ (columnProjection A * R).rank +
        ((1-columnProjection A)*R*columnProjection A.transpose).rank := matrix_rank_add_le _ _
    _ ≤ (columnProjection A).rank + (columnProjection A.transpose).rank :=
      Nat.add_le_add (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
    _ = 2*A.rank := by rw [columnProjection_rank, columnProjection_rank, Matrix.rank_transpose]; omega

theorem normal_left_annihilator (A R : Matrix (Fin m) (Fin n) ℝ) :
    columnProjection A * normalPart A R = 0 := by
  have h : columnProjection A * (1 - columnProjection A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, columnProjection_idempotent, sub_self]
  simp only [normalPart, ← Matrix.mul_assoc, h, Matrix.zero_mul]

theorem normal_right_annihilator (A R : Matrix (Fin m) (Fin n) ℝ) :
    normalPart A R * columnProjection A.transpose = 0 := by
  have h : (1 - columnProjection A.transpose) * columnProjection A.transpose = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, columnProjection_idempotent, sub_self]
  simp only [normalPart, Matrix.mul_assoc, h, Matrix.mul_zero]


theorem transpose_mul_columnProjection (A : Matrix (Fin m) (Fin n) ℝ) :
    A.transpose * columnProjection A = A.transpose := by
  have h := congrArg Matrix.transpose (columnProjection_mul_self A)
  simpa only [Matrix.transpose_mul, columnProjection_transpose] using h

theorem normal_orthogonal_left (A R : Matrix (Fin m) (Fin n) ℝ) :
    A.transpose * normalPart A R = 0 := by
  have h : A.transpose * (1 - columnProjection A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, transpose_mul_columnProjection, sub_self]
  simp only [normalPart, ← Matrix.mul_assoc, h, Matrix.zero_mul]

theorem normal_orthogonal_right (A R : Matrix (Fin m) (Fin n) ℝ) :
    normalPart A R * A.transpose = 0 := by
  have h : (1 - columnProjection A.transpose) * A.transpose = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, columnProjection_mul_self, sub_self]
  simp only [normalPart, Matrix.mul_assoc, h, Matrix.mul_zero]

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank Matrix MinRankRecovery.Recovery
variable {m n : ℕ}

theorem traceInner_eq_trace (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner A B = (A.transpose * B).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, traceInner]
  exact Finset.sum_comm

theorem traceInner_mul_left (P : Matrix (Fin m) (Fin m) ℝ)
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner (P*A) B = traceInner A (P.transpose*B) := by
  simp only [traceInner_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc]

theorem traceInner_mul_right (Q : Matrix (Fin n) (Fin n) ℝ)
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    traceInner (A*Q) B = traceInner A (B*Q.transpose) := by
  simp only [traceInner_eq_trace, Matrix.transpose_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm Q.transpose, Matrix.mul_assoc]

theorem tangent_orthogonal_supported (A R B : Matrix (Fin m) (Fin n) ℝ)
    (hL : columnProjection A * B = 0)
    (hR : B * columnProjection A.transpose = 0) :
    traceInner (tangentPart A R) B = 0 := by
  unfold tangentPart
  rw [traceInner_add_left, traceInner_mul_left, columnProjection_transpose, hL,
    traceInner_mul_right, columnProjection_transpose, hR]
  simp [traceInner]

theorem frobenius_add_sq_of_orthogonal (A B : Matrix (Fin m) (Fin n) ℝ)
    (h : traceInner A B = 0) :
    frobeniusNorm (A+B)^2 = frobeniusNorm A^2 + frobeniusNorm B^2 := by
  simp only [frobenius_sq, traceInner_add_left, traceInner_add_right]
  rw [traceInner_comm B A, h]
  ring

theorem frobenius_le_add_of_orthogonal (A B : Matrix (Fin m) (Fin n) ℝ)
    (h : traceInner A B = 0) : frobeniusNorm A ≤ frobeniusNorm (A+B) := by
  apply (sq_le_sq₀ (frobenius_nonneg _) (frobenius_nonneg _)).mp
  rw [frobenius_add_sq_of_orthogonal _ _ h]
  exact le_add_of_nonneg_right (sq_nonneg _)

end MinRankRecoveryResearch
end


noncomputable section

namespace MinRankRecoveryResearch

open HighDimStat.MatrixRank
open scoped RealInnerProductSpace

variable {m n : ℕ}

def singularBasis (A : Matrix (Fin m) (Fin n) ℝ) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  ((Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.posSemidef_conjTranspose_mul_self A).1).eigenvectorBasis
      (by simp)).reindex (finCongr (Fintype.card_fin n))

def singularImage (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin m) := Matrix.toEuclideanLin A (singularBasis A i)

def singularAtom (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    Matrix (Fin m) (Fin n) ℝ := fun a b => singularImage A i a * singularBasis A i b

def singularPart (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin n)) :
    Matrix (Fin m) (Fin n) ℝ := ∑ i ∈ s, singularAtom A i

theorem singular_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    0 ≤ singularValues A i := Real.sqrt_nonneg _

theorem singular_antitone (A : Matrix (Fin m) (Fin n) ℝ) :
    Antitone (singularValues A) := by
  intro i j hij
  apply Real.sqrt_le_sqrt
  exact (Matrix.posSemidef_conjTranspose_mul_self A).1.eigenvalues₀_antitone hij

theorem singularBasis_gram (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    (Matrix.toEuclideanLin A).adjoint (singularImage A i) =
      (singularValues A i)^2 • singularBasis A i := by
  have h := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.posSemidef_conjTranspose_mul_self A).1).apply_eigenvectorBasis
      (by simp) ((finCongr (Fintype.card_fin n)).symm i)
  have hp := (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))))
      ((finCongr (Fintype.card_fin n)).symm i))
  simp only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] at hp
  simp only [singularValues, Real.sq_sqrt hp, singularBasis,
    OrthonormalBasis.reindex_apply, singularImage]
  rw [← LinearMap.comp_apply, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← Matrix.toLpLin_mul_same]
  exact h

theorem singularImage_inner (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin n) :
    ⟪singularImage A i, singularImage A j⟫ =
      if i = j then (singularValues A i)^2 else 0 := by
  rw [singularImage, ← LinearMap.adjoint_inner_right, singularBasis_gram,
    real_inner_smul_right]
  rw [(singularBasis A).inner_eq_ite]
  split_ifs with h
  · subst j; ring
  · ring

theorem singularImage_norm (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    ‖singularImage A i‖ = singularValues A i := by
  have h := singularImage_inner A i i
  simp only [real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (singular_nonneg A i)).mp h

theorem singularAtom_apply (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (singularAtom A i) x =
      ⟪singularBasis A i, x⟫ • singularImage A i := by
  ext a
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, singularAtom,
    EuclideanSpace.inner_eq_star_dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem singularPart_apply_basis (A : Matrix (Fin m) (Fin n) ℝ)
    (s : Finset (Fin n)) (j : Fin n) :
    Matrix.toEuclideanLin (singularPart A s) (singularBasis A j) =
      if j ∈ s then singularImage A j else 0 := by
  simp only [singularPart, map_sum, LinearMap.sum_apply, singularAtom_apply,
    (singularBasis A).inner_eq_ite]
  simp

theorem singularPart_univ (A : Matrix (Fin m) (Fin n) ℝ) :
    singularPart A Finset.univ = A := by
  apply Matrix.toEuclideanLin.injective
  apply (singularBasis A).toBasis.ext
  intro i
  simpa [singularImage] using singularPart_apply_basis A Finset.univ i

theorem frobenius_singularPart_sq (A : Matrix (Fin m) (Fin n) ℝ)
    (s : Finset (Fin n)) :
    frobeniusNorm (singularPart A s)^2 = ∑ i ∈ s, (singularValues A i)^2 := by
  rw [frobenius_sq, matrix_pairing_basis _ _ (singularBasis A)]
  simp only [singularPart_apply_basis, real_inner_self_eq_norm_sq]
  simp [apply_ite (fun x : EuclideanSpace ℝ (Fin m) => ‖x‖), singularImage_norm]

theorem frobenius_singular_sq (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ^ 2 = ∑ i, (singularValues A i)^2 := by
  simpa only [singularPart_univ] using frobenius_singularPart_sq A Finset.univ

end MinRankRecoveryResearch

end


noncomputable section

namespace MinRankRecoveryResearch

open HighDimStat.MatrixRank
open scoped RealInnerProductSpace

variable {m n : ℕ}

theorem nuclear_nonneg (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ nuclearNorm A :=
  Finset.sum_nonneg fun i _ => singular_nonneg A i

theorem positive_singular_card_le_rank (A : Matrix (Fin m) (Fin n) ℝ) :
    (Finset.univ.filter fun i : Fin n => singularValues A i ≠ 0).card ≤ A.rank := by
  classical
  let s := Finset.univ.filter fun i : Fin n => singularValues A i ≠ 0
  have hli : LinearIndependent ℝ (fun i : s => singularImage A i.1) := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i h
      have hi := (Finset.mem_filter.mp i.2).2
      apply hi
      rw [← singularImage_norm, h, norm_zero]
    · intro i j hij
      rw [singularImage_inner, if_neg (fun h => hij (Subtype.ext h))]
  have hsub : Submodule.span ℝ (Set.range (fun i : s => singularImage A i.1)) ≤
      (Matrix.toEuclideanLin A).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨singularBasis A i.1, rfl⟩
  have h := Submodule.finrank_mono hsub
  rw [finrank_span_eq_card hli] at h
  simpa only [Fintype.card_coe, ← matrix_rank_eq] using h

theorem nuclear_le_sqrt_rank (A : Matrix (Fin m) (Fin n) ℝ) {r : ℕ}
    (hr : A.rank ≤ r) : nuclearNorm A ≤ Real.sqrt r * frobeniusNorm A := by
  classical
  let s := Finset.univ.filter fun i : Fin n => singularValues A i ≠ 0
  have hs : s.card ≤ r := (positive_singular_card_le_rank A).trans hr
  have hn : ∑ i ∈ s, singularValues A i = nuclearNorm A := by
    simp only [s, nuclearNorm, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : singularValues A i = 0 <;> simp [hi]
  have hf : ∑ i ∈ s, singularValues A i ^ 2 = frobeniusNorm A ^ 2 := by
    rw [frobenius_singular_sq]
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : singularValues A i = 0 <;> simp [hi]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => singularValues A i) (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hn, hf] at hc
  have hs' : (s.card : ℝ) ≤ r := by exact_mod_cast hs
  have hsq : (nuclearNorm A)^2 ≤ (Real.sqrt r * frobeniusNorm A)^2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    nlinarith [sq_nonneg (frobeniusNorm A)]
  exact (sq_le_sq₀ (nuclear_nonneg A) (mul_nonneg (Real.sqrt_nonneg _) (frobenius_nonneg A))).mp hsq

theorem frobenius_le_nuclear (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ≤ nuclearNorm A := by
  apply (sq_le_sq₀ (frobenius_nonneg A) (nuclear_nonneg A)).mp
  rw [frobenius_singular_sq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => singular_nonneg A i

theorem nuclear_eq_zero_iff (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    apply (frobenius_eq_zero_iff A).mp
    exact le_antisymm (h ▸ frobenius_le_nuclear A) (frobenius_nonneg A)
  · rintro rfl
    have h := nuclear_le_sqrt_rank (0 : Matrix (Fin m) (Fin n) ℝ) (r := 0) (by simp)
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul] at h
    exact le_antisymm h (nuclear_nonneg _)

theorem nuclear_neg (A : Matrix (Fin m) (Fin n) ℝ) : nuclearNorm (-A) = nuclearNorm A := by
  simp [nuclearNorm, singularValues]

end MinRankRecoveryResearch

end


noncomputable section

namespace MinRankRecoveryResearch

open HighDimStat.MatrixRank
open scoped RealInnerProductSpace

variable {m n : ℕ}

def MatrixContraction (Z : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), ‖Matrix.toEuclideanLin Z x‖ ≤ ‖x‖

def polarImage (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin m) := (singularValues A i)⁻¹ • singularImage A i

def polarMatrix (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.toEuclideanLin.symm ((singularBasis A).toBasis.constr ℝ (polarImage A))

theorem polar_apply_basis (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    Matrix.toEuclideanLin (polarMatrix A) (singularBasis A i) = polarImage A i := by
  simp [polarMatrix]

theorem polar_expansion (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (polarMatrix A) x =
      ∑ i, ⟪singularBasis A i, x⟫ • polarImage A i := by
  nth_rw 1 [← (singularBasis A).sum_repr' x]
  simp [polar_apply_basis]

theorem polarImage_norm_le (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    ‖polarImage A i‖ ≤ 1 := by
  rw [polarImage, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (singular_nonneg A i), singularImage_norm]
  by_cases h : singularValues A i = 0
  · simp [h]
  · simp [h]

theorem orthogonal_sum_norm_sq {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ι → E)
    (ho : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) :
    ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  calc
    ∑ j, ⟪v i, v j⟫ = ⟪v i, v i⟫ := by
      apply Finset.sum_eq_single i
      · intro j _ hji; exact ho i j hji.symm
      · simp
    _ = ‖v i‖^2 := real_inner_self_eq_norm_sq _

theorem polar_contraction (A : Matrix (Fin m) (Fin n) ℝ) :
    MatrixContraction (polarMatrix A) := by
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [polar_expansion, orthogonal_sum_norm_sq]
  · rw [← (singularBasis A).sum_sq_inner_right x]
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hsq : ‖polarImage A i‖ ^ 2 ≤ 1 := by
      have h := (sq_le_sq₀ (norm_nonneg (polarImage A i)) (by norm_num : (0:ℝ) ≤ 1)).2
        (polarImage_norm_le A i)
      simpa only [one_pow] using h
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hsq (sq_nonneg ⟪singularBasis A i, x⟫)
  · intro i j hij
    simp [polarImage, inner_smul_left, inner_smul_right, singularImage_inner, hij]

theorem contraction_pairing_le (Z A : Matrix (Fin m) (Fin n) ℝ)
    (hZ : MatrixContraction Z) : traceInner Z A ≤ nuclearNorm A := by
  rw [matrix_pairing_basis Z A (singularBasis A)]
  apply Finset.sum_le_sum
  intro i _
  calc
    ⟪Matrix.toEuclideanLin Z (singularBasis A i), Matrix.toEuclideanLin A (singularBasis A i)⟫
      ≤ ‖Matrix.toEuclideanLin Z (singularBasis A i)‖ * ‖singularImage A i‖ :=
        real_inner_le_norm _ _
    _ ≤ 1 * singularValues A i := by
      rw [singularImage_norm]
      apply mul_le_mul_of_nonneg_right _ (singular_nonneg A i)
      simpa only [(singularBasis A).orthonormal.1 i] using hZ (singularBasis A i)
    _ = singularValues A i := one_mul _

theorem polar_pairing (A : Matrix (Fin m) (Fin n) ℝ) :
    traceInner (polarMatrix A) A = nuclearNorm A := by
  rw [matrix_pairing_basis _ _ (singularBasis A)]
  apply Finset.sum_congr rfl
  intro i _
  rw [polar_apply_basis]
  change ⟪(singularValues A i)⁻¹ • singularImage A i, singularImage A i⟫ = _
  rw [real_inner_smul_left, singularImage_inner, if_pos rfl]
  by_cases h : singularValues A i = 0
  · simp [h]
  · field_simp

end MinRankRecoveryResearch

end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank
open scoped RealInnerProductSpace
variable {m n k : ℕ}

theorem singularImage_zero_of_singular_zero (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) (h : singularValues A i = 0) : singularImage A i = 0 := by
  apply norm_eq_zero.mp
  rw [singularImage_norm, h]

theorem singularAtom_apply_eq_zero_of_apply_eq_zero (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n))
    (hx : Matrix.toEuclideanLin A x = 0) :
    Matrix.toEuclideanLin (singularAtom A i) x = 0 := by
  rw [singularAtom_apply]
  by_cases hi : singularValues A i = 0
  · rw [singularImage_zero_of_singular_zero A i hi, smul_zero]
  · have h : (singularValues A i)^2 * ⟪singularBasis A i, x⟫ = 0 := by
      rw [← real_inner_smul_left, ← singularBasis_gram,
        LinearMap.adjoint_inner_left, hx, inner_zero_right]
    have hc : ⟪singularBasis A i, x⟫ = 0 := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hi)
    rw [hc, zero_smul]

theorem singularAtom_mul_eq_zero (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (h : A * Q = 0) (i : Fin n) :
    singularAtom A i * Q = 0 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, map_zero]
  apply LinearMap.ext
  intro x
  apply singularAtom_apply_eq_zero_of_apply_eq_zero
  have he := congrArg (fun M => Matrix.toEuclideanLin M x) h
  simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply, map_zero,
    LinearMap.zero_apply] using he

theorem mul_singularAtom_eq_zero (P : Matrix (Fin k) (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (h : P * A = 0) (i : Fin n) :
    P * singularAtom A i = 0 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, map_zero]
  apply LinearMap.ext
  intro x
  change Matrix.toEuclideanLin P (Matrix.toEuclideanLin (singularAtom A i) x) = 0
  rw [singularAtom_apply, map_smul]
  have he := congrArg (fun M => Matrix.toEuclideanLin M (singularBasis A i)) h
  have hz : Matrix.toEuclideanLin P (singularImage A i) = 0 := by
    simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply, map_zero,
      LinearMap.zero_apply, singularImage] using he
  rw [hz, smul_zero]

theorem singularPart_mul_eq_zero (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (h : A * Q = 0) (s : Finset (Fin n)) :
    singularPart A s * Q = 0 := by
  simp only [singularPart, Matrix.sum_mul, singularAtom_mul_eq_zero A Q h,
    Finset.sum_const_zero]

theorem mul_singularPart_eq_zero (P : Matrix (Fin k) (Fin m) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (h : P * A = 0) (s : Finset (Fin n)) :
    P * singularPart A s = 0 := by
  simp only [singularPart, Matrix.mul_sum, mul_singularAtom_eq_zero P A h,
    Finset.sum_const_zero]

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank
open scoped RealInnerProductSpace
variable {m n : ℕ}

theorem nuclear_add_le (A B : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm (A+B) ≤ nuclearNorm A + nuclearNorm B := by
  rw [← polar_pairing (A+B), traceInner_add_right]
  exact add_le_add (contraction_pairing_le _ _ (polar_contraction (A+B)))
    (contraction_pairing_le _ _ (polar_contraction (A+B)))

theorem nuclear_sum_le {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, nuclearNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact le_of_eq ((nuclear_eq_zero_iff _).mpr rfl)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (nuclear_add_le _ _).trans (add_le_add (le_refl _) ih)

theorem singularAtom_rank_le (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    (singularAtom A i).rank ≤ 1 :=
  Matrix.rank_vecMulVec_le _ _

theorem singularPart_rank_le (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin n)) :
    (singularPart A s).rank ≤ s.card := by
  classical
  unfold singularPart
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    exact (matrix_rank_add_le _ _).trans
      (by have h := singularAtom_rank_le A i; omega)

theorem singularAtom_frobenius (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    frobeniusNorm (singularAtom A i) = singularValues A i := by
  have h := frobenius_singularPart_sq A {i}
  simp only [singularPart, Finset.sum_singleton] at h
  exact (sq_eq_sq₀ (frobenius_nonneg _) (singular_nonneg A i)).mp h

theorem singularAtom_nuclear_le (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) :
    nuclearNorm (singularAtom A i) ≤ singularValues A i := by
  have h := nuclear_le_sqrt_rank (singularAtom A i) (singularAtom_rank_le A i)
  simpa [singularAtom_frobenius] using h

theorem polar_pairing_part (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin n)) :
    traceInner (polarMatrix A) (singularPart A s) = ∑ i ∈ s, singularValues A i := by
  classical
  rw [matrix_pairing_basis _ _ (singularBasis A)]
  simp only [polar_apply_basis, singularPart_apply_basis]
  trans ∑ i, if i ∈ s then singularValues A i else 0
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · change ⟪(singularValues A i)⁻¹ • singularImage A i, singularImage A i⟫ = _
      rw [real_inner_smul_left, singularImage_inner, if_pos rfl]
      by_cases h : singularValues A i = 0
      · simp [h]
      · field_simp
    · simp
  · simp

theorem singularPart_nuclear (A : Matrix (Fin m) (Fin n) ℝ) (s : Finset (Fin n)) :
    nuclearNorm (singularPart A s) = ∑ i ∈ s, singularValues A i := by
  apply le_antisymm
  · exact (nuclear_sum_le s (singularAtom A)).trans
      (Finset.sum_le_sum fun i _ => singularAtom_nuclear_le A i)
  · rw [← polar_pairing_part A s]
    exact contraction_pairing_le _ _ (polar_contraction A)

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank
open scoped RealInnerProductSpace
variable {m n : ℕ}

theorem polar_apply_mem_range (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (polarMatrix A) x ∈ (Matrix.toEuclideanLin A).range := by
  rw [polar_expansion]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact LinearMap.mem_range_self _ _

theorem polar_apply_zero_of_apply_zero (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : Matrix.toEuclideanLin A x = 0) :
    Matrix.toEuclideanLin (polarMatrix A) x = 0 := by
  rw [polar_expansion]
  apply Finset.sum_eq_zero
  intro i _
  have h := singularAtom_apply_eq_zero_of_apply_eq_zero A i x hx
  rw [singularAtom_apply] at h
  change ⟪singularBasis A i, x⟫ • ((singularValues A i)⁻¹ • singularImage A i) = 0
  rw [smul_comm, h, smul_zero]

theorem contraction_sum_of_split {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (U V : E →ₗ[ℝ] F) (S : Submodule ℝ E)
    (hU : ∀ x, ‖U x‖ ≤ ‖x‖) (hV : ∀ x, ‖V x‖ ≤ ‖x‖)
    (hUS : ∀ x ∈ S, U x = 0) (hVS : ∀ x ∈ Sᗮ, V x = 0)
    (hUV : ∀ x y, ⟪U x, V y⟫ = 0) (x : E) :
    ‖U x + V x‖ ≤ ‖x‖ := by
  have hsum := S.starProjection_add_starProjection_orthogonal x
  have hu : U x = U (Sᗮ.starProjection x) := by
    nth_rw 1 [← hsum]
    rw [map_add, hUS _ (S.starProjection_apply_mem x), zero_add]
  have hv : V x = V (S.starProjection x) := by
    nth_rw 1 [← hsum]
    rw [map_add, hVS _ (Sᗮ.starProjection_apply_mem x), add_zero]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_add_sq_real, hUV, mul_zero, add_zero, hu, hv,
    Submodule.norm_sq_eq_add_norm_sq_starProjection x S]
  have h1 := sq_le_sq₀ (norm_nonneg (U (Sᗮ.starProjection x)))
    (norm_nonneg (Sᗮ.starProjection x)) |>.2 (hU _)
  have h2 := sq_le_sq₀ (norm_nonneg (V (S.starProjection x)))
    (norm_nonneg (S.starProjection x)) |>.2 (hV _)
  linarith


theorem euclidean_adjoint_eq_transpose (A : Matrix (Fin m) (Fin n) ℝ) :
    (Matrix.toEuclideanLin A).adjoint = Matrix.toEuclideanLin A.transpose := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm

theorem image_inner_eq_zero_of_transpose_mul (A B : Matrix (Fin m) (Fin n) ℝ)
    (h : A.transpose * B = 0) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪Matrix.toEuclideanLin A x, Matrix.toEuclideanLin B y⟫ = 0 := by
  rw [← LinearMap.adjoint_inner_right, euclidean_adjoint_eq_transpose,
    ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, h, map_zero,
    LinearMap.zero_apply, inner_zero_right]

theorem polar_sum_contraction (A B : Matrix (Fin m) (Fin n) ℝ)
    (hAB : A.transpose * B = 0) (hBA : B * A.transpose = 0) :
    MatrixContraction (polarMatrix A + polarMatrix B) := by
  intro x
  simp only [map_add, LinearMap.add_apply]
  apply contraction_sum_of_split _ _ (Matrix.toEuclideanLin A).ker
    (polar_contraction A) (polar_contraction B)
  · intro y hy
    exact polar_apply_zero_of_apply_zero A y hy
  · intro y hy
    rw [LinearMap.orthogonal_ker] at hy
    obtain ⟨z, rfl⟩ := hy
    apply polar_apply_zero_of_apply_zero
    rw [euclidean_adjoint_eq_transpose, ← LinearMap.comp_apply,
      ← Matrix.toLpLin_mul_same, hBA, map_zero, LinearMap.zero_apply]
  · intro y z
    obtain ⟨u, hu⟩ := polar_apply_mem_range A y
    obtain ⟨v, hv⟩ := polar_apply_mem_range B z
    rw [← hu, ← hv]
    exact image_inner_eq_zero_of_transpose_mul A B hAB u v


end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank
open scoped RealInnerProductSpace
variable {m n : ℕ}

theorem polar_pairing_eq_zero (A B : Matrix (Fin m) (Fin n) ℝ)
    (h : A.transpose * B = 0) : traceInner (polarMatrix A) B = 0 := by
  rw [matrix_pairing_basis _ _ (singularBasis B)]
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨x, hx⟩ := polar_apply_mem_range A (singularBasis B i)
  rw [← hx]
  exact image_inner_eq_zero_of_transpose_mul A B h x (singularBasis B i)

theorem nuclear_add_of_orthogonal (A B : Matrix (Fin m) (Fin n) ℝ)
    (hAB : A.transpose * B = 0) (hABt : A * B.transpose = 0) :
    nuclearNorm (A+B) = nuclearNorm A + nuclearNorm B := by
  have hBA : B * A.transpose = 0 := by
    have h := congrArg Matrix.transpose hABt
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hBAt : B.transpose * A = 0 := by
    have h := congrArg Matrix.transpose hAB
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  apply le_antisymm (nuclear_add_le A B)
  have h := contraction_pairing_le (polarMatrix A + polarMatrix B) (A+B)
    (polar_sum_contraction A B hAB hBA)
  simpa only [traceInner_add_left, traceInner_add_right, polar_pairing,
    polar_pairing_eq_zero A B hAB, polar_pairing_eq_zero B A hBAt,
    add_zero, zero_add] using h

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open Finset

def blockMass (a : ℕ → ℝ) (q j : ℕ) : ℝ := ∑ i ∈ range q, a (q*j+i)
def blockSize (a : ℕ → ℝ) (q j : ℕ) : ℝ := Real.sqrt (∑ i ∈ range q, a (q*j+i)^2)

theorem block_entry_le_average (a : ℕ → ℝ) (ha : Antitone a)
    (q j i : ℕ) (hq : 0 < q) :
    a (q*(j+1)+i) ≤ blockMass a q j / q := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hq)).mpr
  calc
    a (q*(j+1)+i) * q = ∑ l ∈ range q, a (q*(j+1)+i) := by simp [mul_comm]
    _ ≤ blockMass a q j := by
      apply sum_le_sum
      intro l hl
      apply ha
      have := mem_range.mp hl
      simp only [Nat.mul_add, Nat.mul_one]
      omega

theorem block_size_le_previous (a : ℕ → ℝ) (ha : Antitone a)
    (hn : ∀ i, 0 ≤ a i) (q j : ℕ) (hq : 0 < q) :
    blockSize a q (j+1) ≤ blockMass a q j / Real.sqrt q := by
  have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hm : 0 ≤ blockMass a q j := sum_nonneg (fun i _ => hn _)
  have hs : 0 < Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hqr
  have he : ∀ i, a (q*(j+1)+i)^2 ≤ (blockMass a q j / q)^2 := by
    intro i
    exact pow_le_pow_left₀ (hn _) (block_entry_le_average a ha q j i hq) 2
  have hb : (∑ i ∈ range q, a (q*(j+1)+i)^2) ≤
      q * (blockMass a q j / q)^2 := by
    calc
      _ ≤ ∑ _i ∈ range q, (blockMass a q j / q)^2 := sum_le_sum (fun i _ => he i)
      _ = _ := by simp
  unfold blockSize
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hh : q * (blockMass a q j / q)^2 = (blockMass a q j / Real.sqrt q)^2 := by
      simp only [div_pow, Real.sq_sqrt hqr.le]
      field_simp
    exact hb.trans_eq hh


theorem sum_blocks {E : Type*} [AddCommMonoid E] (a : ℕ → E) (q N : ℕ) :
    (∑ j ∈ range N, ∑ i ∈ range q, a (q*j+i)) = ∑ i ∈ range (q*N), a i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.mul_succ, sum_range_add]

theorem block_tail_bound (a : ℕ → ℝ) (ha : Antitone a)
    (hn : ∀ i, 0 ≤ a i) (q N : ℕ) (hq : 0 < q) :
    (∑ j ∈ range N, blockSize a q (j+1)) ≤
      (∑ i ∈ range (q*N), a i) / Real.sqrt q := by
  calc
    _ ≤ ∑ j ∈ range N, blockMass a q j / Real.sqrt q :=
      sum_le_sum (fun j _ => block_size_le_previous a ha hn q j hq)
    _ = _ := by rw [← sum_div]; congr 1; exact sum_blocks a q N

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open Finset

variable {n : ℕ}
def zeroExtend {E : Type*} [Zero E] (f : Fin n → E) (k : ℕ) : E :=
  if h : k < n then f ⟨k,h⟩ else 0

def blockIndices (n q j : ℕ) : Finset (Fin n) :=
  univ.filter fun i => q*j ≤ i.val ∧ i.val < q*j+q

theorem sum_blockIndices {E : Type*} [AddCommMonoid E] (f : Fin n → E) (q j : ℕ) :
    (∑ i ∈ blockIndices n q j, f i) = ∑ k ∈ range q, zeroExtend f (q*j+k) := by
  classical
  apply sum_bij_ne_zero (fun i _ _ => i.val-q*j)
  · intro i hi _
    have hi' := (mem_filter.mp hi).2
    exact mem_range.mpr (by omega)
  · intro a ha _ b hb _ he
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    apply Fin.ext
    omega
  · intro k hk hne
    have hk' := mem_range.mp hk
    have hlt : q*j+k < n := by
      by_contra h
      simp [zeroExtend, h] at hne
    refine ⟨⟨q*j+k,hlt⟩, ?_, ?_, ?_⟩
    · simp only [blockIndices, mem_filter, mem_univ, true_and]
      omega
    · simpa [zeroExtend, hlt] using hne
    · simp
  · intro i hi _
    have hi' := (mem_filter.mp hi).2
    have he : q*j+(i.val-q*j) = i.val := by omega
    simp [he, zeroExtend]

theorem card_blockIndices_le (q j : ℕ) : (blockIndices n q j).card ≤ q := by
  classical
  have h := sum_blockIndices (n:=n) (fun _ => (1:ℕ)) q j
  calc
    _ = ∑ k ∈ range q, zeroExtend (fun _ : Fin n => (1:ℕ)) (q*j+k) := by simpa using h
    _ ≤ ∑ _k ∈ range q, (1:ℕ) := by
      apply sum_le_sum
      intro k _
      simp only [zeroExtend]
      split_ifs <;> omega
    _ = q := by simp

theorem zeroExtend_nonneg (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∀ k, 0 ≤ zeroExtend a k := by
  intro k
  unfold zeroExtend
  split_ifs
  · exact ha _
  · exact le_rfl

theorem zeroExtend_antitone (a : Fin n → ℝ) (ha : Antitone a)
    (hn : ∀ i, 0 ≤ a i) : Antitone (zeroExtend a) := by
  intro i j hij
  by_cases hi : i < n
  · by_cases hj : j < n
    · simpa only [zeroExtend, dif_pos hi, dif_pos hj] using ha (show (⟨i,hi⟩ : Fin n) ≤ ⟨j,hj⟩ from hij)
    · simpa only [zeroExtend, dif_pos hi, dif_neg hj] using hn ⟨i,hi⟩
  · have hj : ¬ j < n := by omega
    simp [zeroExtend, hi, hj]

theorem sum_zeroExtend_range {E : Type*} [AddCommMonoid E]
    (f : Fin n → E) (N : ℕ) (hN : n ≤ N) :
    (∑ k ∈ range N, zeroExtend f k) = ∑ i, f i := by
  classical
  symm
  apply sum_bij_ne_zero (fun i _ _ => i.val)
  · intro i _ _
    exact mem_range.mpr (i.isLt.trans_le hN)
  · intro a _ _ b _ _ he
    exact Fin.ext he
  · intro k hk hne
    have hlt : k < n := by
      by_contra h
      simp [zeroExtend, h] at hne
    refine ⟨⟨k,hlt⟩, mem_univ _, ?_, rfl⟩
    simpa [zeroExtend, hlt] using hne
  · intro i _ _
    simp [zeroExtend]

theorem sum_blocks_partition {E : Type*} [AddCommMonoid E]
    (f : Fin n → E) (q N : ℕ) (hN : n ≤ q*N) :
    (∑ j ∈ range N, ∑ i ∈ blockIndices n q j, f i) = ∑ i, f i := by
  simp_rw [sum_blockIndices]
  rw [sum_blocks, sum_zeroExtend_range f (q*N) hN]

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank Finset
variable {m n : ℕ}

def spectralBlock (A : Matrix (Fin m) (Fin n) ℝ) (q j : ℕ) :=
  singularPart A (blockIndices n q j)

theorem spectralBlock_rank (A : Matrix (Fin m) (Fin n) ℝ) (q j : ℕ) :
    (spectralBlock A q j).rank ≤ q :=
  (singularPart_rank_le A _).trans (card_blockIndices_le q j)

theorem spectralBlock_frobenius (A : Matrix (Fin m) (Fin n) ℝ) (q j : ℕ) :
    frobeniusNorm (spectralBlock A q j) = blockSize (zeroExtend (singularValues A)) q j := by
  unfold blockSize
  apply (sq_eq_sq₀ (frobenius_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [spectralBlock, frobenius_singularPart_sq,
    Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _), sum_blockIndices]
  apply sum_congr rfl
  intro k _
  unfold zeroExtend
  split_ifs <;> simp

theorem spectralBlocks_sum (A : Matrix (Fin m) (Fin n) ℝ) (q N : ℕ)
    (hN : n ≤ q*N) : ∑ j ∈ range N, spectralBlock A q j = A := by
  have h := sum_blocks_partition (singularAtom A) q N hN
  change (∑ j ∈ range N, spectralBlock A q j) = singularPart A univ at h
  rwa [singularPart_univ] at h

theorem spectralBlocks_tail (A : Matrix (Fin m) (Fin n) ℝ) (q : ℕ) (hq : 0 < q) :
    (∑ j ∈ range n, frobeniusNorm (spectralBlock A q (j+1))) ≤ nuclearNorm A / Real.sqrt q := by
  simp_rw [spectralBlock_frobenius]
  have h := block_tail_bound (zeroExtend (singularValues A))
    (zeroExtend_antitone _ (singular_antitone A) (singular_nonneg A))
    (zeroExtend_nonneg _ (singular_nonneg A)) q n hq
  have hn : n ≤ q*n := by nlinarith
  simpa only [sum_zeroExtend_range _ _ hn, nuclearNorm] using h

theorem tangent_orthogonal_block (A R : Matrix (Fin m) (Fin n) ℝ) (q j : ℕ) :
    traceInner (tangentPart A R) (spectralBlock (normalPart A R) q j) = 0 := by
  apply tangent_orthogonal_supported
  · exact mul_singularPart_eq_zero _ _ (normal_left_annihilator A R) _
  · exact singularPart_mul_eq_zero _ _ (normal_right_annihilator A R) _

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank MinRankRecovery.Recovery
variable {m n p : ℕ}

def measurementVector (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (observationOp Xs A)

theorem measNorm_eq_norm (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : measNorm Xs A = ‖measurementVector Xs A‖ := by
  simp [measNorm, measurementVector, EuclideanSpace.norm_eq]

theorem measNorm_nonneg (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ measNorm Xs A := Real.sqrt_nonneg _

theorem measNorm_add_le (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ)
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    measNorm Xs (A+B) ≤ measNorm Xs A + measNorm Xs B := by
  have h : measurementVector Xs (A+B) = measurementVector Xs A + measurementVector Xs B := by
    ext i
    exact traceInner_add_right _ _ _
  simpa only [measNorm_eq_norm, h] using norm_add_le (measurementVector Xs A) (measurementVector Xs B)

theorem measNorm_neg (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : measNorm Xs (-A) = measNorm Xs A := by
  have h : measurementVector Xs (-A) = -measurementVector Xs A := by
    ext i
    simp [measurementVector, observationOp, traceInner, Finset.sum_neg_distrib]
  rw [measNorm_eq_norm, h, norm_neg, ← measNorm_eq_norm]

theorem measNorm_upper (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    measNorm Xs A ≤ (∑ i, frobeniusNorm (Xs i)) * frobeniusNorm A := by
  rw [measNorm_eq_norm]
  calc
    _ ≤ ∑ i, ‖measurementVector Xs A i‖ := by
      rw [EuclideanSpace.norm_eq]
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · simpa only [Real.norm_eq_abs, sq_abs] using
          Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
            (fun i _ => abs_nonneg (measurementVector Xs A i))
    _ ≤ ∑ i, frobeniusNorm (Xs i) * frobeniusNorm A := by
      apply Finset.sum_le_sum
      intro i _
      exact traceInner_le_frobenius _ _
    _ = _ := (Finset.sum_mul ..).symm

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank MinRankRecovery.Recovery
variable {m n p : ℕ}

theorem rip_admissible_nonempty (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ) :
    {δ : ℝ | 0 ≤ δ ∧ ∀ A : Matrix (Fin m) (Fin n) ℝ, A.rank ≤ r →
      (1-δ)*frobeniusNorm A ≤ measNorm Xs A ∧
      measNorm Xs A ≤ (1+δ)*frobeniusNorm A}.Nonempty := by
  refine ⟨1 + ∑ i, frobeniusNorm (Xs i), ?_, ?_⟩
  · exact add_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => frobenius_nonneg _)
  · intro A _
    have hc : 0 ≤ ∑ i, frobeniusNorm (Xs i) := Finset.sum_nonneg (fun _ _ => frobenius_nonneg _)
    have hf := frobenius_nonneg A
    have hm := measNorm_nonneg Xs A
    have hu := measNorm_upper Xs A
    constructor <;> nlinarith

theorem rip_actual_witness (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ)
    (h : ripConst Xs r < 1/10) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1/10 ∧
      ∀ A : Matrix (Fin m) (Fin n) ℝ, A.rank ≤ r →
      (1-δ)*frobeniusNorm A ≤ measNorm Xs A ∧
      measNorm Xs A ≤ (1+δ)*frobeniusNorm A := by
  obtain ⟨δ, hδ, hlt⟩ := (csInf_lt_iff (show BddBelow {δ : ℝ | 0 ≤ δ ∧
    ∀ A : Matrix (Fin m) (Fin n) ℝ, A.rank ≤ r →
      (1-δ)*frobeniusNorm A ≤ measNorm Xs A ∧
      measNorm Xs A ≤ (1+δ)*frobeniusNorm A} from ⟨0, fun _ ha => ha.1⟩)
      (rip_admissible_nonempty Xs r)).mp h
  exact ⟨δ, hδ.1, hlt, hδ.2⟩

end MinRankRecoveryResearch
end


noncomputable section
namespace MinRankRecoveryResearch
open HighDimStat.MatrixRank MinRankRecovery.Recovery Finset
variable {m n p : ℕ}

theorem measNorm_sum_le {ι : Type*} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ)
    (s : Finset ι) (f : ι → Matrix (Fin m) (Fin n) ℝ) :
    measNorm Xs (∑ i ∈ s, f i) ≤ ∑ i ∈ s, measNorm Xs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [measNorm, observationOp, traceInner]
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    exact (measNorm_add_le Xs _ _).trans (add_le_add (le_refl _) ih)

theorem observation_sub_eq_zero (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ)
    (X A : Matrix (Fin m) (Fin n) ℝ) (h : observationOp Xs X = observationOp Xs A) :
    observationOp Xs (X-A) = 0 := by
  ext i
  have hi := congrFun h i
  simp only [observationOp, traceInner] at hi ⊢
  simp only [Matrix.sub_apply, mul_sub, sum_sub_distrib, Pi.zero_apply]
  exact sub_eq_zero.mpr hi

theorem cone_condition (A X : Matrix (Fin m) (Fin n) ℝ)
    (h : nuclearNorm X ≤ nuclearNorm A) :
    nuclearNorm (normalPart A (X-A)) ≤ nuclearNorm (tangentPart A (X-A)) := by
  let T := tangentPart A (X-A)
  let N := normalPart A (X-A)
  have hs : T+N = X-A := tangent_normal_sum _ _
  have ho1 : A.transpose*N = 0 := normal_orthogonal_left _ _
  have ho2 : A*N.transpose = 0 := by
    have hh := congrArg Matrix.transpose (normal_orthogonal_right A (X-A))
    simpa using hh
  have he : A+N = X + -T := by
    have : X = A+(T+N) := by rw [hs]; abel
    rw [this]; abel
  have hb := nuclear_add_le X (-T)
  rw [← he, nuclear_add_of_orthogonal A N ho1 ho2, nuclear_neg] at hb
  change nuclearNorm N ≤ nuclearNorm T
  linarith

theorem sqrt_ratio_bound (r : ℕ) : Real.sqrt (2*r:ℝ) ≤ (9/11:ℝ)*Real.sqrt (3*r:ℝ) := by
  have h2 : 0 ≤ (2*r:ℝ) := by positivity
  have h3 : 0 ≤ (3*r:ℝ) := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt h2, Real.sq_sqrt h3]
  nlinarith [Nat.cast_nonneg (α:=ℝ) r]

theorem native_recovery (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ)
    (hr : 1 ≤ r) (hδ : ripConst Xs (5*r) < 1/10) (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A.rank ≤ r) (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : observationOp Xs X = observationOp Xs A) (hnuc : nuclearNorm X ≤ nuclearNorm A) :
    X = A := by
  obtain ⟨δ, hδ0, hδlt, hRIP⟩ := rip_actual_witness Xs (5*r) hδ
  let R := X-A
  let T := tangentPart A R
  let N := normalPart A R
  let B := spectralBlock N (3*r)
  have hq : 0 < 3*r := by omega
  have hT : T.rank ≤ 2*r := (tangent_rank A R).trans (Nat.mul_le_mul_left 2 hA)
  have hcone : nuclearNorm N ≤ nuclearNorm T := cone_condition A X hnuc
  have htail : (∑ j ∈ range n, frobeniusNorm (B (j+1))) ≤ (9/11:ℝ)*frobeniusNorm T := by
    have h1 := spectralBlocks_tail N (3*r) hq
    have h2 := nuclear_le_sqrt_rank T hT
    have hs : 0 < Real.sqrt (3*r:ℝ) := Real.sqrt_pos.mpr (by positivity)
    have h3 := sqrt_ratio_bound r
    have hf := frobenius_nonneg T
    have h4 : nuclearNorm N / Real.sqrt (3*r:ℝ) ≤ (9/11:ℝ)*frobeniusNorm T := by
      apply (div_le_iff₀ hs).mpr
      have ht : nuclearNorm N ≤ Real.sqrt (2*r:ℝ)*frobeniusNorm T := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcone.trans h2
      nlinarith [mul_le_mul_of_nonneg_right h3 hf]
    exact h1.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using h4)
  have hfirst : (T+B 0).rank ≤ 5*r := by
    have hb := spectralBlock_rank N (3*r) 0
    exact (matrix_rank_add_le T (B 0)).trans (by dsimp [B] at *; omega)
  have hF : frobeniusNorm T ≤ frobeniusNorm (T+B 0) :=
    frobenius_le_add_of_orthogonal _ _ (tangent_orthogonal_block A R (3*r) 0)
  have hsum : B 0 + ∑ j ∈ range n, B (j+1) = N := by
    have hh := spectralBlocks_sum N (3*r) (n+1) (by nlinarith)
    simpa only [sum_range_succ', add_comm] using hh
  have hmeas : measNorm Xs (T+B 0) = measNorm Xs (∑ j ∈ range n, B (j+1)) := by
    have hz := observation_sub_eq_zero Xs X A hX
    have he : T+B 0 + ∑ j ∈ range n, B (j+1) = R := by
      rw [add_assoc, hsum]
      exact tangent_normal_sum A R
    have hv : measurementVector Xs (T+B 0) = -measurementVector Xs (∑ j ∈ range n, B (j+1)) := by
      ext i
      have hh := congrFun hz i
      change traceInner (Xs i) (T+B 0) = -traceInner (Xs i) (∑ j ∈ range n, B (j+1))
      have hzero : traceInner (Xs i) R = 0 := hh
      rw [← he, traceInner_add_right] at hzero
      linarith
    rw [measNorm_eq_norm, hv, norm_neg, ← measNorm_eq_norm]
  have hupper : measNorm Xs (∑ j ∈ range n, B (j+1)) ≤
      (1+δ)*(∑ j ∈ range n, frobeniusNorm (B (j+1))) := by
    apply (measNorm_sum_le Xs (range n) (fun j => B (j+1))).trans
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    exact (hRIP _ ((spectralBlock_rank N (3*r) (j+1)).trans (by omega))).2
  have hlower := (hRIP (T+B 0) hfirst).1
  have hδ1 : 0 ≤ 1-δ := by linarith
  have hδp : 0 ≤ 1+δ := by linarith
  have hchain : (1-δ)*frobeniusNorm T ≤ (1+δ)*((9/11:ℝ)*frobeniusNorm T) := by
    calc
      _ ≤ (1-δ)*frobeniusNorm (T+B 0) := mul_le_mul_of_nonneg_left hF hδ1
      _ ≤ measNorm Xs (T+B 0) := hlower
      _ = measNorm Xs (∑ j ∈ range n, B (j+1)) := hmeas
      _ ≤ (1+δ)*(∑ j ∈ range n, frobeniusNorm (B (j+1))) := hupper
      _ ≤ _ := mul_le_mul_of_nonneg_left htail hδp
  have hfzero : frobeniusNorm T = 0 := by
    have hf := frobenius_nonneg T
    nlinarith
  have htzero : T = 0 := (frobenius_eq_zero_iff T).mp hfzero
  have hnzero : N = 0 := by
    apply (nuclear_eq_zero_iff N).mp
    have ht : nuclearNorm T = 0 := (nuclear_eq_zero_iff T).mpr htzero
    exact le_antisymm (ht ▸ hcone) (nuclear_nonneg N)
  have hs := tangent_normal_sum A R
  change T+N = R at hs
  rw [htzero, hnzero, add_zero] at hs
  exact sub_eq_zero.mp hs.symm

end MinRankRecoveryResearch
end


open HighDimStat.MatrixRank Matrix MinRankRecovery.Recovery

namespace MinRankRecovery.Recovery

/-- Theorem 3.3, p. 12: if `r ≥ 1` and `δ_5r < 1/10`, then for every `X₀` of rank at most `r`,
`X₀` is the unique minimizer of `‖X‖_*` subject to `𝒜(X) = 𝒜(X₀)`: every feasible `X` with
`‖X‖_* ≤ ‖X₀‖_*` equals `X₀`. -/
theorem nuclear_norm_recovery {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ)
    (hr : 1 ≤ r) (hδ : ripConst Xs (5 * r) < 1 / 10) (X0 : Matrix (Fin m) (Fin n) ℝ)
    (hX0 : X0.rank ≤ r) :
    ∀ X : Matrix (Fin m) (Fin n) ℝ, observationOp Xs X = observationOp Xs X0 →
      nuclearNorm X ≤ nuclearNorm X0 → X = X0 := by
  intro X hobs hn
  exact MinRankRecoveryResearch.native_recovery Xs r hr hδ X0 hX0 X hobs hn

end MinRankRecovery.Recovery

theorem solution {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ)
    (hr : 1 ≤ r) (hδ : ripConst Xs (5 * r) < 1 / 10) (X0 : Matrix (Fin m) (Fin n) ℝ)
    (hX0 : X0.rank ≤ r) :
    ∀ X : Matrix (Fin m) (Fin n) ℝ, observationOp Xs X = observationOp Xs X0 →
      nuclearNorm X ≤ nuclearNorm X0 → X = X0 := MinRankRecovery.Recovery.nuclear_norm_recovery Xs r hr hδ X0 hX0
