-- Prove2me | solution 1 for IRLSM.RIP.proposition_6_8
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T03:21:03.206202+00:00
-- url     : https://prove2.me/submissions/36caa8f3-6eb2-482b-aa8e-e5f8c8ee33e5

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_IRLSM_Convergence_Basic

-- Module: IRLSMProof.MatrixBasics
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank IRLSM.Convergence

variable {n p m : ℕ}

theorem trace_symm (X Y : Matrix (Fin n) (Fin p) ℝ) : traceInner X Y = traceInner Y X := by
  simp only [traceInner, mul_comm]
theorem trace_add_left (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (X+Y) Z = traceInner X Z + traceInner Y Z := by
  simp only [traceInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
theorem trace_add_right (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner X (Y+Z) = traceInner X Y + traceInner X Z := by
  rw [trace_symm, trace_add_left, trace_symm Y X, trace_symm Z X]
theorem trace_smul_left (a : ℝ) (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (a • X) Y = a * traceInner X Y := by
  simp only [traceInner, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
theorem trace_smul_right (a : ℝ) (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner X (a • Y) = a * traceInner X Y := by
  rw [trace_symm, trace_smul_left, trace_symm]
@[simp] theorem trace_zero_left (X : Matrix (Fin n) (Fin p) ℝ) : traceInner 0 X = 0 := by simp [traceInner]
@[simp] theorem trace_zero_right (X : Matrix (Fin n) (Fin p) ℝ) : traceInner X 0 = 0 := by simp [traceInner]
theorem frob_nonneg (X : Matrix (Fin n) (Fin p) ℝ) : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
theorem frob_sq (X : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm X ^ 2 = ∑ i, ∑ j, X i j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
theorem trace_self (X : Matrix (Fin n) (Fin p) ℝ) : traceInner X X = frobeniusNorm X ^ 2 := by
  rw [frob_sq]; simp only [traceInner, pow_two]
theorem frob_eq_zero (X : Matrix (Fin n) (Fin p) ℝ) : frobeniusNorm X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hz : (∑ i, ∑ j, X i j ^ 2) = 0 := by rw [← frob_sq, h]; norm_num
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (X i j)))).mp hz
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (X i j))).mp (hi i (Finset.mem_univ i)) j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hj
  · rintro rfl; simp [frobeniusNorm]
theorem frob_add_sq (X Y : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm (X+Y)^2 = frobeniusNorm X^2 + 2*traceInner X Y + frobeniusNorm Y^2 := by
  rw [← trace_self, trace_add_left, trace_add_right, trace_add_right, trace_self, trace_self, trace_symm Y X]; ring
theorem frob_smul_sq (a : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm (a • X)^2 = a^2 * frobeniusNorm X^2 := by
  rw [← trace_self, trace_smul_left, trace_smul_right, trace_self]; ring
theorem obs_add (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (X Y : Matrix (Fin n) (Fin p) ℝ) :
    observationOp A (X+Y) = observationOp A X + observationOp A Y := by
  funext l; exact trace_add_right (A l) X Y
theorem obs_smul (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (a : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    observationOp A (a • X) = a • observationOp A X := by
  funext l; exact trace_smul_right a (A l) X
@[simp] theorem obs_zero (A : Fin m → Matrix (Fin n) (Fin p) ℝ) : observationOp A 0 = 0 := by
  funext l; exact trace_zero_right (A l)
theorem rank_add_le (X Y : Matrix (Fin n) (Fin p) ℝ) : (X+Y).rank ≤ X.rank + Y.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank, Matrix.mulVecLin_add]
  apply le_trans (Submodule.finrank_mono (show LinearMap.range (X.mulVecLin+Y.mulVecLin) ≤ LinearMap.range X.mulVecLin ⊔ LinearMap.range Y.mulVecLin from ?_))
  · exact Submodule.finrank_add_le_finrank_add_finrank _ _
  · rintro v ⟨u,rfl⟩
    exact Submodule.mem_sup.mpr ⟨_,⟨u,rfl⟩,_,⟨u,rfl⟩,rfl⟩
theorem rank_smul_le (a : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) : (a • X).rank ≤ X.rank := by
  by_cases ha : a = 0
  · simp [ha]
  · exact (Matrix.rank_smul_of_mem_nonZeroDivisors X (mem_nonZeroDivisors_of_ne_zero ha)).le

theorem trace_cauchy_sq (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner X Y ^ 2 ≤ frobeniusNorm X ^ 2 * frobeniusNorm Y ^ 2 := by
  simpa [traceInner, frob_sq, Fintype.sum_prod_type] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin p))
      (fun ij => X ij.1 ij.2) (fun ij => Y ij.1 ij.2))
theorem frob_smul (a : ℝ) (X : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm (a • X) = |a| * frobeniusNorm X := by
  have h := frob_smul_sq a X
  have h1 := frob_nonneg (a • X)
  have h2 := mul_nonneg (abs_nonneg a) (frob_nonneg X)
  nlinarith [sq_abs a]
theorem frob_pos_iff (X : Matrix (Fin n) (Fin p) ℝ) : 0 < frobeniusNorm X ↔ X ≠ 0 := by
  constructor
  · intro h hx
    exact (ne_of_gt h) ((frob_eq_zero X).mpr hx)
  · intro h
    exact lt_of_le_of_ne (frob_nonneg X) (Ne.symm ((frob_eq_zero X).not.mpr h))
theorem trace_sub_left (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (X-Y) Z = traceInner X Z - traceInner Y Z := by
  simp only [traceInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
theorem trace_sub_right (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    traceInner X (Y-Z) = traceInner X Y - traceInner X Z := by
  rw [trace_symm, trace_sub_left, trace_symm Y X, trace_symm Z X]
end IRLSMProof

-- Module: IRLSMProof.GramSpectrum
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank
variable {n p : ℕ}

noncomputable def eigenIndex (p : ℕ) : Fin p ≃ Fin p :=
  (finCongr (Fintype.card_fin p)).symm.trans (Fintype.equivOfCardEq (Fintype.card_fin _))
noncomputable def gramEigen (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin p) : ℝ :=
  (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues (eigenIndex p i)

theorem gramEigen_native (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin p) :
    gramEigen X i = (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues₀
      ((finCongr (Fintype.card_fin p)).symm i) := by
  simp [gramEigen, Matrix.IsHermitian.eigenvalues, eigenIndex]
theorem sv_eq_sqrt (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin p) :
    singularValues X i = Real.sqrt (gramEigen X i) := by
  rw [gramEigen_native]; rfl
theorem gramEigen_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin p) : 0 ≤ gramEigen X i :=
  (Matrix.posSemidef_conjTranspose_mul_self X).eigenvalues_nonneg _
theorem sv_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin p) : 0 ≤ singularValues X i := Real.sqrt_nonneg _
theorem sv_sq (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin p) : singularValues X i ^ 2 = gramEigen X i := by
  rw [sv_eq_sqrt, Real.sq_sqrt (gramEigen_nonneg X i)]
theorem sv_antitone (X : Matrix (Fin n) (Fin p) ℝ) : Antitone (singularValues X) := by
  intro i j hij
  rw [sv_eq_sqrt, sv_eq_sqrt, gramEigen_native, gramEigen_native]
  apply Real.sqrt_le_sqrt
  exact (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues₀_antitone hij

theorem gramEigen_sum (X : Matrix (Fin n) (Fin p) ℝ) :
    ∑ i, gramEigen X i = frobeniusNorm X ^ 2 := by
  have he : (∑ i, gramEigen X i) = ∑ i, (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues i :=
    Equiv.sum_comp (eigenIndex p) _
  have ht : Matrix.trace (Xᴴ * X) = ∑ i, (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues i := by
    simpa using (Matrix.posSemidef_conjTranspose_mul_self X).1.trace_eq_sum_eigenvalues
  rw [he, ← ht]
  rw [frob_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, pow_two]
  exact Finset.sum_comm

theorem sv_sq_sum (X : Matrix (Fin n) (Fin p) ℝ) :
    ∑ i, singularValues X i ^ 2 = frobeniusNorm X ^ 2 := by
  simp_rw [sv_sq]; exact gramEigen_sum X

theorem nuclear_nonneg (X : Matrix (Fin n) (Fin p) ℝ) : 0 ≤ nuclearNorm X :=
  Finset.sum_nonneg (fun i _ => sv_nonneg X i)
theorem nuclear_rank_bound (X : Matrix (Fin n) (Fin p) ℝ) :
    nuclearNorm X ≤ Real.sqrt (X.rank : ℝ) * frobeniusNorm X := by
  classical
  let ev := (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues
  let S : Finset (Fin p) := Finset.univ.filter (fun i => ev i ≠ 0)
  have hn : ∀ i, 0 ≤ ev i := (Matrix.posSemidef_conjTranspose_mul_self X).eigenvalues_nonneg
  have hcard : S.card = X.rank := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self X).1.rank_eq_card_non_zero_eigs
    rw [Matrix.rank_conjTranspose_mul_self] at h
    simpa only [Fintype.card_subtype, S, ev] using h.symm
  have hsum : (∑ i ∈ S, Real.sqrt (ev i)) = nuclearNorm X := by
    have he : (∑ i, Real.sqrt (ev i)) = nuclearNorm X := by
      unfold nuclearNorm
      simp_rw [sv_eq_sqrt]
      exact (Equiv.sum_comp (eigenIndex p) (fun i => Real.sqrt (ev i))).symm
    rw [← he]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : ev i = 0 := by simpa [S] using hi
    simp [hz]
  have hsquares : (∑ i ∈ S, Real.sqrt (ev i)^2) = frobeniusNorm X^2 := by
    simp_rw [Real.sq_sqrt (hn _)]
    have he : (∑ i, ev i) = frobeniusNorm X^2 := by
      rw [← gramEigen_sum X]
      exact (Equiv.sum_comp (eigenIndex p) ev).symm
    rw [← he]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa [S] using hi
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (ev i)) (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hsum, hsquares, hcard] at hcs
  have hr : Real.sqrt (X.rank : ℝ)^2 = (X.rank : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hnp := nuclear_nonneg X
  have hp := mul_nonneg (Real.sqrt_nonneg (X.rank:ℝ)) (frob_nonneg X)
  nlinarith [sq_nonneg (nuclearNorm X - Real.sqrt (X.rank:ℝ)*frobeniusNorm X)]

noncomputable def orderedBasis (X : Matrix (Fin n) (Fin p) ℝ) :
    OrthonormalBasis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)) :=
  (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvectorBasis.reindex (eigenIndex p).symm

theorem ordered_eigenvector (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin p) :
    (Xᴴ * X) *ᵥ (orderedBasis X i) = gramEigen X i • (orderedBasis X i : Fin p → ℝ) := by
  simpa only [orderedBasis, OrthonormalBasis.reindex_apply, Equiv.symm_symm, gramEigen] using
    (Matrix.posSemidef_conjTranspose_mul_self X).1.mulVec_eigenvectorBasis (eigenIndex p i)
end IRLSMProof

-- Module: IRLSMProof.SpectralProjection
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank
variable {n p : ℕ}
noncomputable def orderedUnitary (X : Matrix (Fin n) (Fin p) ℝ) : Matrix.unitaryGroup (Fin p) ℝ :=
  ⟨(EuclideanSpace.basisFun (Fin p) ℝ).toBasis.toMatrix (orderedBasis X).toBasis,
    (EuclideanSpace.basisFun (Fin p) ℝ).toMatrix_orthonormalBasis_mem_unitary (orderedBasis X)⟩
@[simp] theorem orderedUnitary_apply (X : Matrix (Fin n) (Fin p) ℝ) (i j : Fin p) :
    orderedUnitary X i j = (orderedBasis X j : Fin p → ℝ) i := rfl

theorem gram_mul_unitary (X : Matrix (Fin n) (Fin p) ℝ) :
    (Xᴴ * X) * (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ) =
      (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal (gramEigen X) := by
  ext i j
  have h := congrFun (ordered_eigenvector X j) i
  simp only [Matrix.mul_diagonal]
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, orderedUnitary_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h

theorem gram_diagonalization (X : Matrix (Fin n) (Fin p) ℝ) :
    Xᴴ * X = (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ) * Matrix.diagonal (gramEigen X) *
      star (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ) := by
  have h := congrArg (fun M : Matrix (Fin p) (Fin p) ℝ => M * star (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ)) (gram_mul_unitary X)
  have hu : (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ) * star (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ) = 1 := Unitary.coe_mul_star_self (orderedUnitary X)
  simpa only [Matrix.mul_assoc, hu, Matrix.mul_one] using h

noncomputable def coordinateProj (S : Finset (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.diagonal (fun i => if i ∈ S then 1 else 0)
noncomputable def spectralProj (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ) * coordinateProj S *
    star (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ)

theorem coordinateProj_sq (S : Finset (Fin p)) : coordinateProj S * coordinateProj S = coordinateProj S := by
  classical
  simp only [coordinateProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> norm_num

theorem spectralProj_sq (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    spectralProj X S * spectralProj X S = spectralProj X S := by
  let Q : Matrix (Fin p) (Fin p) ℝ := orderedUnitary X
  change (Q * coordinateProj S * star Q) * (Q * coordinateProj S * star Q) = Q * coordinateProj S * star Q
  calc
    _ = Q * coordinateProj S * (star Q * Q) * coordinateProj S * star Q := by noncomm_ring
    _ = Q * (coordinateProj S * coordinateProj S) * star Q := by
      rw [show star Q * Q = 1 from Unitary.coe_star_mul_self (orderedUnitary X)]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [coordinateProj_sq]

theorem spectralProj_star (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    star (spectralProj X S) = spectralProj X S := by
  have hd : star (coordinateProj S) = coordinateProj S := by
    change (coordinateProj S)ᴴ = coordinateProj S
    simp [coordinateProj]
  simp only [spectralProj, star_mul, star_star, hd, Matrix.mul_assoc]
end IRLSMProof

-- Module: IRLSMProof.SupportProjection
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank
variable {n p : ℕ}

theorem spectralProj_rank (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    (spectralProj X S).rank ≤ S.card := by
  classical
  have h := (Matrix.rank_mul_le_left ((orderedUnitary X : Matrix (Fin p) (Fin p) ℝ) * coordinateProj S)
    (star (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ))).trans
      (Matrix.rank_mul_le_right (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ) (coordinateProj S))
  have he : (coordinateProj S).rank = S.card := by
    rw [coordinateProj, Matrix.rank_diagonal]
    simp
  exact he ▸ h

noncomputable def gramSupport (X : Matrix (Fin n) (Fin p) ℝ) : Finset (Fin p) :=
  Finset.univ.filter (fun i => gramEigen X i ≠ 0)

theorem gramSupport_card (X : Matrix (Fin n) (Fin p) ℝ) : (gramSupport X).card = X.rank := by
  classical
  have h := (Matrix.posSemidef_conjTranspose_mul_self X).1.rank_eq_card_non_zero_eigs
  rw [Matrix.rank_conjTranspose_mul_self] at h
  have he := Equiv.sum_comp (eigenIndex p)
    (fun i => if (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues i ≠ 0 then (1:ℕ) else 0)
  simp only [Finset.sum_boole] at he
  have he' : (gramSupport X).card = Fintype.card {i // (Matrix.posSemidef_conjTranspose_mul_self X).1.eigenvalues i ≠ 0} := by
    simpa [gramSupport, gramEigen, Fintype.card_subtype] using he
  exact he'.trans h.symm

theorem gram_mul_support (X : Matrix (Fin n) (Fin p) ℝ) :
    (Xᴴ * X) * spectralProj X (gramSupport X) = Xᴴ * X := by
  classical
  let Q : Matrix (Fin p) (Fin p) ℝ := orderedUnitary X
  let D := coordinateProj (gramSupport X)
  have hD : Matrix.diagonal (gramEigen X) * D = Matrix.diagonal (gramEigen X) := by
    simp only [D, coordinateProj, Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    by_cases hi : gramEigen X i = 0 <;> simp [gramSupport, hi]
  rw [gram_diagonalization X]
  change (Q * Matrix.diagonal (gramEigen X) * star Q) * (Q * D * star Q) = Q * Matrix.diagonal (gramEigen X) * star Q
  calc
    _ = Q * Matrix.diagonal (gramEigen X) * (star Q * Q) * D * star Q := by noncomm_ring
    _ = Q * (Matrix.diagonal (gramEigen X) * D) * star Q := by
      rw [show star Q * Q = 1 from Unitary.coe_star_mul_self (orderedUnitary X)]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hD]

theorem mul_support_eq (X : Matrix (Fin n) (Fin p) ℝ) :
    X * spectralProj X (gramSupport X) = X := by
  have hg : (Xᴴ * X) * (1 - spectralProj X (gramSupport X)) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, gram_mul_support, sub_self]
  have hx := (Matrix.conjTranspose_mul_self_mul_eq_zero X (1-spectralProj X (gramSupport X))).mp hg
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hx
  exact hx.symm

theorem support_rank (X : Matrix (Fin n) (Fin p) ℝ) :
    (spectralProj X (gramSupport X)).rank ≤ X.rank := by
  simpa only [gramSupport_card] using spectralProj_rank X (gramSupport X)

theorem spectralProj_transpose (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    (spectralProj X S)ᵀ = spectralProj X S := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using spectralProj_star X S
end IRLSMProof

-- Module: IRLSMProof.TangentAlgebra
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank
variable {n p : ℕ}

theorem traceInner_eq_trace (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner X Y = Matrix.trace (Xᵀ * Y) := by
  simp only [traceInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem trace_mul_left (P : Matrix (Fin n) (Fin n) ℝ)
    (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (P*X) Y = traceInner X (Pᵀ*Y) := by
  rw [traceInner_eq_trace, traceInner_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc]

theorem trace_mul_right (Q : Matrix (Fin p) (Fin p) ℝ)
    (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner (X*Q) Y = traceInner X (Y*Qᵀ) := by
  rw [traceInner_eq_trace, traceInner_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc]

def tangentB (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin p) ℝ := (1-P)*X*(1-Q)
def tangentH (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin n) (Fin p) ℝ := X-tangentB P Q X

theorem tangent_sum (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) : X = tangentH P Q X + tangentB P Q X := by
  simp [tangentH]

theorem tangentH_expand (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) : tangentH P Q X = P*X+(1-P)*X*Q := by
  simp only [tangentH, tangentB, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  abel

theorem tangentB_left (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) (hP : P*P=P) : P*tangentB P Q X=0 := by
  have hz : P*(1-P)=0 := by rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
  rw [tangentB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.zero_mul]

theorem tangentB_right (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) (hQ : Q*Q=Q) : tangentB P Q X*Q=0 := by
  have hz : (1-Q)*Q=0 := by rw [Matrix.sub_mul, Matrix.one_mul, hQ, sub_self]
  rw [tangentB, Matrix.mul_assoc, hz, Matrix.mul_zero]

theorem tangent_trace_zero (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X Y : Matrix (Fin n) (Fin p) ℝ) (hPs : Pᵀ=P) (hQs : Qᵀ=Q)
    (hPY : P*Y=0) (hYQ : Y*Q=0) : traceInner (tangentH P Q X) Y=0 := by
  rw [tangentH_expand, trace_add_left, trace_mul_left, hPs, hPY, trace_zero_right,
    trace_mul_right, hQs, hYQ, trace_zero_right, add_zero]

theorem tangent_rank_bound (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (hP : P.rank≤k) (hQ : Q.rank≤k) :
    (tangentH P Q X).rank ≤ 2*k := by
  rw [tangentH_expand]
  have h1 := Matrix.rank_mul_le_left P X
  have h2 := Matrix.rank_mul_le_right ((1-P)*X) Q
  have h3 := rank_add_le (P*X) ((1-P)*X*Q)
  omega

theorem tangent_annihilations (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X X1 : Matrix (Fin n) (Fin p) ℝ) (hPs : Pᵀ=P) (hQs : Qᵀ=Q)
    (hP : P*P=P) (hQ : Q*Q=Q) (hPX : P*X1=X1) (hXQ : X1*Q=X1) :
    X1*(tangentB P Q X)ᵀ=0 ∧ X1ᵀ*tangentB P Q X=0 := by
  have hL := tangentB_left P Q X hP
  have hR := tangentB_right P Q X hQ
  have hRT : Q*(tangentB P Q X)ᵀ=0 := by
    have hh := congrArg Matrix.transpose hR
    simpa only [Matrix.transpose_mul, hQs, Matrix.transpose_zero] using hh
  have hXT : X1ᵀ*P=X1ᵀ := by
    have hh := congrArg Matrix.transpose hPX
    simpa only [Matrix.transpose_mul, hPs] using hh
  constructor
  · calc
      _ = (X1*Q)*(tangentB P Q X)ᵀ := by rw [hXQ]
      _ = 0 := by rw [Matrix.mul_assoc, hRT, Matrix.mul_zero]
  · calc
      _ = (X1ᵀ*P)*tangentB P Q X := by rw [hXT]
      _ = 0 := by rw [Matrix.mul_assoc, hL, Matrix.mul_zero]

theorem tangent_certificate (P : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin p) (Fin p) ℝ)
    (X X1 : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (hPs : Pᵀ=P) (hQs : Qᵀ=Q)
    (hP : P*P=P) (hQ : Q*Q=Q) (hrP : P.rank≤k) (hrQ : Q.rank≤k)
    (hPX : P*X1=X1) (hXQ : X1*Q=X1) :
    X=tangentH P Q X+tangentB P Q X ∧ (tangentH P Q X).rank≤2*k ∧
      P*tangentB P Q X=0 ∧ tangentB P Q X*Q=0 ∧
      X1*(tangentB P Q X)ᵀ=0 ∧ X1ᵀ*tangentB P Q X=0 ∧
      traceInner (tangentH P Q X) (tangentB P Q X)=0 := by
  have hL := tangentB_left P Q X hP
  have hR := tangentB_right P Q X hQ
  have ha := tangent_annihilations P Q X X1 hPs hQs hP hQ hPX hXQ
  exact ⟨tangent_sum P Q X, tangent_rank_bound P Q X k hrP hrQ, hL, hR, ha.1, ha.2,
    tangent_trace_zero P Q X _ hPs hQs hL hR⟩
end IRLSMProof

-- Module: IRLSMProof.SpectralAlgebra
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank
variable {n p : ℕ}

theorem proj_mul (X : Matrix (Fin n) (Fin p) ℝ) (S T : Finset (Fin p)) :
    spectralProj X S * spectralProj X T = spectralProj X (S ∩ T) := by
  classical
  have hd : coordinateProj S * coordinateProj T = coordinateProj (S ∩ T) := by
    simp only [coordinateProj, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp [hs,ht]
  let Q : Matrix (Fin p) (Fin p) ℝ := orderedUnitary X
  change (Q*coordinateProj S*star Q)*(Q*coordinateProj T*star Q)=Q*coordinateProj (S∩T)*star Q
  calc
    _ = Q*coordinateProj S*(star Q*Q)*coordinateProj T*star Q := by noncomm_ring
    _ = Q*(coordinateProj S*coordinateProj T)*star Q := by
      rw [show star Q*Q=1 from Unitary.coe_star_mul_self (orderedUnitary X)]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hd]

@[simp] theorem proj_empty (X : Matrix (Fin n) (Fin p) ℝ) : spectralProj X ∅ = 0 := by
  simp [spectralProj, coordinateProj]

theorem gram_proj_commute (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    (Xᴴ*X)*spectralProj X S = spectralProj X S*(Xᴴ*X) := by
  have hd : Matrix.diagonal (gramEigen X)*coordinateProj S = coordinateProj S*Matrix.diagonal (gramEigen X) := by
    simp only [coordinateProj, Matrix.diagonal_mul_diagonal]; congr 1; funext i; exact mul_comm _ _
  rw [gram_diagonalization X]
  let Q : Matrix (Fin p) (Fin p) ℝ := orderedUnitary X
  change (Q*diagonal (gramEigen X)*star Q)*(Q*coordinateProj S*star Q) = (Q*coordinateProj S*star Q)*(Q*diagonal (gramEigen X)*star Q)
  have hu : star Q*Q=1 := Unitary.coe_star_mul_self (orderedUnitary X)
  calc
    _ = Q*(diagonal (gramEigen X)*(star Q*Q)*coordinateProj S)*star Q := by noncomm_ring
    _ = Q*(coordinateProj S*(star Q*Q)*diagonal (gramEigen X))*star Q := by rw [hu]; simp only [mul_one]; rw [hd]
    _ = _ := by noncomm_ring

noncomputable def spectralBlock (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) := X * spectralProj X S

theorem block_rank (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    (spectralBlock X S).rank ≤ S.card :=
  (Matrix.rank_mul_le_right X (spectralProj X S)).trans (spectralProj_rank X S)

theorem block_left_zero (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p))
    (P : Matrix (Fin n) (Fin n) ℝ) (h : P*X=0) : P*spectralBlock X S=0 := by
  rw [spectralBlock, ← Matrix.mul_assoc, h, Matrix.zero_mul]
theorem block_right_zero (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p))
    (Q : Matrix (Fin p) (Fin p) ℝ) (h : X*Q=0) : spectralBlock X S*Q=0 := by
  have hg : (Xᴴ*X)*Q=0 := by rw [Matrix.mul_assoc,h,Matrix.mul_zero]
  have hp : (Xᴴ*X)*(spectralProj X S*Q)=0 := by
    rw [← Matrix.mul_assoc,gram_proj_commute,Matrix.mul_assoc,hg,Matrix.mul_zero]
  have hh := (Matrix.conjTranspose_mul_self_mul_eq_zero X (spectralProj X S*Q)).mp hp
  simpa only [spectralBlock,Matrix.mul_assoc] using hh

theorem blocks_orthogonal (X : Matrix (Fin n) (Fin p) ℝ) (S T : Finset (Fin p))
    (h : Disjoint S T) : traceInner (spectralBlock X S) (spectralBlock X T)=0 := by
  rw [spectralBlock,spectralBlock,trace_mul_right,spectralProj_transpose,Matrix.mul_assoc,proj_mul]
  rw [Finset.disjoint_iff_inter_eq_empty.mp h.symm,proj_empty,Matrix.mul_zero,trace_zero_right]

theorem trace_unitary_conj (X : Matrix (Fin n) (Fin p) ℝ) (M : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace ((orderedUnitary X : Matrix (Fin p) (Fin p) ℝ)*M*star (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ)) = Matrix.trace M := by
  rw [Matrix.trace_mul_comm,← Matrix.mul_assoc]
  rw [show star (orderedUnitary X : Matrix (Fin p) (Fin p) ℝ)*(orderedUnitary X : Matrix (Fin p) (Fin p) ℝ)=1 from Unitary.coe_star_mul_self (orderedUnitary X),Matrix.one_mul]

theorem block_energy (X : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    frobeniusNorm (spectralBlock X S)^2 = ∑ i ∈ S, singularValues X i^2 := by
  classical
  rw [← trace_self,spectralBlock,trace_mul_right,spectralProj_transpose,Matrix.mul_assoc,spectralProj_sq,traceInner_eq_trace]
  rw [← Matrix.mul_assoc,← Matrix.conjTranspose_eq_transpose_of_trivial X,gram_diagonalization X]
  let Q : Matrix (Fin p) (Fin p) ℝ := orderedUnitary X
  have he : (Q*diagonal (gramEigen X)*star Q)*(Q*coordinateProj S*star Q) = Q*(diagonal (gramEigen X)*coordinateProj S)*star Q := by
    calc
      _ = Q*diagonal (gramEigen X)*(star Q*Q)*coordinateProj S*star Q := by noncomm_ring
      _ = _ := by rw [show star Q*Q=1 from Unitary.coe_star_mul_self (orderedUnitary X)]; simp only [Matrix.mul_one,Matrix.mul_assoc]
  change Matrix.trace ((Q*diagonal (gramEigen X)*star Q)*(Q*coordinateProj S*star Q)) = _
  rw [he,trace_unitary_conj,coordinateProj,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_mem,Finset.univ_inter,sv_sq]
end IRLSMProof

-- Module: IRLSMProof.ActualTangent
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank
variable {n p : ℕ}

noncomputable def rightSupport (X : Matrix (Fin n) (Fin p) ℝ) := spectralProj X (gramSupport X)
noncomputable def leftSupport (X : Matrix (Fin n) (Fin p) ℝ) := rightSupport Xᵀ

theorem rightSupport_mul (X : Matrix (Fin n) (Fin p) ℝ) : X*rightSupport X=X := mul_support_eq X

theorem leftSupport_mul (X : Matrix (Fin n) (Fin p) ℝ) : leftSupport X*X=X := by
  have h := congrArg Matrix.transpose (mul_support_eq Xᵀ)
  simpa only [leftSupport,rightSupport,Matrix.transpose_mul,Matrix.transpose_transpose,spectralProj_transpose] using h

theorem rightSupport_rank (X : Matrix (Fin n) (Fin p) ℝ) : (rightSupport X).rank ≤ X.rank := support_rank X

theorem leftSupport_rank (X : Matrix (Fin n) (Fin p) ℝ) : (leftSupport X).rank ≤ X.rank := by
  simpa only [leftSupport,Matrix.rank_transpose] using rightSupport_rank Xᵀ

theorem actual_tangent_certificate (X X1 : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (hr : X1.rank≤k) :
    X=tangentH (leftSupport X1) (rightSupport X1) X + tangentB (leftSupport X1) (rightSupport X1) X ∧
    (tangentH (leftSupport X1) (rightSupport X1) X).rank≤2*k ∧
    leftSupport X1*tangentB (leftSupport X1) (rightSupport X1) X=0 ∧
    tangentB (leftSupport X1) (rightSupport X1) X*rightSupport X1=0 ∧
    X1*(tangentB (leftSupport X1) (rightSupport X1) X)ᵀ=0 ∧
    X1ᵀ*tangentB (leftSupport X1) (rightSupport X1) X=0 ∧
    traceInner (tangentH (leftSupport X1) (rightSupport X1) X)
      (tangentB (leftSupport X1) (rightSupport X1) X)=0 := by
  exact tangent_certificate (leftSupport X1) (rightSupport X1) X X1 k
    (spectralProj_transpose _ _) (spectralProj_transpose _ _)
    (spectralProj_sq _ _) (spectralProj_sq _ _)
    ((leftSupport_rank X1).trans hr) ((rightSupport_rank X1).trans hr)
    (leftSupport_mul X1) (rightSupport_mul X1)
end IRLSMProof

-- Module: IRLSMProof.ScalarShelling

open scoped BigOperators
open Finset
namespace IRLSMProof

def shellIndices (p k j : ℕ) : Finset (Fin p) :=
  univ.filter fun i => j * k ≤ i.val ∧ i.val < (j + 1) * k

@[simp] theorem mem_shellIndices {p k j : ℕ} {i : Fin p} :
    i ∈ shellIndices p k j ↔ j * k ≤ i.val ∧ i.val < (j + 1) * k := by
  simp [shellIndices]

theorem shell_card_le (p k j : ℕ) : (shellIndices p k j).card ≤ k := by
  have hsub : (shellIndices p k j).image Fin.val ⊆ Ico (j * k) ((j + 1) * k) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact mem_Ico.mpr (mem_shellIndices.mp hi)
  have hc := card_le_card hsub
  rw [card_image_of_injective _ Fin.val_injective, Nat.card_Ico] at hc
  simpa [Nat.add_mul] using hc

theorem shell_card_eq {p k j : ℕ} (h : (j + 1) * k ≤ p) :
    (shellIndices p k j).card = k := by
  have he : (shellIndices p k j).image Fin.val = Ico (j * k) ((j + 1) * k) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact mem_Ico.mpr (mem_shellIndices.mp hi)
    · intro hx
      have hx' := mem_Ico.mp hx
      exact mem_image.mpr ⟨⟨x, lt_of_lt_of_le hx'.2 h⟩, mem_shellIndices.mpr hx', rfl⟩
  have hc := congrArg Finset.card he
  rw [card_image_of_injective _ Fin.val_injective, Nat.card_Ico] at hc
  simpa [Nat.add_mul] using hc

theorem shell_point_bound {p k j : ℕ} (s : Fin p → ℝ) (hs : Antitone s)
    {i : Fin p} (hi : i ∈ shellIndices p k (j + 1)) :
    (k : ℝ) * s i ≤ ∑ a ∈ shellIndices p k j, s a := by
  have hip := mem_shellIndices.mp hi
  have hc := shell_card_eq (p := p) (k := k) (j := j) (by omega)
  calc
    (k : ℝ) * s i = ∑ _a ∈ shellIndices p k j, s i := by simp [hc]
    _ ≤ ∑ a ∈ shellIndices p k j, s a := by
      apply sum_le_sum
      intro a ha
      apply hs
      have hap := mem_shellIndices.mp ha
      exact Fin.le_iff_val_le_val.mpr (by omega)

theorem shell_energy_bound {p k : ℕ} (s : Fin p → ℝ) (hs : Antitone s)
    (h0 : ∀ i, 0 ≤ s i) (hk : 0 < k) (j : ℕ) :
    Real.sqrt (∑ i ∈ shellIndices p k (j + 1), s i ^ 2) ≤
      (∑ i ∈ shellIndices p k j, s i) / Real.sqrt k := by
  let S : ℝ := ∑ i ∈ shellIndices p k j, s i
  have hS : 0 ≤ S := sum_nonneg fun i _ => h0 i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcard : ((shellIndices p k (j + 1)).card : ℝ) ≤ k := by
    exact_mod_cast shell_card_le p k (j + 1)
  have hb : ∀ i ∈ shellIndices p k (j + 1), s i ≤ S / k := by
    intro i hi
    exact (le_div_iff₀ hkR).mpr (by simpa [mul_comm, S] using shell_point_bound s hs hi)
  have he : (∑ i ∈ shellIndices p k (j + 1), s i ^ 2) ≤ (S / Real.sqrt k) ^ 2 := by
    calc
      (∑ i ∈ shellIndices p k (j + 1), s i ^ 2) ≤
          ∑ _i ∈ shellIndices p k (j + 1), (S / k) ^ 2 := by
        apply sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (h0 i) (hb i hi) 2
      _ = ((shellIndices p k (j + 1)).card : ℝ) * (S / k) ^ 2 := by simp
      _ ≤ (k : ℝ) * (S / k) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = (S / Real.sqrt k) ^ 2 := by
        rw [div_pow, div_pow, Real.sq_sqrt hkR.le]
        field_simp
  exact (Real.sqrt_le_iff).mpr ⟨div_nonneg hS (Real.sqrt_nonneg _), he⟩

theorem shell_disjoint {p k : ℕ} {i j : ℕ} (hij : i ≠ j) :
    Disjoint (shellIndices p k i) (shellIndices p k j) := by
  apply disjoint_left.mpr
  intro a hai haj
  have hi := mem_shellIndices.mp hai
  have hj := mem_shellIndices.mp haj
  rcases lt_or_gt_of_ne hij with h | h
  · have hm := Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr h)
    simp only [Nat.succ_eq_add_one] at hm
    omega
  · have hm := Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr h)
    simp only [Nat.succ_eq_add_one] at hm
    omega

theorem sum_shell_mass_le {p k : ℕ} (s : Fin p → ℝ) (h0 : ∀ i, 0 ≤ s i)
    (J : Finset ℕ) :
    (∑ j ∈ J, ∑ i ∈ shellIndices p k j, s i) ≤ ∑ i, s i := by
  have hd : Set.PairwiseDisjoint (↑J) (shellIndices p k) := by
    intro i _ j _ hij
    exact shell_disjoint hij
  rw [← sum_biUnion hd]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => h0 i)

theorem scalar_shelling {p k : ℕ} (s : Fin p → ℝ) (hs : Antitone s)
    (h0 : ∀ i, 0 ≤ s i) (hk : 0 < k) :
    (∑ j ∈ range p, Real.sqrt (∑ i ∈ shellIndices p k (j + 1), s i ^ 2)) ≤
      (∑ i, s i) / Real.sqrt k := by
  calc
    _ ≤ ∑ j ∈ range p, (∑ i ∈ shellIndices p k j, s i) / Real.sqrt k := by
      exact sum_le_sum fun j _ => shell_energy_bound s hs h0 hk j
    _ = (∑ j ∈ range p, ∑ i ∈ shellIndices p k j, s i) / Real.sqrt k := by
      rw [sum_div]
    _ ≤ (∑ i, s i) / Real.sqrt k :=
      div_le_div_of_nonneg_right (sum_shell_mass_le s h0 _) (Real.sqrt_nonneg _)

end IRLSMProof

-- Module: IRLSMProof.ShellPartition
namespace IRLSMProof
open Finset

theorem mem_shell_quotient {p k : ℕ} (hk : 0 < k) (i : Fin p) :
    i ∈ shellIndices p k (i.val / k) := by
  apply mem_shellIndices.mpr
  constructor
  · exact Nat.div_mul_le_self i.val k
  · exact (Nat.div_lt_iff_lt_mul hk).mp (Nat.lt_succ_self (i.val / k))

theorem shell_quotient_mem_range {p k : ℕ} (i : Fin p) :
    i.val / k ∈ range (p+1) := by
  apply mem_range.mpr
  have h := Nat.div_le_self i.val k
  omega

theorem shell_indicator_sum {p k : ℕ} (hk : 0 < k) (i : Fin p) :
    (∑ j ∈ range (p+1), if i ∈ shellIndices p k j then (1:ℝ) else 0) = 1 := by
  classical
  have hi := mem_shell_quotient hk i
  rw [sum_eq_single (i.val / k)]
  · simp [hi]
  · intro j _ hne
    have hnot : i ∉ shellIndices p k j := by
      intro hij
      exact (disjoint_left.mp (shell_disjoint hne)) hij hi
    simp [hnot]
  · intro hnot
    exact False.elim (hnot (shell_quotient_mem_range i))

end IRLSMProof

-- Module: IRLSMProof.SpectralBlocks
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank Finset
variable {n p : ℕ}

theorem coordinate_shell_sum (k : ℕ) (hk : 0 < k) :
    (∑ j ∈ range (p+1), coordinateProj (shellIndices p k j)) = (1 : Matrix (Fin p) (Fin p) ℝ) := by
  classical
  ext a b
  simp only [Matrix.sum_apply,coordinateProj,Matrix.diagonal_apply]
  by_cases hab : a=b
  · subst b
    simpa only [if_true,Matrix.one_apply_eq] using shell_indicator_sum hk a
  · simp [hab]

theorem spectral_shell_sum (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (hk : 0 < k) :
    (∑ j ∈ range (p+1), spectralProj X (shellIndices p k j)) = 1 := by
  simp only [spectralProj]
  rw [← Finset.sum_mul,← Finset.mul_sum,coordinate_shell_sum k hk,Matrix.mul_one]
  exact Unitary.coe_mul_star_self (orderedUnitary X)

theorem block_shell_sum (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (hk : 0 < k) :
    (∑ j ∈ range (p+1), spectralBlock X (shellIndices p k j)) = X := by
  simp only [spectralBlock]
  rw [← Matrix.mul_sum,spectral_shell_sum X k hk,Matrix.mul_one]

theorem full_block_certificate (X X1 : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hk : 0 < k) (hr : X1.rank ≤ k) :
    ∃ (H B : Matrix (Fin n) (Fin p) ℝ) (Y : ℕ → Matrix (Fin n) (Fin p) ℝ),
      X=H+B ∧ H.rank≤2*k ∧ traceInner H B=0 ∧ X1*Bᵀ=0 ∧ X1ᵀ*B=0 ∧
      (∀ j,(Y j).rank≤k) ∧ (∀ j,traceInner H (Y j)=0) ∧
      (∀ i j,i≠j → traceInner (Y i) (Y j)=0) ∧
      (∀ j,frobeniusNorm (Y j)^2 = ∑ i ∈ shellIndices p k j,singularValues B i^2) ∧
      (∑ j ∈ range (p+1),Y j)=B := by
  let P := leftSupport X1
  let Q := rightSupport X1
  let H := tangentH P Q X
  let B := tangentB P Q X
  let Y := fun j => spectralBlock B (shellIndices p k j)
  obtain ⟨hX,hH,hPB,hBQ,hXB,hXTB,hHB⟩ := actual_tangent_certificate X X1 k hr
  refine ⟨H,B,Y,hX,hH,hHB,hXB,hXTB,?_,?_,?_,?_,?_⟩
  · intro j
    exact (block_rank B (shellIndices p k j)).trans (shell_card_le p k j)
  · intro j
    exact tangent_trace_zero P Q X (Y j) (spectralProj_transpose _ _) (spectralProj_transpose _ _)
      (block_left_zero B (shellIndices p k j) P hPB) (block_right_zero B (shellIndices p k j) Q hBQ)
  · intro i j hij
    exact blocks_orthogonal B _ _ (shell_disjoint hij)
  · intro j
    exact block_energy B (shellIndices p k j)
  · exact block_shell_sum B k hk
end IRLSMProof

-- Module: IRLSMProof.RIPInfimum

open scoped BigOperators
open Matrix HighDimStat.MatrixRank IRLSM.Convergence
namespace IRLSMProof
variable {n p m : ℕ}

def ripAdmissible (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ ∀ X : Matrix (Fin n) (Fin p) ℝ, X.rank ≤ k →
    (1 - δ) * frobeniusNorm X ^ 2 ≤ measSq A X ∧
      measSq A X ≤ (1 + δ) * frobeniusNorm X ^ 2}

theorem trace_cs_sq (X Y : Matrix (Fin n) (Fin p) ℝ) :
    traceInner X Y ^ 2 ≤ frobeniusNorm X ^ 2 * frobeniusNorm Y ^ 2 := by
  rw [frob_sq, frob_sq]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin p))
    (fun i => X i.1 i.2) (fun i => Y i.1 i.2)
  simpa [traceInner, Fintype.sum_prod_type] using h

theorem measSq_nonneg (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) : 0 ≤ measSq A X :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem measSq_le_energy (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) :
    measSq A X ≤ (∑ l, frobeniusNorm (A l) ^ 2) * frobeniusNorm X ^ 2 := by
  unfold measSq
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun l _ => trace_cs_sq (A l) X

theorem ripAdmissible_nonempty (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    (ripAdmissible A k).Nonempty := by
  let K : ℝ := ∑ l, frobeniusNorm (A l) ^ 2
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨1 + K, ?_, ?_⟩
  · linarith
  · intro X _
    constructor
    · have hM := measSq_nonneg A X
      have hF := sq_nonneg (frobeniusNorm X)
      nlinarith [mul_nonneg hK hF]
    · have hM := measSq_le_energy A X
      have hF := sq_nonneg (frobeniusNorm X)
      dsimp [K] at *
      nlinarith

theorem ripAdmissible_bddBelow (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    BddBelow (ripAdmissible A k) := ⟨0, fun _ h => h.1⟩

theorem ripAdmissible_closed (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    IsClosed (ripAdmissible A k) := by
  unfold ripAdmissible
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter (isClosed_le continuous_const continuous_id)
  apply isClosed_iInter
  intro X
  apply isClosed_iInter
  intro _hX
  exact (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le continuous_const (by fun_prop))

theorem rip_attained (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    ripConst A k ∈ ripAdmissible A k :=
  (ripAdmissible_closed A k).csInf_mem (ripAdmissible_nonempty A k)
    (ripAdmissible_bddBelow A k)

theorem rip_nonneg (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    0 ≤ ripConst A k := (rip_attained A k).1

theorem rip_bounds (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (X : Matrix (Fin n) (Fin p) ℝ) (hX : X.rank ≤ k) :
    (1 - ripConst A k) * frobeniusNorm X ^ 2 ≤ measSq A X ∧
      measSq A X ≤ (1 + ripConst A k) * frobeniusNorm X ^ 2 :=
  (rip_attained A k).2 X hX

theorem rip_mono (A : Fin m → Matrix (Fin n) (Fin p) ℝ) {k l : ℕ} (h : k ≤ l) :
    ripConst A k ≤ ripConst A l := by
  apply csInf_le (ripAdmissible_bddBelow A k)
  exact ⟨rip_nonneg A l, fun X hX => rip_bounds A l X (hX.trans h)⟩

theorem eta_bounds (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hpos : 0 < ripConst A (4 * k)) (h66 : ripConst A (4 * k) < Real.sqrt 2 - 1) :
    0 < Real.sqrt 2 * ripConst A (4 * k) / (1 - ripConst A (3 * k)) ∧
      Real.sqrt 2 * ripConst A (4 * k) / (1 - ripConst A (3 * k)) < 1 := by
  have hm := rip_mono A (k := 3*k) (l := 4*k) (by omega)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslt : Real.sqrt 2 < 2 := by nlinarith
  have hd : 0 < 1 - ripConst A (3*k) := by linarith
  refine ⟨div_pos (mul_pos hs hpos) hd, (div_lt_one hd).mpr ?_⟩
  have ht := mul_lt_mul_of_pos_left h66 (show 0 < Real.sqrt 2 + 1 by positivity)
  nlinarith

end IRLSMProof

-- Module: IRLSMProof.RestrictedOrthogonality
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank IRLSM.Convergence
variable {n p m : ℕ}

def measurementInner (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (X Y : Matrix (Fin n) (Fin p) ℝ) : ℝ :=
  ∑ l, observationOp A X l * observationOp A Y l

theorem measurementInner_smul (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (a b : ℝ) (X Y : Matrix (Fin n) (Fin p) ℝ) :
    measurementInner A (a • X) (b • Y) = a * b * measurementInner A X Y := by
  simp only [measurementInner, obs_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem measSq_add (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (X Y : Matrix (Fin n) (Fin p) ℝ) :
    measSq A (X+Y) = measSq A X + 2 * measurementInner A X Y + measSq A Y := by
  simp only [measSq, measurementInner, obs_add, Pi.add_apply, add_sq,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem restricted_orthogonality_unit (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (r : ℕ) (X Y : Matrix (Fin n) (Fin p) ℝ)
    (hr : X.rank + Y.rank ≤ r) (ho : traceInner X Y = 0)
    (hX : frobeniusNorm X = 1) (hY : frobeniusNorm Y = 1) :
    |measurementInner A X Y| ≤ ripConst A r := by
  have hplus := rip_bounds A r (X+Y) ((rank_add_le X Y).trans hr)
  have hrneg : ((-1 : ℝ) • Y).rank ≤ Y.rank := rank_smul_le _ _
  have hminus := rip_bounds A r (X+(-1:ℝ)•Y)
    ((rank_add_le _ _).trans (Nat.add_le_add_left hrneg _ |>.trans hr))
  have hp : frobeniusNorm (X+Y)^2 = 2 := by rw [frob_add_sq, ho, hX, hY]; norm_num
  have hn : frobeniusNorm (X+(-1:ℝ)•Y)^2 = 2 := by
    rw [frob_add_sq, trace_smul_right, ho, frob_smul_sq, hX, hY]; norm_num
  have he : measSq A (X+(-1:ℝ)•Y) =
      measSq A X - 2*measurementInner A X Y + measSq A Y := by
    rw [measSq_add]
    have ht : measurementInner A X ((-1:ℝ)•Y) = -measurementInner A X Y := by
      simpa using measurementInner_smul A 1 (-1) X Y
    have hm : measSq A ((-1:ℝ)•Y) = measSq A Y := by
      simp only [measSq, obs_smul, Pi.smul_apply, smul_eq_mul, neg_one_mul, neg_sq]
    rw [ht, hm]; ring
  rw [hp, measSq_add] at hplus
  rw [hn, he] at hminus
  exact abs_le.mpr ⟨by linarith [hminus.2, hplus.1], by linarith [hplus.2, hminus.1]⟩

theorem restricted_orthogonality (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (r : ℕ) (X Y : Matrix (Fin n) (Fin p) ℝ)
    (hr : X.rank + Y.rank ≤ r) (ho : traceInner X Y = 0) :
    |measurementInner A X Y| ≤ ripConst A r * frobeniusNorm X * frobeniusNorm Y := by
  by_cases hX : X = 0
  · subst X; simp [measurementInner, obs_zero, frobeniusNorm]
  by_cases hY : Y = 0
  · subst Y; simp [measurementInner, obs_zero, frobeniusNorm]
  have hFX := (frob_pos_iff X).mpr hX
  have hFY := (frob_pos_iff Y).mpr hY
  let U := (frobeniusNorm X)⁻¹ • X
  let V := (frobeniusNorm Y)⁻¹ • Y
  have hu : frobeniusNorm U = 1 := by
    rw [frob_smul, abs_of_pos (inv_pos.mpr hFX), inv_mul_cancel₀ (ne_of_gt hFX)]
  have hv : frobeniusNorm V = 1 := by
    rw [frob_smul, abs_of_pos (inv_pos.mpr hFY), inv_mul_cancel₀ (ne_of_gt hFY)]
  have huv : traceInner U V = 0 := by
    rw [trace_smul_left, trace_smul_right, ho]; ring
  have hruv : U.rank + V.rank ≤ r :=
    (Nat.add_le_add (rank_smul_le _ _) (rank_smul_le _ _)).trans hr
  have h := restricted_orthogonality_unit A r U V hruv huv hu hv
  change |measurementInner A ((frobeniusNorm X)⁻¹ • X) ((frobeniusNorm Y)⁻¹ • Y)| ≤ _ at h
  rw [measurementInner_smul] at h
  have he : (frobeniusNorm X)⁻¹ * (frobeniusNorm Y)⁻¹ * measurementInner A X Y =
      measurementInner A X Y / (frobeniusNorm X * frobeniusNorm Y) := by ring
  rw [he, abs_div, abs_of_pos (mul_pos hFX hFY)] at h
  have hh := (div_le_iff₀ (mul_pos hFX hFY)).mp h
  simpa [mul_assoc] using hh

end IRLSMProof

-- Module: IRLSMProof.BlockEstimate
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank IRLSM.Convergence Finset
variable {n p m : ℕ}

theorem obs_sum {ι : Type*} (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (J : Finset ι) (Y : ι → Matrix (Fin n) (Fin p) ℝ) :
    observationOp A (∑ j ∈ J, Y j) = ∑ j ∈ J, observationOp A (Y j) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih => simp only [sum_insert ha, obs_add, ih]

theorem measurementInner_add_right (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (X Y Z : Matrix (Fin n) (Fin p) ℝ) :
    measurementInner A X (Y+Z) = measurementInner A X Y + measurementInner A X Z := by
  simp only [measurementInner, obs_add, Pi.add_apply, mul_add, sum_add_distrib]

theorem measurementInner_sum_right {ι : Type*} (A : Fin m → Matrix (Fin n) (Fin p) ℝ)
    (X : Matrix (Fin n) (Fin p) ℝ) (J : Finset ι) (Y : ι → Matrix (Fin n) (Fin p) ℝ) :
    measurementInner A X (∑ j ∈ J, Y j) = ∑ j ∈ J, measurementInner A X (Y j) := by
  simp only [measurementInner, obs_sum, Finset.sum_apply, mul_sum]
  exact sum_comm

theorem block_nuclear_bound (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hk : 0 < k) (h66 : ripConst A (4*k) < Real.sqrt 2 - 1)
    (H B : Matrix (Fin n) (Fin p) ℝ) (Y : ℕ → Matrix (Fin n) (Fin p) ℝ)
    (s : Fin p → ℝ) (hs : Antitone s) (h0 : ∀ i, 0 ≤ s i)
    (hnuc : nuclearNorm B = ∑ i, s i)
    (hH : H.rank ≤ 2*k) (hY : ∀ j, (Y j).rank ≤ k)
    (hHY : ∀ j, traceInner H (Y j) = 0)
    (hYY : ∀ i j, i ≠ j → traceInner (Y i) (Y j) = 0)
    (henergy : ∀ j, frobeniusNorm (Y j)^2 = ∑ i ∈ shellIndices p k j, s i^2)
    (hsum : ∑ j ∈ range (p+1), Y j = B)
    (hker : observationOp A (H+B) = 0)
    (hNF : nuclearNorm H ≤ Real.sqrt (2*k) * frobeniusNorm H) :
    nuclearNorm H ≤ (Real.sqrt 2 * ripConst A (4*k) / (1-ripConst A (3*k))) * nuclearNorm B := by
  let Z := H + Y 0
  have hZrank : Z.rank ≤ 3*k := by
    exact (rank_add_le H (Y 0)).trans (by have := hY 0; omega)
  have hZorth : ∀ j, traceInner Z (Y (j+1)) = 0 := by
    intro j
    rw [trace_add_left, hHY, hYY 0 (j+1) (by omega), add_zero]
  have hdecomp : H+B = Z + ∑ j ∈ range p, Y (j+1) := by
    rw [← hsum, sum_range_succ']
    dsimp [Z]
    abel
  have hcross : measSq A Z + ∑ j ∈ range p, measurementInner A Z (Y (j+1)) = 0 := by
    have he : measurementInner A Z (H+B) = 0 := by simp [measurementInner, hker]
    rw [hdecomp, measurementInner_add_right, measurementInner_sum_right] at he
    simpa [measurementInner, measSq, pow_two] using he
  have hmeas : measSq A Z ≤ ∑ j ∈ range p, |measurementInner A Z (Y (j+1))| := by
    have hh : -(∑ j ∈ range p, measurementInner A Z (Y (j+1))) ≤
        ∑ j ∈ range p, |measurementInner A Z (Y (j+1))| := by
      rw [← sum_neg_distrib]
      exact sum_le_sum fun j _ => neg_le_abs _
    linarith
  have htail : (∑ j ∈ range p, frobeniusNorm (Y (j+1))) ≤ nuclearNorm B / Real.sqrt k := by
    have hnorm : ∀ j, frobeniusNorm (Y j) = Real.sqrt (∑ i ∈ shellIndices p k j, s i^2) := by
      intro j
      rw [← henergy, Real.sqrt_sq (frob_nonneg _)]
    simp_rw [hnorm]
    rw [hnuc]
    exact scalar_shelling s hs h0 hk
  have hmain : (1-ripConst A (3*k))*frobeniusNorm Z^2 ≤
      ripConst A (4*k)*frobeniusNorm Z * (nuclearNorm B / Real.sqrt k) := by
    calc
      _ ≤ measSq A Z := (rip_bounds A (3*k) Z hZrank).1
      _ ≤ ∑ j ∈ range p, |measurementInner A Z (Y (j+1))| := hmeas
      _ ≤ ∑ j ∈ range p, ripConst A (4*k)*frobeniusNorm Z*frobeniusNorm (Y (j+1)) := by
        apply sum_le_sum
        intro j _
        exact restricted_orthogonality A (4*k) Z (Y (j+1))
          (by have := hY (j+1); omega) (hZorth j)
      _ = ripConst A (4*k)*frobeniusNorm Z * (∑ j ∈ range p, frobeniusNorm (Y (j+1))) := by
        rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left htail (mul_nonneg (rip_nonneg A _) (frob_nonneg _))
  have hF : frobeniusNorm H ≤ frobeniusNorm Z := by
    have he := frob_add_sq H (Y 0)
    rw [hHY 0] at he
    have hH0 := frob_nonneg H
    have hZ0 := frob_nonneg Z
    change frobeniusNorm Z^2 = _ at he
    nlinarith [sq_nonneg (frobeniusNorm (Y 0))]
  have hm := rip_mono A (k := 3*k) (l := 4*k) (by omega)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  have hd : 0 < 1-ripConst A (3*k) := by nlinarith
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
  have hN0 : 0 ≤ nuclearNorm B := by rw [hnuc]; exact sum_nonneg fun i _ => h0 i
  have hcoef : 0 ≤ (Real.sqrt 2 * ripConst A (4*k)/(1-ripConst A (3*k))) :=
    div_nonneg (mul_nonneg hs0 (rip_nonneg A _)) hd.le
  by_cases hz : frobeniusNorm Z = 0
  · have hh : frobeniusNorm H = 0 := le_antisymm (hF.trans_eq hz) (frob_nonneg H)
    rw [hh, mul_zero] at hNF
    exact hNF.trans (mul_nonneg hcoef hN0)
  have hzpos : 0 < frobeniusNorm Z := lt_of_le_of_ne (frob_nonneg Z) (Ne.symm hz)
  have hcancel : (1-ripConst A (3*k))*frobeniusNorm Z ≤
      ripConst A (4*k)*(nuclearNorm B/Real.sqrt k) := by
    apply (mul_le_mul_iff_right₀ hzpos).mp
    nlinarith only [hmain]
  have hZF : frobeniusNorm Z ≤
      ripConst A (4*k)*(nuclearNorm B/Real.sqrt k)/(1-ripConst A (3*k)) :=
    (le_div_iff₀ hd).mpr (by simpa [mul_comm] using hcancel)
  calc
    nuclearNorm H ≤ Real.sqrt (2*k)*frobeniusNorm H := hNF
    _ ≤ Real.sqrt (2*k)*frobeniusNorm Z := mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2*k)*(ripConst A (4*k)*(nuclearNorm B/Real.sqrt k)/(1-ripConst A (3*k))) :=
      mul_le_mul_of_nonneg_left hZF (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      field_simp

end IRLSMProof

-- Module: IRLSMProof.RankBasics
namespace IRLSMProof
open Matrix

theorem matrix_rank_zero_iff {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) : X.rank=0 ↔ X=0 := by
  constructor
  · intro h
    have hr : LinearMap.range X.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
    have hx : X.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
    ext i j
    have he := congrArg (fun F : (Fin p → ℝ) →ₗ[ℝ] (Fin n → ℝ) => F (Pi.single j 1) i) hx
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using he
  · rintro rfl; exact Matrix.rank_zero
end IRLSMProof

-- Module: IRLSMProof.RIPEdges
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank IRLSM.Convergence
variable {n p m : ℕ}

theorem rip_zero (A : Fin m → Matrix (Fin n) (Fin p) ℝ) : ripConst A 0 = 0 := by
  apply le_antisymm _ (rip_nonneg A 0)
  apply csInf_le (ripAdmissible_bddBelow A 0)
  refine ⟨le_rfl, ?_⟩
  intro X hX
  have hx : X = 0 := (matrix_rank_zero_iff X).mp (Nat.eq_zero_of_le_zero hX)
  subst X
  simp [frobeniusNorm, measSq, obs_zero]

theorem rank_parameter_pos (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hpos : 0 < ripConst A (4*k)) : 0 < k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  simp [hk0, rip_zero] at hpos

end IRLSMProof

-- Module: IRLSMProof.Root
namespace IRLSMProof
open Matrix HighDimStat.MatrixRank IRLSM.Convergence

theorem full_solution {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hpos : 0 < ripConst A (4*k)) (h66 : ripConst A (4*k) < Real.sqrt 2 - 1) :
    SRNSP A k (Real.sqrt 2 * ripConst A (4*k)/(1-ripConst A (3*k))) := by
  have heta := eta_bounds A k hpos h66
  have hk := rank_parameter_pos A k hpos
  refine ⟨heta.1, heta.2, ?_⟩
  intro X hker _hne X1 _X2 _hdecomp hrank
  obtain ⟨H,B,Y,hXB,hH,hHB,hX1B,hX1tB,hY,hHY,hYY,henergy,hsum⟩ :=
    full_block_certificate X X1 k hk hrank
  refine ⟨H,B,hXB,hH,hHB,hX1B,hX1tB,?_⟩
  have hNF : nuclearNorm H ≤ Real.sqrt (2*k)*frobeniusNorm H := by
    apply (nuclear_rank_bound H).trans
    apply mul_le_mul_of_nonneg_right _ (frob_nonneg H)
    apply Real.sqrt_le_sqrt
    exact_mod_cast hH
  exact block_nuclear_bound A k hk h66 H B Y (singularValues B)
    (sv_antitone B) (sv_nonneg B) rfl hH hY hHY hYY henergy hsum
    (by rw [← hXB]; exact hker) hNF

end IRLSMProof

theorem solution {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hpos : 0 < IRLSM.Convergence.ripConst A (4 * k)) (h66 : IRLSM.Convergence.ripConst A (4 * k) < Real.sqrt 2 - 1) :
    IRLSM.Convergence.SRNSP A k (Real.sqrt 2 * IRLSM.Convergence.ripConst A (4 * k) / (1 - IRLSM.Convergence.ripConst A (3 * k))) := IRLSMProof.full_solution A k hpos h66

namespace IRLSM.RIP
theorem proposition_6_8 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hpos : 0 < IRLSM.Convergence.ripConst A (4 * k)) (h66 : IRLSM.Convergence.ripConst A (4 * k) < Real.sqrt 2 - 1) :
    IRLSM.Convergence.SRNSP A k (Real.sqrt 2 * IRLSM.Convergence.ripConst A (4 * k) / (1 - IRLSM.Convergence.ripConst A (3 * k))) := IRLSMProof.full_solution A k hpos h66
end IRLSM.RIP
