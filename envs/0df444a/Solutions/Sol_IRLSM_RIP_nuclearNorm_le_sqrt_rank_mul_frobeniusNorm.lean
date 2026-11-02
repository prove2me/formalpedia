-- Prove2me | solution 1 for IRLSM.RIP.nuclearNorm_le_sqrt_rank_mul_frobeniusNorm
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:01.291838+00:00
-- url     : https://prove2.me/submissions/957e6922-6aeb-4f35-a46d-c3abe2b02ae8

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open Matrix HighDimStat.MatrixRank

namespace NuclearRankProof

variable {n p : ℕ}

theorem frob_nonneg (X : Matrix (Fin n) (Fin p) ℝ) : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
theorem frob_sq (X : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm X ^ 2 = ∑ i, ∑ j, X i j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
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
theorem sv_nonneg (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin p) : 0 ≤ singularValues X i := Real.sqrt_nonneg _
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

end NuclearRankProof

-- Adapted from accepted submission 36caa8f3-6eb2-482b-aa8e-e5f8c8ee33e5,
-- which proves the stronger rank-sensitive bound as IRLSMProof.nuclear_rank_bound.
theorem solution {n p : ℕ} (H : Matrix (Fin n) (Fin p) ℝ)
    (r : ℕ) (hr : H.rank ≤ r) :
    nuclearNorm H ≤ Real.sqrt r * frobeniusNorm H := by
  calc
    nuclearNorm H ≤ Real.sqrt (H.rank : ℝ) * frobeniusNorm H :=
      NuclearRankProof.nuclear_rank_bound H
    _ ≤ Real.sqrt r * frobeniusNorm H :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hr))
        (NuclearRankProof.frob_nonneg H)
