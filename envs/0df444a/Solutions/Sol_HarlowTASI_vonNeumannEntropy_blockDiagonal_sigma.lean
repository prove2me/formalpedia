-- Prove2me | solution 1 for HarlowTASI.vonNeumannEntropy_blockDiagonal_sigma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:54:52.419288+00:00
-- url     : https://prove2.me/submissions/532c7284-d0f2-4728-b1da-90598a5e9204

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics
open Matrix Polynomial
open scoped Kronecker ComplexOrder

namespace S192HT

lemma ent_roots {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    HarlowTASI.vonNeumannEntropy A =
      ((A.charpoly.roots).map (fun z : ℂ => Real.negMulLog z.re)).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  unfold HarlowTASI.vonNeumannEntropy
  rw [dif_pos hA]
  rfl

lemma ent_udiag {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (P : Matrix n n ℂ) (hP : Pᴴ * P = 1) (f : n → ℝ)
    (h : A = P * diagonal (fun i => (f i : ℂ)) * Pᴴ) :
    HarlowTASI.vonNeumannEntropy A = ∑ i, Real.negMulLog (f i) := by
  rw [ent_roots _ hA]
  have hc : A.charpoly = ∏ i, (X - C (f i : ℂ)) := by
    rw [h, Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc, hP, Matrix.mul_one,
      charpoly_diagonal]
  rw [hc, roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero])]
  simp only [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map]
  rfl

lemma spec {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ∃ P : Matrix n n ℂ, Pᴴ * P = 1 ∧
      A = P * diagonal (fun i => (hA.eigenvalues i : ℂ)) * Pᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℂ), ?_, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2)
  · conv_lhs => rw [hA.spectral_theorem]
    rfl

lemma ent_blockDiag {ι : Type} [Fintype ι] [DecidableEq ι]
    {o : ι → Type} [∀ a, Fintype (o a)] [∀ a, DecidableEq (o a)]
    (Y : ∀ a, Matrix (o a) (o a) ℂ) (hY : ∀ a, (Y a).IsHermitian) :
    HarlowTASI.vonNeumannEntropy (blockDiagonal' Y) = ∑ a, HarlowTASI.vonNeumannEntropy (Y a) := by
  choose P hP hYP using fun a => spec (Y a) (hY a)
  have hB : (blockDiagonal' Y).IsHermitian := by
    unfold IsHermitian
    rw [blockDiagonal'_conjTranspose]
    exact congrArg _ (funext fun a => hY a)
  rw [ent_udiag _ hB (blockDiagonal' P) ?_ (fun ik => (hY ik.1).eigenvalues ik.2) ?_]
  · rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ent_udiag _ (hY a) (P a) (hP a) _ (hYP a)]
  · rw [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
    simp_rw [hP]
    exact blockDiagonal'_one
  · rw [← blockDiagonal'_diagonal (fun a i => ((hY a).eigenvalues i : ℂ)), blockDiagonal'_conjTranspose,
      ← blockDiagonal'_mul, ← blockDiagonal'_mul]
    exact congrArg _ (funext hYP)

lemma ent_kron {p q : Type} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (A : Matrix p p ℂ) (B : Matrix q q ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    HarlowTASI.vonNeumannEntropy (A ⊗ₖ B) =
      B.trace.re * HarlowTASI.vonNeumannEntropy A + A.trace.re * HarlowTASI.vonNeumannEntropy B := by
  obtain ⟨P, hP, hAP⟩ := spec A hA
  obtain ⟨Q, hQ, hBQ⟩ := spec B hB
  have hK : (A ⊗ₖ B).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_kronecker, hA.eq, hB.eq]
  have htA : A.trace.re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]; simp
  have htB : B.trace.re = ∑ i, hB.eigenvalues i := by
    rw [hB.trace_eq_sum_eigenvalues]; simp
  rw [ent_udiag _ hK (P ⊗ₖ Q) ?_ (fun ij => hA.eigenvalues ij.1 * hB.eigenvalues ij.2) ?_,
    ent_udiag _ hA P hP _ hAP, ent_udiag _ hB Q hQ _ hBQ, htA, htB, Fintype.sum_prod_type]
  · simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun x x_1 => hA.eigenvalues x * (hB.eigenvalues x_1).negMulLog)]
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul, hP, hQ, one_kronecker_one]
  · have hD : diagonal (fun ij : p × q => ((hA.eigenvalues ij.1 * hB.eigenvalues ij.2 : ℝ) : ℂ)) =
        diagonal (fun i => (hA.eigenvalues i : ℂ)) ⊗ₖ diagonal (fun j => (hB.eigenvalues j : ℂ)) := by
      rw [diagonal_kronecker_diagonal]
      congr 1
      funext ij
      push_cast
      rfl
    rw [hD, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul, ← hAP, ← hBQ]

end S192HT

open HarlowTASI in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    {o : ι → Type} [∀ a, Fintype (o a)] [∀ a, DecidableEq (o a)]
    (Y : ∀ a, Matrix (o a) (o a) ℂ) (hY : ∀ a, (Y a).IsHermitian) :
    vonNeumannEntropy (blockDiagonal' Y) = ∑ a, vonNeumannEntropy (Y a) := S192HT.ent_blockDiag Y hY
