-- Prove2me | solution 1 for GlobalTheory.annihilator_diagonal_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:19.029515+00:00
-- url     : https://prove2.me/submissions/fae4ffec-1134-4b45-83bb-c8d0d608d4f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Theorems.Thm_GlobalTheory_annihilator_diagonal_form_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped TensorProduct
namespace GlobalTheory
theorem _root_.solution {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Module.Basis (Fin d) R B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0) :
    ∑ i, ∑ j, (M i j * Algebra.trace R B (b i)) • b j = ∑ i, ∑ j, M i j • (b i * b j) := by
  classical
  have htr : ∀ z : B, Algebra.trace R B z = ∑ k, b.repr (z * b k) k := by
    intro z
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  have key : ∀ k, ∑ i, ∑ j, (M i j * b.repr (b i * b k) k) • b j =
      ∑ i, ∑ j, (M i j * b.repr (b i) k) • (b j * b k) :=
    fun k => annihilator_diagonal_form_swap (fun i => b i) M h (b.coord k) (b k)
  have hij : ∀ i j, ∑ k, (M i j * b.repr (b i) k) • (b j * b k) = M i j • (b i * b j) := by
    intro i j
    conv_rhs => rw [mul_comm, ← b.sum_repr (b i)]
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, smul_smul]
  calc ∑ i, ∑ j, (M i j * Algebra.trace R B (b i)) • b j
      = ∑ i, ∑ j, ∑ k, (M i j * b.repr (b i * b k) k) • b j := by
        simp only [htr, Finset.mul_sum, Finset.sum_smul]
    _ = ∑ k, ∑ i, ∑ j, (M i j * b.repr (b i * b k) k) • b j := by
        symm
        exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
    _ = ∑ k, ∑ i, ∑ j, (M i j * b.repr (b i) k) • (b j * b k) :=
        Finset.sum_congr rfl fun k _ => key k
    _ = ∑ i, ∑ j, ∑ k, (M i j * b.repr (b i) k) • (b j * b k) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ j, M i j • (b i * b j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hij i j
end GlobalTheory
