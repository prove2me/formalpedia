-- Prove2me | solution 1 for MIPRE.xSqNorm_sum_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:14.401925+00:00
-- url     : https://prove2.me/submissions/23686bae-8009-42e6-8718-380fc8ed9d24

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (solution of MIPRE.xSqNorm_sum_le_two_mul);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Theorems.Thm_MIPRE_sum_stateSqNorm_le_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] in
theorem stateVecB_entry (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) (i : dA) (j : dB) :
    (((1 : Matrix dA dA ℂ) ⊗ₖ N) *ᵥ ψ) (i, j) = ∑ l, N j l * ψ (i, l) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_ite_eq, mul_comm]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] in
theorem stateVec_swapVec_entry (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) (i : dA) (j : dB) :
    ((N ⊗ₖ (1 : Matrix dA dA ℂ)) *ᵥ swapVec ψ) (j, i) = ∑ l, N j l * ψ (i, l) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, swapVec, mul_ite,
    Finset.sum_ite_eq]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] in
/-- **Bob's norm is Alice's norm of the swapped state.** -/
theorem norm_stateVecB (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
    ‖stateVecB ψ N‖ = stateNorm (swapVec ψ) N := by
  classical
  rw [stateNorm, stateVecB, stateVec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm dA dB) _ _ fun p => ?_
  obtain ⟨i, j⟩ := p
  show ‖(((1 : Matrix dA dA ℂ) ⊗ₖ N) *ᵥ ψ) (i, j)‖ ^ 2
      = ‖((N ⊗ₖ (1 : Matrix dA dA ℂ)) *ᵥ swapVec ψ) (j, i)‖ ^ 2
  rw [stateVecB_entry, stateVec_swapVec_entry]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
/-- The inner product of the two factors' vectors is the blueprint's `⟨ψ| Q ⊗ R |ψ⟩`, for
self-adjoint `Q`. -/
theorem inner_stateVec_stateVecB (ψ : dA × dB → ℂ) {Q : Matrix dA dA ℂ} (hQ : Qᴴ = Q)
    (R : Matrix dB dB ℂ) :
    inner ℂ (stateVec ψ Q) (stateVecB ψ R) = star ψ ⬝ᵥ ((Q ⊗ₖ R) *ᵥ ψ) := by
  classical
  have hadj : (Q ⊗ₖ (1 : Matrix dB dB ℂ))ᴴ * ((1 : Matrix dA dA ℂ) ⊗ₖ R) = Q ⊗ₖ R := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, hQ]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  show ((1 : Matrix dA dA ℂ) ⊗ₖ R) *ᵥ ψ ⬝ᵥ star ((Q ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ) = _
  rw [dotProduct_comm, star_mulVec_dotProduct, hadj]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] [DecidableEq dA] in
/-- The swap is a reindexing, so it preserves the norm of the state. -/
theorem swapVec_dotProduct (ψ : dA × dB → ℂ) :
    star (swapVec ψ) ⬝ᵥ swapVec ψ = star ψ ⬝ᵥ ψ :=
  (Fintype.sum_equiv (Equiv.prodComm dA dB) _ _ fun _ => rfl).symm
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- Bob's version, by the swap. -/
theorem sum_stateSqNormB_le_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (N : POVM B dB) :
    ∑ b, ‖stateVecB ψ (((N.mats b).val))‖ ^ 2 ≤ 1 := by
  have hψ' : star (swapVec ψ) ⬝ᵥ swapVec ψ = 1 := by rw [swapVec_dotProduct]; exact hψ
  have h := sum_stateSqNorm_le_one (dA := dB) (dB := dA) (A := B) hψ' N
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) h
  rw [norm_stateVecB, stateSqNorm]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq C] in
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : POVM C dA) (N : POVM C dB) :
    ∑ c, xSqNorm ψ (((M.mats c).val)) (((N.mats c).val))
      ≤ 2 * (1 - ∑ c, bornProb ψ (((M.mats c).val)) (((N.mats c).val))) := by
  classical
  have hexp : ∀ c, xSqNorm ψ (((M.mats c).val)) (((N.mats c).val))
      = stateSqNorm ψ (((M.mats c).val)) + ‖stateVecB ψ (((N.mats c).val))‖ ^ 2
        - 2 * bornProb ψ (((M.mats c).val)) (((N.mats c).val)) := by
    intro c
    have hsa : (((M.mats c).val))ᴴ = ((M.mats c).val) := by
      rw [← Matrix.star_eq_conjTranspose, (M.mats c).2]
    rw [xSqNorm, norm_sub_sq (𝕜 := ℂ), inner_stateVec_stateVecB ψ hsa, stateSqNorm,
      stateNorm, bornProb]
    simp only [RCLike.re_to_complex]
    ring
  rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => hexp c]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_stateSqNorm_le_one (dB := dB) hψ M
  have h2 := sum_stateSqNormB_le_one (dA := dA) hψ N
  linarith
end MIPRE
