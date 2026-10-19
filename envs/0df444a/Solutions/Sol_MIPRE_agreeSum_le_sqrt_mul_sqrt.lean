-- Prove2me | solution 1 for MIPRE.agreeSum_le_sqrt_mul_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:40.392506+00:00
-- url     : https://prove2.me/submissions/8d499d91-da78-4568-aef7-bc2e9a82df12

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMMix.lean (solution of MIPRE.agreeSum_le_sqrt_mul_sqrt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

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
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
/-- A Born probability is at most the product of the two state norms (Cauchy--Schwarz). -/
theorem bornProb_le_norm_mul_norm (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} (hEA : EAᴴ = EA)
    (EB : Matrix dB dB ℂ) :
    bornProb ψ EA EB ≤ ‖stateVec ψ EA‖ * ‖stateVecB ψ EB‖ := by
  have h : bornProb ψ EA EB = (inner ℂ (stateVec ψ EA) (stateVecB ψ EB)).re := by
    rw [inner_stateVec_stateVecB ψ hEA, bornProb]
  rw [h]
  exact le_trans (Complex.re_le_norm _) (norm_inner_le_norm _ _)
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
theorem _root_.solution (hμ : ∀ x, 0 ≤ μ x) (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    agreeSum μ ψ M N ≤ Real.sqrt (weightA μ ψ M) * Real.sqrt (weightB μ ψ N) := by
  classical
  have hpt : ∀ x a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val)
      ≤ ‖stateVec ψ (((M x).mats a).val)‖ * ‖stateVecB ψ (((N x).mats a).val)‖ := fun x a =>
    bornProb_le_norm_mul_norm ψ (by
      rw [← Matrix.star_eq_conjTranspose]; exact selfAdjoint.mem_iff.mp ((M x).mats a).prop) _
  have h1 : agreeSum μ ψ M N ≤ ∑ p : X × Λ, μ p.1
      * (‖stateVec ψ (((M p.1).mats p.2).val)‖ * ‖stateVecB ψ (((N p.1).mats p.2).val)‖) := by
    rw [agreeSum, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun x _ => ?_
    dsimp only
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hpt x a) (hμ x)
  refine le_trans h1 (le_of_le_of_eq (sum_weighted_mul_le_sqrt (fun p : X × Λ => μ p.1)
    (fun p => ‖stateVec ψ (((M p.1).mats p.2).val)‖)
    (fun p => ‖stateVecB ψ (((N p.1).mats p.2).val)‖) fun p => hμ p.1) ?_)
  congr 1 <;> congr 1
  · rw [weightA, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [stateSqNorm, stateNorm]
  · rw [weightB, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
end MIPRE
