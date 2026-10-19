-- Prove2me | solution 1 for MIPRE.xDev_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:05.754517+00:00
-- url     : https://prove2.me/submissions/3c51ab9b-dce7-4054-b26c-8db153128f8c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMMix.lean (solution of MIPRE.xDev_eq);
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
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **Expanding a cross-party deviation.** -/
theorem xSqNorm_eq_expand (ψ : dA × dB → ℂ) {A : Matrix dA dA ℂ} (hA : Aᴴ = A)
    (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = stateSqNorm ψ A + ‖stateVecB ψ B‖ ^ 2 - 2 * bornProb ψ A B := by
  rw [xSqNorm, norm_sub_sq (𝕜 := ℂ), inner_stateVec_stateVecB ψ hA, stateSqNorm, stateNorm,
    bornProb]
  simp only [RCLike.re_to_complex]
  ring
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
theorem _root_.solution (M : X → POVM Λ dA) (N : X → POVM Λ dB) :
    xDev μ ψ M N = weightA μ ψ M + weightB μ ψ N - 2 * agreeSum μ ψ M N := by
  unfold xDev weightA weightB agreeSum
  have hexp : ∀ x a, xSqNorm ψ (((M x).mats a).val) (((N x).mats a).val)
      = stateSqNorm ψ (((M x).mats a).val) + ‖stateVecB ψ (((N x).mats a).val)‖ ^ 2
        - 2 * bornProb ψ (((M x).mats a).val) (((N x).mats a).val) := fun x a =>
    xSqNorm_eq_expand ψ (by
      rw [← Matrix.star_eq_conjTranspose]; exact selfAdjoint.mem_iff.mp ((M x).mats a).prop) _
  have hx : ∀ x, μ x * ∑ a, xSqNorm ψ (((M x).mats a).val) (((N x).mats a).val)
      = μ x * ∑ a, stateSqNorm ψ (((M x).mats a).val)
        + μ x * ∑ a, ‖stateVecB ψ (((N x).mats a).val)‖ ^ 2
        - 2 * (μ x * ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val)) := by
    intro x
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  simp only [hx, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
end MIPRE
