-- Prove2me | solution 1 for MIPRE.quadForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:38.601586+00:00
-- url     : https://prove2.me/submissions/c2fec81e-19ea-47dd-8ed7-611289aa6618

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/StateDistance.lean (solution of MIPRE.quadForm_eq);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    star ψ ⬝ᵥ ((((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ) = (stateSqNorm ψ M : ℂ) := by
  classical
  set A : Matrix (dA × dB) (dA × dB) ℂ := M ⊗ₖ (1 : Matrix dB dB ℂ) with hA
  have hAdj : Aᴴ * A = (Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ) := by
    rw [hA, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have h1 : star (A *ᵥ ψ) ⬝ᵥ (A *ᵥ ψ) = star ψ ⬝ᵥ ((Aᴴ * A) *ᵥ ψ) :=
    star_mulVec_dotProduct A A ψ
  rw [← hAdj, ← h1, dotProduct]
  have hentry : ∀ i, star (A *ᵥ ψ) i * (A *ᵥ ψ) i = ((‖(A *ᵥ ψ) i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hentry i, ← Complex.ofReal_sum]
  show _ = ((‖stateVec ψ M‖ ^ 2 : ℝ) : ℂ)
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl
end MIPRE
