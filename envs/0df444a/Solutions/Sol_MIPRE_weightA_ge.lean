-- Prove2me | solution 1 for MIPRE.weightA_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:35.953333+00:00
-- url     : https://prove2.me/submissions/7008f700-4fc2-44e6-bd52-1804c8fda24a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMMix.lean (solution of MIPRE.weightA_ge);
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
import Theorems.Thm_MIPRE_agreeSum_le_sqrt_mul_sqrt
import Theorems.Thm_MIPRE_sum_stateSqNorm_le_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
theorem weightB_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (N : X → POVM Λ dB) : weightB μ ψ N ≤ 1 := by
  calc weightB μ ψ N ≤ ∑ x, μ x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (sum_stateSqNormB_le_one hψ (N x)) (hμ x)
    _ = 1 := by simp [hμ1]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
theorem weightA_nonneg (hμ : ∀ x, 0 ≤ μ x) (M : X → POVM Λ dA) : 0 ≤ weightA μ ψ M :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (Finset.sum_nonneg fun _ _ => by
    rw [stateSqNorm]; positivity)
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
theorem _root_.solution (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) (N : X → POVM Λ dB) {δ : ℝ} (h : 1 - agreeSum μ ψ M N ≤ δ) :
    1 - 2 * δ ≤ weightA μ ψ M := by
  have hcs := agreeSum_le_sqrt_mul_sqrt (ψ := ψ) hμ M N
  have hB : Real.sqrt (weightB μ ψ N) ≤ 1 :=
    Real.sqrt_le_one.mpr (weightB_le_one hμ hμ1 hψ N)
  have hA0 : 0 ≤ weightA μ ψ M := weightA_nonneg hμ M
  have hsA : agreeSum μ ψ M N ≤ Real.sqrt (weightA μ ψ M) :=
    le_trans hcs (by
      calc Real.sqrt (weightA μ ψ M) * Real.sqrt (weightB μ ψ N)
          ≤ Real.sqrt (weightA μ ψ M) * 1 :=
            mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)
        _ = Real.sqrt (weightA μ ψ M) := mul_one _)
  by_cases hδ : 1 - δ ≤ 0
  · nlinarith
  · have h1 : 1 - δ ≤ Real.sqrt (weightA μ ψ M) := by linarith
    have h2 : (1 - δ) ^ 2 ≤ weightA μ ψ M := by
      have := Real.sq_sqrt hA0
      nlinarith [Real.sqrt_nonneg (weightA μ ψ M)]
    have hsq : 1 - 2 * δ ≤ (1 - δ) ^ 2 := by nlinarith [sq_nonneg δ]
    linarith
end MIPRE
