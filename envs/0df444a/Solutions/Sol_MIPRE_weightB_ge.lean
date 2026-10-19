-- Prove2me | solution 1 for MIPRE.weightB_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:36.646983+00:00
-- url     : https://prove2.me/submissions/78b153c0-535d-4677-97d0-5817b04058d5

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMMix.lean (solution of MIPRE.weightB_ge);
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
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Λ : Type*} [Fintype X] [Fintype Λ] {dA dB : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB]
variable {μ : X → ℝ} {ψ : dA × dB → ℂ}
theorem weightA_le_one (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM Λ dA) : weightA μ ψ M ≤ 1 := by
  calc weightA μ ψ M ≤ ∑ x, μ x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (sum_stateSqNorm_le_one hψ (M x)) (hμ x)
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
theorem weightB_nonneg (hμ : ∀ x, 0 ≤ μ x) (N : X → POVM Λ dB) : 0 ≤ weightB μ ψ N :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (Finset.sum_nonneg fun _ _ => by positivity)
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
    1 - 2 * δ ≤ weightB μ ψ N := by
  have hcs := agreeSum_le_sqrt_mul_sqrt (ψ := ψ) hμ M N
  have hA : Real.sqrt (weightA μ ψ M) ≤ 1 :=
    Real.sqrt_le_one.mpr (weightA_le_one hμ hμ1 hψ M)
  have hB0 : 0 ≤ weightB μ ψ N := weightB_nonneg hμ N
  have hsB : agreeSum μ ψ M N ≤ Real.sqrt (weightB μ ψ N) :=
    le_trans hcs (by
      calc Real.sqrt (weightA μ ψ M) * Real.sqrt (weightB μ ψ N)
          ≤ 1 * Real.sqrt (weightB μ ψ N) :=
            mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)
        _ = Real.sqrt (weightB μ ψ N) := one_mul _)
  by_cases hδ : 1 - δ ≤ 0
  · nlinarith
  · have h1 : 1 - δ ≤ Real.sqrt (weightB μ ψ N) := by linarith
    have h2 : (1 - δ) ^ 2 ≤ weightB μ ψ N := by
      have := Real.sq_sqrt hB0
      nlinarith [Real.sqrt_nonneg (weightB μ ψ N)]
    have hsq : 1 - 2 * δ ≤ (1 - δ) ^ 2 := by nlinarith [sq_nonneg δ]
    linarith
end MIPRE
