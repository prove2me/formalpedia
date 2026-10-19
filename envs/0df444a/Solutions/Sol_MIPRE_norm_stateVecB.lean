-- Prove2me | solution 1 for MIPRE.norm_stateVecB
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:36:38.647731+00:00
-- url     : https://prove2.me/submissions/47cdff37-519d-4ee1-9426-068b982797bc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/StateDistance.lean (solution of MIPRE.norm_stateVecB);
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
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] in
theorem _root_.solution (ψ : dA × dB → ℂ) (N : Matrix dB dB ℂ) :
    ‖stateVecB ψ N‖ = stateNorm (swapVec ψ) N := by
  classical
  rw [stateNorm, stateVecB, stateVec, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm dA dB) _ _ fun p => ?_
  obtain ⟨i, j⟩ := p
  show ‖(((1 : Matrix dA dA ℂ) ⊗ₖ N) *ᵥ ψ) (i, j)‖ ^ 2
      = ‖((N ⊗ₖ (1 : Matrix dA dA ℂ)) *ᵥ swapVec ψ) (j, i)‖ ^ 2
  rw [stateVecB_entry, stateVec_swapVec_entry]
end MIPRE
