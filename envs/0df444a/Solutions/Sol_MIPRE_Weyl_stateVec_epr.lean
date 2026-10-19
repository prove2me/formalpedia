-- Prove2me | solution 1 for MIPRE.Weyl.stateVec_epr
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:43:22.480201+00:00
-- url     : https://prove2.me/submissions/f8e34a7f-bf69-4f54-a017-e7e6f8365917

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/WeylEPR.lean (solution of MIPRE.Weyl.stateVec_epr);
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
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_WeylEPR

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

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem stateVec_entry (ψ : (n → F) × (n → F) → ℂ) (M : Matrix (n → F) (n → F) ℂ)
    (a b : n → F) :
    ((M ⊗ₖ (1 : Matrix (n → F) (n → F) ℂ)) *ᵥ ψ) (a, b) = ∑ k, M a k * ψ (k, b) := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_ite_eq, mul_comm]
end
end MIPRE.Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Weyl
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem _root_.solution (M : Matrix (n → F) (n → F) ℂ) :
    stateVec (epr (F := F) (n := n)) M = stateVecB epr Mᵀ := by
  classical
  show WithLp.toLp 2 _ = WithLp.toLp 2 _
  congr 1
  funext p
  obtain ⟨a, b⟩ := p
  rw [stateVec_entry, stateVecB_entry,
    Finset.sum_eq_single b (fun k _ hk => by rw [epr_ne hk, mul_zero])
      fun hmem => absurd (Finset.mem_univ b) hmem,
    Finset.sum_eq_single a (fun l _ hl => by rw [epr_ne (Ne.symm hl), mul_zero])
      fun hmem => absurd (Finset.mem_univ a) hmem,
    Matrix.transpose_apply, epr_same, epr_same]
end MIPRE.Weyl
