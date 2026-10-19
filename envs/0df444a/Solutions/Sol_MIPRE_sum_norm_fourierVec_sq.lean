-- Prove2me | solution 1 for MIPRE.sum_norm_fourierVec_sq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:41:25.13583+00:00
-- url     : https://prove2.me/submissions/e97070f3-70fc-49a0-b7da-a1b56330418a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Parseval.lean (solution of MIPRE.sum_norm_fourierVec_sq);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Theorems.Thm_MIPRE_sum_norm_fourierVecRaw_sq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem fourierVec_eq_smul (T : (n → F) → (N → ℂ)) (e : n → F) :
    fourierVec T e = (Fintype.card (n → F) : ℂ)⁻¹ • fourierVecRaw T e := rfl
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix MIPRE.Weyl
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem _root_.solution (T : (n → F) → (N → ℂ)) :
    ∑ e : n → F, ‖evec (fourierVec T e)‖ ^ 2
      = (Fintype.card (n → F) : ℝ)⁻¹ * ∑ a : n → F, ‖evec (T a)‖ ^ 2 := by
  classical
  have hNR : (Fintype.card (n → F) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos (α := n → F)).ne'
  have hraw := sum_norm_fourierVecRaw_sq T
  have hscale : ∀ e : n → F, ‖evec (fourierVec T e)‖ ^ 2
      = ((Fintype.card (n → F) : ℝ)⁻¹ * (Fintype.card (n → F) : ℝ)⁻¹)
        * ‖evec (fourierVecRaw T e)‖ ^ 2 := by
    intro e
    rw [fourierVec_eq_smul, show evec ((Fintype.card (n → F) : ℂ)⁻¹ • fourierVecRaw T e)
        = (Fintype.card (n → F) : ℂ)⁻¹ • evec (fourierVecRaw T e) from rfl,
      norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
    ring
  rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) => hscale e, ← Finset.mul_sum, hraw]
  field_simp
end MIPRE
