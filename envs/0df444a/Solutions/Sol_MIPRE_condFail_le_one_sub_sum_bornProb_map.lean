-- Prove2me | solution 1 for MIPRE.condFail_le_one_sub_sum_bornProb_map
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:27:27.650827+00:00
-- url     : https://prove2.me/submissions/219b2453-7574-4486-98cf-7abf1299de2e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMMix.lean (solution of MIPRE.condFail_le_one_sub_sum_bornProb_map);
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
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_sum_bornProb_map

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_zero_left (ψ : dA × dB → ℂ) (EB : Matrix dB dB ℂ) : bornProb ψ 0 EB = 0 := by
  rw [bornProb, Matrix.zero_kronecker, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_zero_right (ψ : dA × dB → ℂ) (EA : Matrix dA dA ℂ) : bornProb ψ EA 0 = 0 := by
  rw [bornProb, Matrix.kronecker_zero, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {X Y A B C : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq C] {ψ : dA × dB → ℂ} {x : X} {y : Y}
theorem _root_.solution {G : Game X Y A B} {MA : X → POVM A dA}
    {MB : Y → POVM B dB} (f : A → C) (g : B → C)
    (hD : ∀ a b, ((MA x).mats a).val ≠ 0 → ((MB y).mats b).val ≠ 0 → f a = g b →
      G.D x y a b = true) :
    condFail G ψ MA MB x y
      ≤ 1 - ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val) := by
  classical
  rw [sum_bornProb_map, condFail]
  have hle : ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
      * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) ≤ condWin G ψ MA MB x y := by
    rw [condWin]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    by_cases hfg : f a = g b
    · rw [if_pos hfg]
      by_cases hA : ((MA x).mats a).val = 0
      · rw [hA, bornProb_zero_left, mul_zero, mul_zero]
      by_cases hB : ((MB y).mats b).val = 0
      · rw [hB, bornProb_zero_right, mul_zero, mul_zero]
      rw [if_pos (hD a b hA hB hfg)]
    · rw [if_neg hfg, zero_mul]
      exact mul_nonneg (by split_ifs <;> norm_num)
        (bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b))
  linarith
end MIPRE
