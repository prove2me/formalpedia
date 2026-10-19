-- Prove2me | solution 1 for MIPRE.condFail_le_one_sub_sum_bornProb_diag
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:29:28.167479+00:00
-- url     : https://prove2.me/submissions/921930a3-4eca-45c4-94be-664902e4aa9e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMMix.lean (solution of MIPRE.condFail_le_one_sub_sum_bornProb_diag);
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
theorem _root_.solution {G : Game X Y A A} {MA : X → POVM A dA}
    {MB : Y → POVM A dB}
    (hD : ∀ a, ((MA x).mats a).val ≠ 0 → ((MB y).mats a).val ≠ 0 → G.D x y a a = true) :
    condFail G ψ MA MB x y
      ≤ 1 - ∑ a, bornProb ψ (((MA x).mats a).val) (((MB y).mats a).val) := by
  classical
  rw [condFail]
  have hle : ∑ a, bornProb ψ (((MA x).mats a).val) (((MB y).mats a).val)
      ≤ condWin G ψ MA MB x y := by
    rw [condWin]
    refine Finset.sum_le_sum fun a _ => ?_
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun b => (if G.D x y a b then (1 : ℝ) else 0)
        * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val))
      (fun b _ => mul_nonneg (by split_ifs <;> norm_num)
        (bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b))) (Finset.mem_univ a))
    by_cases hA : ((MA x).mats a).val = 0
    · rw [hA, bornProb_zero_left, mul_zero]
    by_cases hB : ((MB y).mats a).val = 0
    · rw [hB, bornProb_zero_right, mul_zero]
    rw [if_pos (hD a hA hB), one_mul]
  linarith
end MIPRE
