-- Prove2me | solution 1 for MIPRE.one_sub_sum_bornProb_le_condFail
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:04.85121+00:00
-- url     : https://prove2.me/submissions/23432419-9148-49c8-9882-775b25b64bae

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (solution of MIPRE.one_sub_sum_bornProb_le_condFail);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_sum_bornProb_map

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq dA] [DecidableEq dB] in
theorem bornProb_nonneg (ψ : dA × dB → ℂ) {EA : Matrix dA dA ℂ} {EB : Matrix dB dB ℂ}
    (hA : EA.PosSemidef) (hB : EB.PosSemidef) : 0 ≤ bornProb ψ EA EB :=
  (Complex.nonneg_iff.mp ((hA.kronecker hB).dotProduct_mulVec_nonneg ψ)).1
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem _root_.solution {x : X} {y : Y} (f : A → C) (g : B → C)
    (hD : ∀ a b, G.D x y a b = true → f a = g b) :
    1 - ∑ c, bornProb ψ ((((MA x).map f).mats c).val) ((((MB y).map g).mats c).val)
      ≤ condFail G ψ MA MB x y := by
  classical
  have hle : condWin G ψ MA MB x y
      ≤ ∑ a, ∑ b, (if f a = g b then (1 : ℝ) else 0)
          * bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) := by
    rw [condWin]
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    have h0 : 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) :=
      bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
    by_cases h : G.D x y a b = true
    · rw [if_pos h, if_pos (hD a b h)]
    · rw [if_neg h, zero_mul]
      exact mul_nonneg (by split_ifs <;> norm_num) h0
  rw [sum_bornProb_map, condFail]
  linarith
end MIPRE
