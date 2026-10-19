-- Prove2me | solution 1 for MIPRE.IsPVM.marg_left
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:21:59.626578+00:00
-- url     : https://prove2.me/submissions/1207dcb7-75d3-47e7-bb82-4653490287c9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (solution of MIPRE.IsPVM.marg_left);
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
import Theorems.Thm_MIPRE_IsPVM_orthogonal

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N B C : Type*} [Fintype N] [DecidableEq N] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
/-- The marginal over `C`, as the coarse-graining of `P` that forgets the second outcome. -/
theorem IsPVM.sum_marg_left {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    ∑ b, (∑ c, P (b, c)) = 1 := by
  rw [← Fintype.sum_prod_type]
  exact h.sum_eq_one
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.IsPVM
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N B C : Type*} [Fintype N] [DecidableEq N] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
theorem _root_.solution {P : B × C → Matrix N N ℂ} (h : IsPVM P) :
    IsPVM fun b => ∑ c, P (b, c) where
  isSelfAdjoint b := by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun c _ => h.isSelfAdjoint (b, c)
  idem b := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single c (fun c' _ hc' => ?_)
      fun hmem => absurd (Finset.mem_univ c) hmem]
    · exact h.idem (b, c)
    · exact h.orthogonal fun he => hc' (Prod.mk.injEq .. ▸ he).2.symm
  sum_eq_one := h.sum_marg_left
end MIPRE.IsPVM
