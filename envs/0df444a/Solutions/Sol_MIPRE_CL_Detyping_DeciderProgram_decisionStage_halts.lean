-- Prove2me | solution 1 for MIPRE.CL.Detyping.DeciderProgram.decisionStage_halts
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:47:38.933593+00:00
-- url     : https://prove2.me/submissions/8c84ce7c-d6d3-425b-a06f-56cfacecf6af

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingDeciderProg.lean (solution of MIPRE.CL.Detyping.DeciderProgram.decisionStage_halts);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_decisionStage_direct
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_decisionStage_indirect

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Cost.PolyTimeFun Detyping.Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
theorem route_apply (E : T → T → Prop) [DecidableRel E] (c : Data) : route E c = routeResult E c := by
  simp only [route, routeResult, edgeAction, ap₂_apply, comp_apply, pair_apply,
    const_apply, encoded_apply, treePair_apply, treeEq_apply, SAT.ArrayProg.eqNat_apply,
    lengthNat_apply, leNat_apply, addUnary_apply, length_unary, drop_apply, finiteFunction_apply,
    readVector_apply, PolyTimeFun.ite_apply, graphOfBits, rawTruthProg, typedArgument,
    decide_eq_true_eq]
  simp only [Nat.add_comm]
  split_ifs <;> simp_all
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Cost.PolyTimeFun Detyping.Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
/-- Successful routing preserves the normalized original index on all raw input trees. -/
theorem route_preserves (E : T → T → Prop) [DecidableRel E] (c payload : Data)
    (h : route E c = (true, payload)) :
    ∃ d ctx, payload = .cons (.cons (encode (indexReader c)) d) ctx := by
  rw [route_apply] at h
  dsimp only [routeResult] at h
  split_ifs at h <;> simp only [Prod.mk.injEq, Bool.false_eq_true, false_and, true_and] at h
  all_goals first | contradiction | (subst payload; exact ⟨_, _, rfl⟩)
end
end MIPRE.CL.Detyping.DeciderProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping.DeciderProgram
open Cost Cost.PolyTimeFun Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
theorem _root_.solution (hD : D.Total) (c : Data) : Halts (decisionStage E D) c := by
  cases h : route E c with
  | mk call payload =>
    cases call with
    | false =>
      obtain ⟨time, hr⟩ := decisionStage_direct E D c payload h
      exact ⟨_, time, hr⟩
    | true =>
      obtain ⟨d, ctx, rfl⟩ := route_preserves E c payload h
      obtain ⟨r, time, hr⟩ := hD (indexReader c) d
      obtain ⟨t, ht⟩ := decisionStage_indirect E D c _ ctx r time h hr
      exact ⟨_, t, ht⟩
end MIPRE.CL.Detyping.DeciderProgram
