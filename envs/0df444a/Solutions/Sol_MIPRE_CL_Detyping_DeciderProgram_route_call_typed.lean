-- Prove2me | solution 1 for MIPRE.CL.Detyping.DeciderProgram.route_call_typed
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:02:36.634996+00:00
-- url     : https://prove2.me/submissions/98f0877f-9750-4041-a1cc-44898c1825c3

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingDeciderCost.lean (solution of MIPRE.CL.Detyping.DeciderProgram.route_call_typed);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
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
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping.DeciderProgram
open Cost Cost.PolyTimeFun Detyping.Program Pipeline
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable (E : T → T → Prop) [DecidableRel E]
theorem _root_.solution (n s inner outer : ℕ) (d payload : Data)
    (h : route E (context (.cons (encode n) d) s inner outer) = (true, payload)) :
    ∃ (u v : T) (x y a b : BitStr), payload = .cons (encode (n, u, x, v, y, a, b)) .nil ∧
      x.length = s ∧ y.length = s ∧ a.length ≤ inner ∧ b.length ≤ inner := by
  rw [route_apply] at h
  dsimp only [routeResult] at h
  have hn : indexReader (context (.cons (encode n) d) s inner outer) = n := by
    simp [indexReader, inputReader, context, readNat_encode]
  have hs : dimensionReader (context (.cons (encode n) d) s inner outer) = s := by
    simp [dimensionReader, context, readNat_encode]
  have hi : innerReader (context (.cons (encode n) d) s inner outer) = inner := by
    simp [innerReader, context, encode_prod, readNat_encode]
  split_ifs at h with hc h2 h3
  · obtain ⟨-, hx, hy, -, -⟩ := hc
    obtain ⟨ha, hb⟩ := h3
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    set x := xReader (context (.cons (encode n) d) s inner outer)
    set y := yReader (context (.cons (encode n) d) s inner outer)
    rw [hn]
    rw [hs] at hx hy
    rw [hi] at ha hb
    cases hsel : selectedEdge E (graphOfBits x) (graphOfBits y) with
    | none => simp [edgeData, hsel, rawTruth] at h2
    | some uv =>
      refine ⟨uv.1, uv.2, x.drop (graphDim T), y.drop (graphDim T), _, _, ?_, by simp [hx],
        by simp [hy], ha, hb⟩
      simp only [edgeData, hsel, treeHead_cons, treeTail_cons]
      rfl
  all_goals simp at h
end MIPRE.CL.Detyping.DeciderProgram
