-- Prove2me | solution 1 for MIPRE.CL.Detyping.DeciderProgram.route_context
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:20:41.232028+00:00
-- url     : https://prove2.me/submissions/558bcd90-e38a-479c-9c4b-0dd42062ed6d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingDeciderRoute.lean (solution of MIPRE.CL.Detyping.DeciderProgram.route_context);
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
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode
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
open Cost Cost.PolyTimeFun Detyping.Program
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
theorem _root_.solution (E : T → T → Prop) [DecidableRel E]
    (n s inner outer : ℕ) (x y a b : BitStr) :
    route E (context (encode (n, x, y, a, b)) s inner outer) =
      if x.length = graphDim T + s ∧ y.length = graphDim T + s ∧
          a.length ≤ outer ∧ b.length ≤ outer then
        match selectedEdge E (graphOfBits x) (graphOfBits y) with
        | none => (false, encode true)
        | some uv => if a.length ≤ inner ∧ b.length ≤ inner then
            (true, .cons (encode (n, uv.1, x.drop (graphDim T), uv.2, y.drop (graphDim T), a, b)) .nil)
          else (false, encode false)
      else (false, encode false) := by
  rw [route_apply]
  simp only [routeResult, context, inputReader, indexReader, xReader, yReader, aReader, bReader,
    dimensionReader, innerReader, outerReader, comp_apply, encode_prod, treeHead_cons, treeTail_cons,
    readNat_encode, readBits_encode, true_and]
  cases h : selectedEdge E (graphOfBits x) (graphOfBits y) <;>
    simp [edgeData, h, rawTruth, typedArgument, encode_prod]
end MIPRE.CL.Detyping.DeciderProgram
