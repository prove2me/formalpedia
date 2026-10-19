-- Prove2me | solution 1 for MIPRE.CL.Detyping.Program.route_marginal_late
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:22:21.896253+00:00
-- url     : https://prove2.me/submissions/754578d3-9f31-41bb-a564-a0323307c2e5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgBranches.lean (solution of MIPRE.CL.Detyping.Program.route_marginal_late);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
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
import Theorems.Thm_MIPRE_CL_Detyping_Program_parse_query

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.Detyping.Program
noncomputable section
open Cost Cost.PolyTimeFun
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
theorem routeParsed_apply (g : ℕ) (p : Parsed) (a : GraphResult) :
    routeParsed g (p, a) = routeResult g p a := by
  have hf : (const false : PolyTimeFun Bool Bool).toFun = fun _ => false := rfl
  have ht : (const true : PolyTimeFun Bool Bool).toFun = fun _ => true := rfl
  simp only [routeParsed, routeResult, pIndex, pKind, pPlayer, pLevel, pU, pY,
    directP, callP, prefixP, directResult, callResult, typedRequest, withPrefix,
    ap₂_apply, PolyTimeFun.ite_apply, pair_apply, comp_apply, fst_apply, snd_apply, const_apply,
    treePair_apply, encoded_apply, SAT.ArrayProg.eqNat_apply, leNat_apply,
    subUnary_apply, drop_apply, length_unary, map_apply, append_apply,
    rawTruthProg, decide_eq_true_eq, content, pad, hf, ht]
  split_ifs <;> simp_all
end
end MIPRE.CL.Detyping.Program

namespace MIPRE.CL.Detyping.Program
noncomputable section
open Cost Cost.PolyTimeFun
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable (E : T → T → Prop) [DecidableRel E]
theorem route_query (n : ℕ) (q : Sampler.Query) :
    route E (encode (n, q)) =
      routeResult (graphDim T)
        (encode n, q.toTuple.1, q.toTuple.2.1.toBool, q.toTuple.2.2.1,
          q.toTuple.2.2.2.1, q.toTuple.2.2.2.2)
        (graphResult E (q.toTuple.2.1.toBool, decide (q.toTuple.2.2.1 = 1),
          ofBits (graphDim T) q.toTuple.2.2.2.1, ofBits (graphDim T) q.toTuple.2.2.2.2)) := by
  simp only [route, comp_apply, pair_apply, id_apply, parse_query, routeParsed_apply]
  rfl
end
end MIPRE.CL.Detyping.Program

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping.Program
open Cost Cost.PolyTimeFun
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable (E : T → T → Prop) [DecidableRel E]
theorem _root_.solution (n : ℕ) (w : Player) (j : ℕ) (z : BitStr) (hj : 2 < j) :
    route E (encode (n, Sampler.Query.marginal w j z)) =
      match select E w.toBool (graphOfBits z) with
      | none => directResult (graphBits ((Graph.presentation E w.toBool).eval (graphOfBits z)) ++
          pad false (content (graphDim T) z))
      | some t => callResult
          (encode (n, TypedSampler.Query.atType t
            (Sampler.Query.marginal w (j - 2) (content (graphDim T) z))))
          (withPrefix (graphBits ((Graph.presentation E w.toBool).eval (graphOfBits z)))) := by
  rw [route_query]
  have hj1 : j ≠ 1 := by omega
  have hj2 : ¬j ≤ 2 := by omega
  simp only [routeResult, graphResult, Sampler.Query.toTuple, hj1, decide_false,
    Bool.false_eq_true, ↓reduceIte, hj2]
  change (if rawTruth (match select E w.toBool (graphOfBits z) with
      | none => Data.nil | some t => .cons (encode t) .nil) then _ else _) = _
  cases ht : select E w.toBool (graphOfBits z)
  all_goals simp only [graphOfBits] at ht
  all_goals simp only [ht, rawTruth, ↓reduceIte, Bool.false_eq_true,
    treeHead_cons]
  all_goals rfl
end MIPRE.CL.Detyping.Program
