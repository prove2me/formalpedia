-- Prove2me | solution 1 for MIPRE.CL.Detyping.Program.route_preserves
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:18:29.298984+00:00
-- url     : https://prove2.me/submissions/e53dc0ab-e321-4045-a74a-26e610d13d63

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgRoute.lean (solution of MIPRE.CL.Detyping.Program.route_preserves);
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
theorem routeResult_preserves (g : ℕ) (p : Parsed) (a : GraphResult) (payload : Data)
    (h : routeResult g p a = (true, payload)) :
    ∃ d ctx, payload = .cons (.cons p.1 d) ctx := by
  dsimp only [routeResult] at h
  split_ifs at h <;> simp only [callResult, directResult, typedRequest, Prod.mk.injEq,
    Bool.false_eq_true, false_and, true_and] at h
  all_goals first | contradiction | (subst payload; exact ⟨_, _, rfl⟩)
end
end MIPRE.CL.Detyping.Program

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping.Program
open Cost Cost.PolyTimeFun
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
theorem _root_.solution (E : T → T → Prop) [DecidableRel E] (n : ℕ) (q payload : Data)
    (h : route E (.cons (encode n) q) = (true, payload)) :
    ∃ d ctx, payload = .cons (.cons (encode n) d) ctx := by
  simp only [route, comp_apply, pair_apply, id_apply, routeParsed_apply] at h
  exact routeResult_preserves _ _ _ _ h
end MIPRE.CL.Detyping.Program
