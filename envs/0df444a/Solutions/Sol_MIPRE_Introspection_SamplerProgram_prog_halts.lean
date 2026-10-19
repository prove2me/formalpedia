-- Prove2me | solution 1 for MIPRE.Introspection.SamplerProgram.prog_halts
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:16:40.852643+00:00
-- url     : https://prove2.me/submissions/67740c60-c9e2-4281-8cec-c80ca80531d2

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SamplerProgram.lean (solution of MIPRE.Introspection.SamplerProgram.prog_halts);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
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
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_SamplerProgram
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_halts

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.SamplerProgram
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program
theorem aux_apply (p : Parsed) : aux p = auxResult p := by
  have hf : (const false : PolyTimeFun Bool Bool).toFun = fun _ => false := rfl
  have ht : (const true : PolyTimeFun Bool Bool).toFun = fun _ => true := rfl
  simp only [aux, auxResult, pKind, pLevel, pU, pY, pad, PolyTimeFun.ite_apply,
    ap₂_apply, SAT.ArrayProg.eqNat_apply, const_apply, comp_apply, map_apply,
    fst_apply, snd_apply, decide_eq_true_eq, hf, ht]
  split_ifs <;> simp_all
end
end MIPRE.Introspection.SamplerProgram

namespace MIPRE.Introspection.SamplerProgram
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program
theorem route_apply (x : Data) : route x = routeResult x := by
  simp only [route, routeResult, PolyTimeFun.ite_apply, comp_apply, pair_apply, const_apply,
    ap₂_apply, treePair_apply, encoded_apply, aux_apply, directResult, callResult,
    rawTruthProg]
end
end MIPRE.Introspection.SamplerProgram

namespace MIPRE.Introspection.SamplerProgram
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program
theorem route_preserves (n : ℕ) (q a : Data)
    (h : route (.cons (encode n) q) = (true, a)) :
    ∃ d ctx, a = .cons (.cons (encode n) d) ctx := by
  rw [route_apply] at h
  simp only [routeResult, treeHead_cons, treeTail_cons] at h
  by_cases hq : rawTruth q = true
  · by_cases ht : rawTruth (treeHead (treeHead q)) = true
    · simp [hq, ht, directResult] at h
    · simp [hq, ht, callResult] at h
      exact ⟨_, .nil, h.symm⟩
  · simp [hq, callResult] at h
    exact ⟨.nil, .nil, h.symm⟩
end
end MIPRE.Introspection.SamplerProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.SamplerProgram
open Cost Cost.PolyTimeFun CL CL.Detyping.Program
theorem _root_.solution {P : Type*} [SizedEncoding P] (S : TypedSampler 3 P) (n : ℕ) (d : Data) :
    Halts (prog S) (.cons (encode n) d) :=
  Prog.routeOneCall_halts _ S.closed _ n d (S.halts n) (route_preserves n d)
end MIPRE.Introspection.SamplerProgram
