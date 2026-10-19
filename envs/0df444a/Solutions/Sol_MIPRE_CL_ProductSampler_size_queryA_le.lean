-- Prove2me | solution 1 for MIPRE.CL.ProductSampler.size_queryA_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:47.069681+00:00
-- url     : https://prove2.me/submissions/d6656df1-9702-454f-b88b-3d347e078fe8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSamplerCost.lean (solution of MIPRE.CL.ProductSampler.size_queryA_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
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
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
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
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
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
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerCost

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem esize_nat_le_four (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := x)); omega)
end
end MIPRE.Pipeline

namespace MIPRE.CL.ProductSampler
section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
theorem size_treeHead_le (d : Data) : (treeHead d).size ≤ d.size := by
  cases d with
  | nil => exact le_refl _
  | cons a b => simp only [treeHead_cons, Data.size_cons]; omega
end
end MIPRE.CL.ProductSampler

namespace MIPRE.CL.ProductSampler
section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
theorem size_treeTail_le (d : Data) : (treeTail d).size ≤ d.size := by
  cases d with
  | nil => exact le_refl _
  | cons a b => simp only [treeTail_cons, Data.size_cons]; omega
end
end MIPRE.CL.ProductSampler

namespace MIPRE.CL.ProductSampler
section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
theorem length_rawList_le (d : Data) : (rawList d).length ≤ d.size := by
  induction d with
  | nil => simp [rawList]
  | cons a b _ ihb => simp only [rawList, List.length_cons, Data.size_cons]; omega
end
end MIPRE.CL.ProductSampler

namespace MIPRE.CL.ProductSampler
section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
theorem length_readBits_le (d : Data) : (readBits d).length ≤ d.size := by
  change ((rawList d).map rawTruth).length ≤ _
  rw [List.length_map]
  exact length_rawList_le d
end
end MIPRE.CL.ProductSampler

namespace MIPRE.CL.ProductSampler
section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)
/-- `A`'s half of a vector read off the query is no longer than the query. -/
theorem length_leftBits_le (l : PolyTimeFun Data BitStr) (x : Data) :
    (leftBits D l x).length ≤ (l x).length := by
  simp only [leftBits, comp_apply, pair_apply, reverse_apply, drop_apply, List.length_reverse,
    List.length_drop]
  omega
end
end MIPRE.CL.ProductSampler

namespace MIPRE.CL.ProductSampler
section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)
/-- The vectors of the parsed query are no longer than the typed query. -/
theorem length_uD_le (pdn H nD' q : Data) :
    (uD (.cons pdn (.cons H (.cons nD' q)))).length ≤ q.size := by
  simp only [uD, parsedQ, pU, comp_apply, parse, pair_apply, ap₂_apply, treePair_apply, nD, qD,
    queryD, treeTail_cons, treeHead_cons, fst_apply, snd_apply]
  refine (length_readBits_le _).trans ?_
  have h1 := size_treeHead_le (treeTail (treeTail (treeTail (treeTail q))))
  have h2 := size_treeTail_le (treeTail (treeTail (treeTail q)))
  have h3 := size_treeTail_le (treeTail (treeTail q))
  have h4 := size_treeTail_le (treeTail q)
  have h5 := size_treeTail_le q
  omega
end
end MIPRE.CL.ProductSampler

namespace MIPRE.CL.ProductSampler
section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)
theorem length_yD_le (pdn H nD' q : Data) :
    (yD (.cons pdn (.cons H (.cons nD' q)))).length ≤ q.size := by
  simp only [yD, parsedQ, pY, comp_apply, parse, pair_apply, ap₂_apply, treePair_apply, nD, qD,
    queryD, treeTail_cons, treeHead_cons, snd_apply]
  refine (length_readBits_le _).trans ?_
  have h1 := size_treeTail_le (treeTail (treeTail (treeTail (treeTail q))))
  have h2 := size_treeTail_le (treeTail (treeTail (treeTail q)))
  have h3 := size_treeTail_le (treeTail (treeTail q))
  have h4 := size_treeTail_le (treeTail q)
  have h5 := size_treeTail_le q
  omega
end
end MIPRE.CL.ProductSampler

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.ProductSampler
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)
theorem _root_.solution (j : PolyTimeFun Data ℕ) (ap pp : Prog) (ℓa n : ℕ) (pdn q : Data)
    (hj : j (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) ≤ ℓa) :
    (queryA D j (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q)))).size ≤
      esize n + 12 * q.size + 4 * ℓa + 20 := by
  set x : Data := .cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))
  have hu := (esize_bitStr_le (leftBits D uD x)).trans
    (by
      have := length_leftBits_le D uD x
      have : (uD x).length ≤ q.size := length_uD_le pdn _ _ q
      omega :
      4 * (leftBits D uD x).length + 1 ≤ 4 * q.size + 1)
  have hy := (esize_bitStr_le (leftBits D yD x)).trans
    (by
      have := length_leftBits_le D yD x
      have : (yD x).length ≤ q.size := length_yD_le pdn _ _ q
      omega :
      4 * (leftBits D yD x).length + 1 ≤ 4 * q.size + 1)
  have hjs := (esize_nat_le_four (j x)).trans (by omega : 4 * j x + 1 ≤ 4 * ℓa + 1)
  have h1 := size_treeHead_le (treeHead q)
  have h2 := size_treeHead_le q
  have h3 := size_treeHead_le (treeTail q)
  have h4 := size_treeTail_le q
  have h5 := size_treeHead_le (treeTail (treeTail q))
  have h6 := size_treeTail_le (treeTail q)
  simp only [queryA, ap₂_apply, treePair_apply, comp_apply, encoded_apply, nD, tagD, qD,
    queryD, treeTail_cons, treeHead_cons, Data.size_cons, x] at hu hy hjs ⊢
  change esize n + ((treeHead (treeHead q)).size + ((treeHead (treeTail q)).size +
    ((treeHead (treeTail (treeTail q))).size + (esize (j _) + (esize (leftBits D uD _) +
      esize (leftBits D yD _) + 1) + 1) + 1) + 1) + 1) + 1 ≤ _
  omega
end MIPRE.CL.ProductSampler
