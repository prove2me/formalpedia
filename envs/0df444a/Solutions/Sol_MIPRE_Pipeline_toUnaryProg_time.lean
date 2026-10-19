-- Prove2me | solution 1 for MIPRE.Pipeline.toUnaryProg_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:00.747224+00:00
-- url     : https://prove2.me/submissions/d2d70911-9965-4fba-9d5c-7784969ff4e0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pipeline/PowDomRun.lean (solution of MIPRE.Pipeline.toUnaryProg_time);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_seqProg_runs
import Theorems.Thm_MIPRE_Cost_whileProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost
section
open PolyTimeFun
theorem whileProg_closed (f : PolyTimeFun Data (Bool × Data)) : (whileProg f).WellScoped 1 :=
  ⟨Nat.zero_lt_one, f.closed⟩
end
end MIPRE.Cost

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem toUnaryStep_zero (acc : Unary) :
    toUnaryStep (encode ((0 : ℕ), acc)) = (false, encode acc) := by
  simp [toUnaryStep, encode_prod, readNat_encode]
end
end MIPRE.Pipeline

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem toUnaryStep_succ (x : ℕ) (acc : Unary) :
    toUnaryStep (encode (x + 1, acc)) = (true, encode (x, () :: acc)) := by
  simp [toUnaryStep, encode_prod, readNat_encode]
end
end MIPRE.Pipeline

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem esize_nat_le_four (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := x)); omega)
end
end MIPRE.Pipeline

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem sum_range_le_mul {N B : ℕ} {f : ℕ → ℕ} (h : ∀ i ≤ N, f i ≤ B) :
    ∑ i ∈ Finset.range (N + 1), f i ≤ (N + 1) * B := by
  calc ∑ i ∈ Finset.range (N + 1), f i ≤ ∑ _i ∈ Finset.range (N + 1), B :=
        Finset.sum_le_sum fun i hi => h i (by simp at hi; omega)
    _ = (N + 1) * B := by simp
end
end MIPRE.Pipeline

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Pipeline
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem _root_.solution (x : ℕ) :
    ∃ t ≤ toUnaryInit.timeBound.eval (4 * x + 1) +
        (x + 1) * (toUnaryStep.timeBound.eval (4 * x + 3) + 1) + 1,
      toUnaryProg.Runs (encode x) (encode (unary x)) t := by
  obtain ⟨t₀, ht₀, h₀⟩ := toUnaryInit.computes (encode x)
  have hi : toUnaryInit (encode x) = encode (x, ([] : Unary)) := by simp [readNat_encode]
  rw [hi] at h₀
  obtain ⟨t, ht, hrun⟩ := whileProg_runs toUnaryStep x (fun i => encode (x - i, unary i))
    (encode (unary x)) (fun i hi => by
      obtain ⟨y, hy⟩ : ∃ y, x - i = y + 1 := ⟨x - i - 1, by omega⟩
      rw [hy, toUnaryStep_succ, show x - (i + 1) = y by omega]
      simp [unary, List.replicate_succ])
    (by simp only [Nat.sub_self, toUnaryStep_zero])
  refine ⟨_, ?_, seqProg_runs (whileProg_closed _) h₀ (by simpa [unary] using hrun)⟩
  have h1 : t₀ ≤ toUnaryInit.timeBound.eval (4 * x + 1) :=
    ht₀.trans (polynomial_eval_mono _ (esize_nat_le_four x))
  have h2 : t ≤ (x + 1) * (toUnaryStep.timeBound.eval (4 * x + 3) + 1) := by
    refine ht.trans (sum_range_le_mul fun i hi => Nat.add_le_add_right
      (polynomial_eval_mono _ ?_) 1)
    have := esize_nat_le_four (x - i)
    simp only [encode_prod, Data.size_cons]
    change esize (x - i) + esize (unary i) + 1 ≤ _
    rw [esize_unary]
    omega
  omega
end MIPRE.Pipeline
