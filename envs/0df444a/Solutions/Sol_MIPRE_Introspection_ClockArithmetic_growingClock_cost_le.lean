-- Prove2me | solution 1 for MIPRE.Introspection.ClockArithmetic.growingClock_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:46:24.457211+00:00
-- url     : https://prove2.me/submissions/b979bafa-ad1e-44bf-b178-a29c7730eeb4

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ClockCost.lean (solution of MIPRE.Introspection.ClockArithmetic.growingClock_cost_le);
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
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
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
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
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
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingClock
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Introspection_ClockArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.ClockArithmetic
noncomputable section
open Cost Polynomial
theorem esize_le_value {n M : ℕ} (h : n ≤ M) : esize n ≤ 4 * M + 1 := by
  have hs : Nat.size n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self
  exact (esize_nat_le n).trans (by omega)
end
end MIPRE.Introspection.ClockArithmetic

namespace MIPRE.Introspection.ClockArithmetic
noncomputable section
open Cost Polynomial
theorem unaryCost_le {n M : ℕ} (h : n ≤ M) : unaryCost n ≤ unaryCostPoly.eval M := by
  have hs : Nat.size n ≤ M := (Nat.size_le.2 Nat.lt_two_pow_self).trans h
  have he := esize_le_value h
  simp only [unaryCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  unfold unaryCost
  gcongr
end
end MIPRE.Introspection.ClockArithmetic

namespace MIPRE.Introspection.ClockArithmetic
noncomputable section
open Cost Polynomial
theorem mulCost_le {a b M : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    mulCost a b ≤ mulCostPoly.eval M := by
  simp only [mulCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  unfold mulCost
  gcongr
end
end MIPRE.Introspection.ClockArithmetic

namespace MIPRE.Introspection.ClockArithmetic
noncomputable section
open Cost Polynomial
theorem clock_arguments_le {k lam n : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    lam ≤ ansBound k lam n ∧ n ≤ ansBound k lam n ∧
      lam * n + 1 ≤ ansBound k lam n ∧ (lam * n + 1) ^ k ≤ ansBound k lam n := by
  have hm : lam * n + 1 ≤ (lam * n + 1) ^ k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ lam * n + 1) hk
  have hq : (lam * n + 1) ^ k ≤ ansBound k lam n := Nat.lt_two_pow_self.le
  have hlam : lam ≤ lam * n := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left lam hn
  have hnn : n ≤ lam * n := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hl
  exact ⟨(by omega : lam ≤ lam * n + 1).trans (hm.trans hq),
    (by omega : n ≤ lam * n + 1).trans (hm.trans hq), hm.trans hq, hq⟩
end
end MIPRE.Introspection.ClockArithmetic

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.ClockArithmetic
open Cost Polynomial
theorem _root_.solution {k lam n : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    uniformCost k lam n + esize lam + esize n + 3 ≤ (clockCostPoly k).eval (ansBound k lam n) := by
  obtain ⟨hlB, hnB, hmB, hqB⟩ := clock_arguments_le hk hl hn
  have hul := unaryCost_le hlB
  have hun := unaryCost_le hnB
  have huB := unaryCost_le (Nat.le_refl (ansBound k lam n))
  have hel := esize_le_value hlB
  have hen := esize_le_value hnB
  have hmul := mulCost_le hlB hnB
  have hp := polynomial_eval_mono (powerBound k) hmB
  have hprod := Nat.mul_le_mul hlB hnB
  have he := Nat.mul_le_mul (Nat.add_le_add_right hqB 2)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hqB) 20)
  simp only [clockCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  dsimp only [uniformCost]
  omega
end MIPRE.Introspection.ClockArithmetic
