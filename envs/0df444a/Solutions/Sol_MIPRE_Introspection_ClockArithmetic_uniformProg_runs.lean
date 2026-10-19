-- Prove2me | solution 1 for MIPRE.Introspection.ClockArithmetic.uniformProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:50:07.002988+00:00
-- url     : https://prove2.me/submissions/ad5aca9b-e4f7-47bd-8a4d-84998176938c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ClockArithmetic.lean (solution of MIPRE.Introspection.ClockArithmetic.uniformProg_runs);
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
import Theorems.Thm_MIPRE_Cost_Prog_mulLoop_runs
import Theorems.Thm_MIPRE_Cost_Prog_polyProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_polyProg_wellScoped
import Theorems.Thm_MIPRE_Introspection_ClockArithmetic_bothUnary_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Polynomial
open Data
theorem mulProg_wellScoped : mulProg.WellScoped 1 := by
  simp [mulProg, WellScoped, mulBody, addProg, lenBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Polynomial
open Data
/-- `mulProg` multiplies unary numerals. -/
theorem mulProg_runs (a b : ℕ) :
    ∃ t ≤ (b + 1) * ((a + 1) * (4 * a + 2 * (a * b) + 15) + 4 * a + 4 * (a * b) + 2 * b + 41) +
        2 * b + 10,
      mulProg.Runs (Data.cons (ofNat a) (ofNat b)) (ofNat (a * b)) t := by
  obtain ⟨t, ht, hrun⟩ := mulLoop_runs a b 0 [ofNat b, Data.cons (ofNat a) (ofNat b)] (a * b)
    (by omega)
  have hpre := Eval.cons (Eval.var_of_get (env := [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
    (i := 1) (v := ofNat b) (by simp)) (Eval.nil [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
  have hrun' : Eval (Data.cons (ofNat b) Data.nil :: [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
      (.loop mulBody) (ofNat (a * b)) t := by simpa [ofNat] using hrun
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ofNat a) (b := ofNat b) (by simp)
    (Eval.let_ hpre hrun')⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)
end
end MIPRE.Cost.Prog

namespace MIPRE.Introspection.ClockArithmetic
noncomputable section
open Cost Cost.Prog Polynomial
theorem powerCoeffs_eval (k m : ℕ) : Data.polyEval (powerCoeffs k) m = m ^ k := by
  induction k with
  | zero => simp [powerCoeffs, Data.polyEval]
  | succ k ih =>
    simpa only [powerCoeffs, List.replicate_succ, List.cons_append, Data.polyEval,
      Nat.zero_add, pow_succ, Nat.mul_comm] using congrArg (m * ·) ih
end
end MIPRE.Introspection.ClockArithmetic

namespace MIPRE.Introspection.ClockArithmetic
noncomputable section
open Cost Cost.Prog Polynomial
theorem power_runs (k m : ℕ) : ∃ time ≤ (powerBound k).eval m,
    (polyProg (powerCoeffs k)).Runs (.ofNat m) (.ofNat (m ^ k)) time := by
  simpa only [powerCoeffs_eval, powerBound, Prog.Runs] using
    (polyProg_runs (powerCoeffs k)).choose_spec m []
end
end MIPRE.Introspection.ClockArithmetic

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.ClockArithmetic
open Cost Cost.Prog Polynomial
theorem _root_.solution (k lam n : ℕ) :
    ∃ time ≤ uniformCost k lam n,
      (uniformProg k).Runs (encode (lam, n)) (.ofNat (ansBound k lam n)) time := by
  obtain ⟨t₁, ht₁, h₁⟩ := bothUnary_runs lam n
  obtain ⟨t₂, ht₂, h₂⟩ := mulProg_runs lam n
  obtain ⟨t₃, ht₃, h₃⟩ := power_runs k (lam * n + 1)
  obtain ⟨t₄, ht₄, h₄⟩ := expBitsProg_runs ((lam * n + 1) ^ k)
  obtain ⟨t₅, ht₅, h₅⟩ := toUnaryProg_runs (ansBound k lam n)
  have hs : (Prog.cons .nil (.var 0)).Runs (.ofNat (lam * n))
      (.ofNat (lam * n + 1)) (2 * (lam * n) + 4) := by
    have h := Eval.cons (Eval.nil [Data.ofNat (lam * n)])
        (Eval.var_of_get (env := [Data.ofNat (lam * n)]) (i := 0)
          (v := .ofNat (lam * n)) (by simp))
    exact h.cast_cost (by simp only [Data.size_ofNat]; omega)
  refine ⟨_, ?_, Eval.let_ h₁ (Eval.append_of_wellScoped
    (Eval.let_ h₂ (Eval.append_of_wellScoped
      (Eval.let_ hs (Eval.append_of_wellScoped
        (Eval.let_ h₃ (Eval.append_of_wellScoped
          (Eval.let_ h₄ (Eval.append_of_wellScoped h₅ toUnaryProg_wellScoped _))
          ⟨expBitsProg_wellScoped, toUnaryProg_wellScoped.mono (by omega) _⟩ _))
        ⟨polyProg_wellScoped _, expBitsProg_wellScoped.mono (by omega) _,
          toUnaryProg_wellScoped.mono (by omega) _⟩ _))
      ⟨⟨trivial, by simp [WellScoped]⟩, (polyProg_wellScoped _).mono (by omega) _,
        expBitsProg_wellScoped.mono (by omega) _, toUnaryProg_wellScoped.mono (by omega) _⟩ _))
    ⟨mulProg_wellScoped, ⟨trivial, by simp [WellScoped]⟩,
      (polyProg_wellScoped _).mono (by omega) _, expBitsProg_wellScoped.mono (by omega) _,
      toUnaryProg_wellScoped.mono (by omega) _⟩ _)⟩
  change t₂ ≤ mulCost lam n at ht₂
  change t₄ ≤ ((lam * n + 1) ^ k + 2) * (4 * (lam * n + 1) ^ k + 20) at ht₄
  change t₅ ≤ unaryCost (ansBound k lam n) at ht₅
  dsimp only [uniformCost]
  omega
end MIPRE.Introspection.ClockArithmetic
