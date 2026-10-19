-- Prove2me | solution 1 for MIPRE.Introspection.DecisionCompiler.answerBound_ansBound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:18:08.117983+00:00
-- url     : https://prove2.me/submissions/605ca898-cf32-42aa-9dd4-33cb6f222c91

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/DecisionCompilerCutoff.lean (solution of MIPRE.Introspection.DecisionCompiler.answerBound_ansBound);
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
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParams
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
import Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparation
import Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparationCost
import Definitions.Def_MIPRE_Background_Introspection_DecisionCompilerCutoff
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_selectorBits_le_fieldBits
import Theorems.Thm_MIPRE_Introspection_polynomial_ansBound

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.PauliSamplerParameters
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
theorem registerPower_le (c lam n : ℕ) :
    registerPower c lam n ≤ c * canonicalLog lam n + 1 := by
  apply Nat.lt_size.mp
  have h := Nat.size_pos.mpr (show 0 < c * canonicalLog lam n + 1 by omega)
  omega
end
end MIPRE.Introspection.PauliSamplerParameters

namespace MIPRE.Introspection.PauliSamplerParameters
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
theorem fieldBits_le (c lam n : ℕ) :
    fieldBits c lam n ≤ c * canonicalLog lam n + 1 := by
  have hs : (canonicalLog lam n - 1).size ≤ canonicalLog lam n :=
    (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans (Nat.sub_le _ _)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left c hs) 1
end
end MIPRE.Introspection.PauliSamplerParameters

namespace MIPRE.Introspection.PauliSamplerParameters
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler ClockArithmetic
theorem parameters_le_widthBound {c lam n v : ℕ} (hc : 1 ≤ c) (hu : lam * n ≤ v) :
    fieldBits c lam n ≤ widthBound c v ∧
    selectorBits c lam n ≤ widthBound c v ∧
    registerPower c lam n ≤ widthBound c v := by
  have ht : canonicalLog lam n ≤ v + 2 := by unfold canonicalLog; omega
  have hw : c * canonicalLog lam n + 1 ≤ widthBound c v := by
    unfold widthBound
    gcongr
  have hk := (fieldBits_le c lam n).trans hw
  exact ⟨hk, (selectorBits_le_fieldBits hc lam n).trans hk,
    (registerPower_le c lam n).trans hw⟩
end
end MIPRE.Introspection.PauliSamplerParameters

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.DecisionCompiler
open Cost Cost.PolyTimeFun Polynomial
theorem _root_.solution {c : ℕ} (hc : 1 ≤ c) :
    ∃ K, ∀ lam n, 1 ≤ lam → 1 ≤ n →
      answerBound (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n) ≤
        ansBound K lam n := by
  let d := 2*(3*c+1)
  obtain ⟨K,hK⟩ := polynomial_ansBound (8*X^d) 1
  refine ⟨K, fun lam n hl hn => ?_⟩
  let u := lam*n
  let H := PauliSamplerParameters.widthBound c u
  let B := ansBound 1 lam n
  obtain ⟨hk, _, hm⟩ := PauliSamplerParameters.parameters_le_widthBound hc (le_refl u)
  have hH : H ≤ (3*c+1)*(u+1) := by
    dsimp [H, PauliSamplerParameters.widthBound]
    nlinarith
  have hQ : SourceCompiler.registerBits c lam n ≤ B^d := by
    calc SourceCompiler.registerBits c lam n
        ≤ 2^H * 2^H := Nat.mul_le_mul
          (Nat.pow_le_pow_right (by decide) hm)
          (hk.trans (Nat.lt_two_pow_self.le))
      _ = 2^(2*H) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2^((u+1)*d) := Nat.pow_le_pow_right (by decide) (by dsimp [d]; nlinarith)
      _ = B^d := by simp [B, ansBound, u, pow_mul]
  have hB : 1 ≤ B := Nat.one_le_pow _ _ (by decide)
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hR : SourceCompiler.originalBound lam n ≤ B^d := by
    calc SourceCompiler.originalBound lam n ≤ B := by
          apply Nat.pow_le_pow_right (by decide)
          change u ≤ (u+1)^1
          simp
      _ ≤ B^d := by simpa only [pow_one] using Nat.pow_le_pow_right hB hd
  have hmB : max 1 (max (SourceCompiler.registerBits c lam n)
      (SourceCompiler.originalBound lam n)) ≤ B^d :=
    max_le (Nat.one_le_pow _ _ hB) (max_le hQ hR)
  calc answerBound (SourceCompiler.registerBits c lam n) (SourceCompiler.originalBound lam n)
      ≤ 8*B^d := Nat.mul_le_mul_left _ hmB
    _ ≤ ansBound K lam n := by
      simpa only [eval_mul, eval_ofNat, eval_pow, eval_X] using hK lam n hl hn
end MIPRE.Introspection.DecisionCompiler
