-- Prove2me | solution 1 for MIPRE.Introspection.PauliErrorParameters.qldError_le_profile
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:58.850471+00:00
-- url     : https://prove2.me/submissions/99dff378-4f0a-4cd0-8b81-4c0aa08cd28f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PauliErrorParameters.lean (solution of MIPRE.Introspection.PauliErrorParameters.qldError_le_profile);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalitiesPow
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
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
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_PauliErrorParameters

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.PauliErrorParameters
noncomputable section
open SourceCompiler PauliSamplerParameters
theorem profileCoefficient_one_le (a c : ℝ) : 1 ≤ profileCoefficient a c := le_max_left _ _
end
end MIPRE.Introspection.PauliErrorParameters

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.PauliErrorParameters
open SourceCompiler PauliSamplerParameters
theorem _root_.solution {a b c x m q ε : ℝ}
    (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1) (hc : 1 ≤ c)
    (hcb : 2 * a + 2 ≤ c * b) (hx : 1 ≤ x) (hm : 0 ≤ m) (hε : 0 ≤ ε)
    (hmx : m ≤ (c + 1) * x) (hqx : x ^ c ≤ q)
    (h2x : x ^ c ≤ (2 : ℝ) ^ (2 * m)) :
    qldError a b m q ε ≤ errorProfile (profileCoefficient a c) b x ε := by
  have ha0 : 0 ≤ a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hxp : 0 < x := by linarith
  have hcp : 0 ≤ c + 1 := by linarith
  have hxcp := Real.rpow_pos_of_pos hxp c
  have hq := Real.rpow_le_rpow_of_nonpos hxcp hqx (show -b ≤ 0 by linarith)
  rw [← Real.rpow_mul hx0] at hq
  have h2 := Real.rpow_le_rpow_of_nonpos hxcp h2x (show -b / 2 ≤ 0 by linarith)
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hx0] at h2
  have hexp : 2 * m * (-b / 2) = -b * m := by ring
  rw [hexp] at h2
  have hmPow := Real.rpow_le_rpow hm hmx ha0
  rw [Real.mul_rpow hcp hx0] at hmPow
  have hqTail : x ^ a * q ^ (-b) ≤ x ^ (-b) := by
    calc
      _ ≤ x ^ a * x ^ (c * -b) := mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hx0 _)
      _ = x ^ (a + c * -b) := (Real.rpow_add hxp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  have h2Tail : x ^ a * (2 : ℝ) ^ (-b * m) ≤ x ^ (-b) := by
    calc
      _ ≤ x ^ a * x ^ (c * (-b / 2)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx0 _)
      _ = x ^ (a + c * (-b / 2)) := (Real.rpow_add hxp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  let K := a * (c + 1) ^ a
  have hK : 0 ≤ K := mul_nonneg ha0 (Real.rpow_nonneg hcp _)
  have hq0 : 0 ≤ q := hxcp.le.trans hqx
  have hrest : 0 ≤ ε ^ b + q ^ (-b) + (2 : ℝ) ^ (-b * m) := by positivity
  have hmain : qldError a b m q ε ≤ K * (x ^ a * ε ^ b + 2 * x ^ (-b)) := by
    calc
      _ ≤ a * ((c + 1) ^ a * x ^ a) *
          (ε ^ b + q ^ (-b) + (2 : ℝ) ^ (-b * m)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmPow ha0) hrest
      _ = K * (x ^ a * ε ^ b + x ^ a * q ^ (-b) + x ^ a * (2 : ℝ) ^ (-b * m)) := by
        dsimp [K]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK
  have haA : a ≤ profileCoefficient a c := (le_max_left _ _).trans (le_max_right _ _)
  have hKA : 2 * K ≤ profileCoefficient a c := by
    simpa only [K, profileCoefficient, mul_assoc] using
      ((le_max_right a (2 * a * (c + 1) ^ a)).trans (le_max_right 1 _))
  have hK1 : K ≤ profileCoefficient a c := by linarith
  have hxPow := Real.rpow_le_rpow_of_exponent_le hx haA
  have hεpow := Real.rpow_nonneg hε b
  have hxNeg := Real.rpow_nonneg hx0 (-b)
  have hfirst := mul_le_mul_of_nonneg_right hxPow hεpow
  have hf := mul_le_mul hK1 hfirst (mul_nonneg (Real.rpow_nonneg hx0 _) hεpow)
    (by linarith [profileCoefficient_one_le a c])
  have ht := mul_le_mul_of_nonneg_right hKA hxNeg
  unfold errorProfile
  nlinarith
end MIPRE.Introspection.PauliErrorParameters
