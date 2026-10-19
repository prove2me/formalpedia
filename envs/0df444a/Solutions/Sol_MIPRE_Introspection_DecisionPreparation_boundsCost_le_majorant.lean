-- Prove2me | solution 1 for MIPRE.Introspection.DecisionPreparation.boundsCost_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:43:48.695004+00:00
-- url     : https://prove2.me/submissions/b2321d42-5977-47fc-bbd9-4c085f4877d5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/DecisionPreparationCost.lean (solution of MIPRE.Introspection.DecisionPreparation.boundsCost_le_majorant);
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
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_selectorBits_le_fieldBits

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
theorem mulCost_le {a b M : ℕ} (ha : a ≤ M) (hb : b ≤ M) :
    mulCost a b ≤ mulCostPoly.eval M := by
  simp only [mulCostPoly, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  unfold mulCost
  gcongr
end
end MIPRE.Introspection.ClockArithmetic

namespace MIPRE.Introspection.PauliSamplerParameters
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler ClockArithmetic
theorem unaryCost_le {x v : ℕ} (hx : x ≤ v) : unaryCost x ≤ unaryMajorant v := by
  have hsize : x.size ≤ v := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hx
  have henc : esize x ≤ 4 * v + 1 := (esize_nat_le x).trans (by omega)
  unfold unaryCost unaryMajorant
  gcongr
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

namespace MIPRE.Introspection.DecisionPreparation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler Polynomial
theorem esize_two_pow_le (n : ℕ) : esize (2 ^ n) ≤ 4 * n + 5 := by
  have h := esize_nat_le (2 ^ n)
  rw [Nat.size_pow] at h
  omega
end
end MIPRE.Introspection.DecisionPreparation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.DecisionPreparation
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler Polynomial
theorem _root_.solution {c lam n v : ℕ} (hc : 1 ≤ c)
    (hl : lam ≤ v) (hn : n ≤ v) (hu : lam*n ≤ v) :
    boundsCost c lam n ≤ boundsMajorant c v := by
  obtain ⟨hk,hj,hm⟩ := PauliSamplerParameters.parameters_le_widthBound hc hu
  have hv : v ≤ PauliSamplerParameters.widthBound c v := by
    have := Nat.mul_le_mul_right (v+2) hc
    unfold PauliSamplerParameters.widthBound
    omega
  have hul := PauliSamplerParameters.unaryCost_le hl
  have hun := PauliSamplerParameters.unaryCost_le hn
  have hel := ClockArithmetic.esize_le_value hl
  have hen := ClockArithmetic.esize_le_value hn
  have hmul := ClockArithmetic.mulCost_le hl hn
  have hseed := polynomial_eval_mono (parameterSeed c).timeBound
    (show 2*(lam*n)+1 ≤ 2*v+1 by omega)
  have hpower : powerUnaryCost (PauliSamplerParameters.selectorBits c lam n) ≤
      exponentBitsCost (PauliSamplerParameters.widthBound c v) +
        PauliSamplerParameters.unaryMajorant (PauliSamplerParameters.widthBound c v) + 1 := by
    have hexp : exponentBitsCost (PauliSamplerParameters.selectorBits c lam n) ≤
        exponentBitsCost (PauliSamplerParameters.widthBound c v) := by unfold exponentBitsCost; gcongr
    have hconv := PauliSamplerParameters.unaryCost_le hm
    change ClockArithmetic.unaryCost (2 ^ PauliSamplerParameters.selectorBits c lam n) ≤ _ at hconv
    unfold powerUnaryCost
    omega
  have hparam := polynomial_eval_mono parameterPost.timeBound
    (show 2*(lam*n)+1+(2*fieldBits c lam n+1)+1+(2*registerPower c lam n+1)+1 ≤
      6*PauliSamplerParameters.widthBound c v+5 by omega)
  have htwo := esize_two_pow_le (lam*n)
  have hbound := polynomial_eval_mono boundsPost.timeBound
    (show 2*registerPower c lam n+1+(2*fieldBits c lam n+1)+1+esize (2^(lam*n))+1 ≤
      8*PauliSamplerParameters.widthBound c v+9 by omega)
  have hexp : exponentBitsCost (lam*n) ≤ exponentBitsCost (PauliSamplerParameters.widthBound c v) := by
    unfold exponentBitsCost
    gcongr <;> omega
  have hmul' : ClockArithmetic.mulCost lam n ≤ ClockArithmetic.mulCost v v := by
    unfold ClockArithmetic.mulCost
    gcongr
  unfold boundsCost boundsMajorant contextCost
  change (encode (2^(lam*n))).size ≤ 4*(lam*n)+5 at htwo
  change boundsPost.timeBound.eval
    (2*registerPower c lam n+1+(2*fieldBits c lam n+1)+1+(encode (2^(lam*n))).size+1) ≤ _ at hbound
  simp only [Data.size_cons, Data.size_ofNat]
  change _ + _ + _ + _ + _ + _ + _ + _ + _ ≤ _
  dsimp only [PauliSamplerParameters.selectorBits] at hj hpower
  omega
end MIPRE.Introspection.DecisionPreparation
