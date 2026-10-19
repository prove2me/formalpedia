-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryDecision.directed_complete
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:13:11.631809+00:00
-- url     : https://prove2.me/submissions/f2a89b14-0431-4a1f-9b9c-e849ab09964a

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryDecisionCompleteness.lean (solution of MIPRE.Introspection.AuxiliaryDecision.directed_complete);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
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
import Definitions.Def_MIPRE_Foundations_Cost_FiniteEncoding
import Definitions.Def_MIPRE_Foundations_Cost_FiniteChoice
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
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryReadProgram
import Definitions.Def_MIPRE_Foundations_Introspection_ClockedQueryProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingProgram
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterBits
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_ClockedSourceChecks
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryPrefixSolve
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryMaskProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingCoreProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySourceQueries
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanStage
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingNextProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingBoundaryProgram
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueries
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueryProg
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionProgram
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePaddingQueryCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_PrefixGuard
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryPrefixGuardProgram
import Definitions.Def_MIPRE_Foundations_Introspection_GuardedAuxiliaryProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_TypedQuotientPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryAnswerCoding
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionSoundness
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionCompleteness
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDecision_directed_apply
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDecision_directed_first
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDecision_directed_last
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDecision_directed_next
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_equal_iff
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_ofBits_take_first
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_readingCheck_vectors
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_samplingProg_depthFamily
import Theorems.Thm_MIPRE_Introspection_ClockedSourceChecks_sampling_eq_program
import Theorems.Thm_MIPRE_Introspection_legal_query_cost_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.Detyping.ClockProgram
noncomputable section
open Cost Cost.PolyTimeFun Program
theorem evalWithin_eq_some_iff (c : Prog) (x r : Data) (k : ℕ) :
    evalWithin c x k = some r ↔ ∃ time ≤ k, c.Runs x r time := by
  classical
  unfold evalWithin
  by_cases h : ∃ r time, time ≤ k ∧ c.Runs x r time
  · rw [dif_pos h]
    obtain ⟨time, ht, hr⟩ := h.choose_spec
    constructor
    · intro he
      have he' := Option.some.inj he
      exact ⟨time, ht, he' ▸ hr⟩
    · rintro ⟨t, ht', hr'⟩
      exact congrArg some (hr.deterministic hr').1
  · rw [dif_neg h]
    constructor
    · intro he; cases he
    · rintro ⟨time, ht, hr⟩
      exact False.elim (h ⟨r, time, ht, hr⟩)
end
end MIPRE.CL.Detyping.ClockProgram

namespace MIPRE.CL.Detyping.ClockProgram
noncomputable section
open Cost Cost.PolyTimeFun Program
/-- The success tag carries precisely the source result of an in-budget run. -/
theorem clockedResult_eq_iff (c : Prog) (x r : Data) (k : ℕ) :
    clockedResult c x k = .cons (encode true) r ↔ ∃ time ≤ k, c.Runs x r time := by
  have he : clockedResult c x k = .cons (encode true) r ↔ evalWithin c x k = some r := by
    cases h : evalWithin c x k <;> simp [clockedResult, h, encode, Data.ofBool]
  exact he.trans (evalWithin_eq_some_iff c x r k)
end
end MIPRE.CL.Detyping.ClockProgram

namespace MIPRE.Introspection
section
open Cost
/-- Positive introspection indices are exactly the range where the original budget applies. -/
theorem two_le_exp_index_iff (n : ℕ) : 2 ≤ 2 ^ n ↔ 1 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have : n = 0 := by omega
    simp [this] at h
  · intro hn
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn : 2 ^ 1 ≤ 2 ^ n)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
section
open Cost
/-- An actual bounded decider halts within an absolute polynomial-exponent
budget on every input from the original answer cut. -/
theorem original_decider_haltsWithin {ℓ lam n : ℕ} (V : Verifier ℓ)
    (hV : V.IsBounded lam) (hn : 1 ≤ n) (x y a b : BitStr)
    (hx : x.length ≤ (2 ^ n) ^ lam) (hy : y.length ≤ (2 ^ n) ^ lam)
    (ha : a.length ≤ (2 ^ n) ^ lam) (hb : b.length ≤ (2 ^ n) ^ lam) :
    HaltsWithin V.decider.prog (encode (2 ^ n, x, y, a, b)) (ansBound 5 lam n) := by
  have htime := (hV.1 (2 ^ n) ((two_le_exp_index_iff n).mpr hn)).2.2
  obtain ⟨r, t, ht, hrun⟩ := htime (encode (x, y, a, b))
  exact ⟨r, t, ht.trans (legal_query_cost_le (by have := hV.two_le; omega) hn
    x y a b hx hy ha hb), hrun⟩
end
end MIPRE.Introspection

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
/-- The repaired strict `8Q` outer cutoff contains every honest pair tuple. -/
theorem pairBits_lt_outer (Q R : ℕ) (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q)
    (y a : BitStr) (hy : y.length = Q) (ha : a.length ≤ R) :
    (pairBits y a).length < 8 * Q := by rw [pairBits_length, hy]; omega
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.DynamicParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem pairCheck_apply (bs : BitStr) (Q R : ℕ) :
    pairCheck (bs, Q, R) = decide (AnswerParser.pairValid Q R bs) := by
  simp only [pairCheck, AnswerParser.pairValid, PolyTimeFun.ite_apply, ap₂_apply,
    comp_apply, pair_apply, fst_apply, snd_apply, encoded_apply, treeEq_apply,
    AnswerParser.pairBitsProg_apply, pairParts_apply, lengthNat_apply,
    SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply, encode_injective.eq_iff,
    decide_eq_true_eq]
  rw [decide_and_if, decide_and_if]
  rfl
end
end MIPRE.Introspection.DynamicParser

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem sourceCheck_iff (y : BitStr) (s : ℕ) : sourceCheck (y,s) = true ↔ InSource s y := by
  simp only [sourceCheck, ap₂_apply, comp_apply, encoded_apply, treeEq_apply,
    DynamicParser.dropBits_apply, decide_eq_true_eq, encode_injective.eq_iff]
  change y.drop s = (y.drop s).map (fun _ => false) ↔ InSource s y
  simp only [List.map_const', List.length_drop, InSource]
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem guardCheck_iff (x : GuardInput) : guardCheck x = true ↔ GuardReady x := by
  simp only [guardCheck, andCheck_iff, ap₂_apply, comp_apply, pair_apply,
    leNat_apply, decide_eq_true_eq, DynamicParser.pairCheck_apply, fst_apply,
    sourceCheck_iff, inc_apply, lengthNat_apply, eight_apply, GuardReady, Nat.add_one_le_iff]
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem projectedCall_apply (x : GuardInput) : projectedCall x =
    encode (inputIndex x, (leftParts x).1.take (inputDim x),
      (rightParts x).1.take (inputDim x), (leftParts x).2, (rightParts x).2) := by
  simp [projectedCall, DynamicParser.takeBits_apply]
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
/-- All four original strings satisfy the internal original-game bound. -/
theorem GuardReady_cutoffs {x : GuardInput} (h : GuardReady x) :
    ((leftParts x).1.take (inputDim x)).length ≤ inputR x ∧
    ((rightParts x).1.take (inputDim x)).length ≤ inputR x ∧
    (leftParts x).2.length ≤ inputR x ∧ (rightParts x).2.length ≤ inputR x := by
  refine ⟨(List.length_take_le _ _).trans h.2.1, (List.length_take_le _ _).trans h.2.1, ?_, ?_⟩
  · simpa only [leftParts, comp_apply, pair_apply, DynamicParser.pairParts_apply] using h.2.2.1.2.2
  · simpa only [rightParts, comp_apply, pair_apply, DynamicParser.pairParts_apply] using h.2.2.2.1.2.2
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem andCheck_iff {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    andCheck f g x = true ↔ f x = true ∧ g x = true := by
  simp only [andCheck, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> simp
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.ClockedSourceChecks
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram SourceCompiler
theorem cross_iff (U : ClockedUniversalMachine) (b : Unary) (D : Prog)
    (x : GuardInput) :
    cross U (b, D, x) = true ↔ GuardReady x ∧
      clockedResult D (projectedCall x) b.length = .cons (encode true) (encode true) := by
  simp only [cross, MIPRE.Introspection.AuxiliaryProgram.andCheck_iff, equal_iff, comp_apply, pair_apply,
    fst_apply, snd_apply, const_apply, ClockedQuery.run_apply, guardCheck_iff]
end
end MIPRE.Introspection.ClockedSourceChecks

namespace MIPRE.Introspection.ClockedSourceChecks
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram SourceCompiler
/-- Exact full-register Sample semantics for the actual padded source. -/
theorem sampling_depthFamily {ℓ lam n Q R : ℕ} (U : ClockedUniversalMachine)
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓR : Nat.size ℓ ≤ (2 ^ n) ^ lam) (hs : V.sampler.dim (2 ^ n) ≤ Q)
    (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q) (w : Bool)
    (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    sampling U (unary (ansBound 5 lam n), V.sampler.prog, ℓ, w, 2 ^ n, Q, R,
      V.sampler.dim (2 ^ n), AnswerParser.pairBits (CL.toBits y) a,
      AnswerParser.pairBits (CL.toBits z) b) = true ↔
      a.length ≤ R ∧ b.length ≤ R ∧
      CLChecks.sampling (SourcePadding.depthFamily (firstEmbedding hs)
        (fun w => V.sampler.cl (2 ^ n) (Player.ofBool w)) w) (y,a) (z,b) := by
  rw [sampling_eq_program]
  exact samplingProg_depthFamily U V hV hn hℓ hℓR hs hQ hR w y z a b
end
end MIPRE.Introspection.ClockedSourceChecks

namespace MIPRE.Introspection.ClockedSourceChecks
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram SourceCompiler
/-- Exact source-game acceptance on the original legal alphabet. -/
theorem cross_original {ℓ lam n Q : ℕ} (U : ClockedUniversalMachine)
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n) (s : ℕ) (a b : BitStr) :
    let x : GuardInput := (2 ^ n,Q,(2 ^ n)^lam,s,a,b)
    cross U (unary (ansBound 5 lam n), V.decider.prog, x) = true ↔
      GuardReady x ∧ V.decider.Accepts (2 ^ n)
        ((leftParts x).1.take s) ((rightParts x).1.take s)
        (leftParts x).2 (rightParts x).2 := by
  dsimp only
  rw [cross_iff, length_unary, projectedCall_apply, CL.Detyping.ClockProgram.clockedResult_eq_iff]
  constructor
  · rintro ⟨hg,t,_,hr⟩
    exact ⟨hg,t,hr⟩
  · rintro ⟨hg,t,hr⟩
    obtain ⟨hx,hy,ha,hb⟩ := GuardReady_cutoffs hg
    obtain ⟨r,time,ht,hout⟩ := original_decider_haltsWithin V hV hn _ _ _ _ hx hy ha hb
    exact ⟨hg,t,(hout.deterministic hr).2 ▸ ht,hr⟩
end
end MIPRE.Introspection.ClockedSourceChecks

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram
theorem toBits_pull_first {s Q : ℕ} (h : s ≤ Q) (x : Fin Q → CL.𝔽₂) :
    CL.toBits (CL.pull (firstEmbedding h) x) = (CL.toBits x).take s := by
  rw [← ofBits_take_first h x, CL.toBits_ofBits]
  simp [CL.length_toBits, Nat.min_eq_left h]
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.AuxiliarySourceScan
noncomputable section
open Cost SourcePadding SourcePadding.Program AuxiliaryProgram
theorem level_size_le {lam n j : ℕ} (hlam : 2 ≤ lam) (hn : 1 ≤ n) (hj : j < 7) :
    Nat.size (j + 1) ≤ (2 ^ n) ^ lam := by
  have hs : Nat.size (j + 1) ≤ 3 := Nat.size_le.mpr (by norm_num; omega)
  have htwo : 2 ≤ 2 ^ n := (two_le_exp_index_iff n).mpr hn
  have hfour : 4 ≤ (2 ^ n) ^ lam := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left htwo 2
      _ ≤ (2 ^ n) ^ lam := Nat.pow_le_pow_right (by omega) hlam
  omega
end
end MIPRE.Introspection.AuxiliarySourceScan

namespace MIPRE.Introspection.AuxiliaryDecision
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SourcePadding SourcePadding.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
theorem directed_canonical (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) (V : Verifier 7) (lam n Q R : ℕ)
    (t u : QuestionType P 7) (a b : BitStr) :
    directed U X Z project (canonical V lam n Q R parameters t u a b) =
      branch U X Z project (route X Z (t,u)).1 (canonical V lam n Q R parameters t u a b) :=
  directed_apply U X Z project _
end
end MIPRE.Introspection.AuxiliaryDecision

namespace MIPRE.Introspection.AuxiliaryDecision
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SourcePadding SourcePadding.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
/-- The Z/Sample edge compares the full register, including padding coordinates. -/
theorem directed_z_sample (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) (V : Verifier 7) (lam n Q R : ℕ)
    (w : Bool) (a : BitStr) (z : Fin Q → CL.𝔽₂) (b : BitStr) :
    let x := canonical V lam n Q R parameters (.inl Z) (.inr (.sample,w)) a
      (AnswerParser.pairBits (CL.toBits z) b)
    directed U X Z project x = true ↔ project x = CL.toBits z := by
  dsimp only
  rw [directed_canonical]
  simp only [route, ↓reduceIte]
  change equal project (fst.comp rightPair) _ = true ↔ _
  rw [equal_iff]
  simp only [comp_apply, rightPair, pair_apply, fst_apply, rightBits, right, width, bounds,
    canonical, snd_apply, DynamicParser.pairParts_apply,
    AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]
end
end MIPRE.Introspection.AuxiliaryDecision

namespace MIPRE.Introspection.AuxiliaryDecision
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SourcePadding SourcePadding.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
/-- The actual source Sample call enforces the full padded CL relation. -/
theorem directed_sampling (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q R : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q)
    (w : Bool) (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    directed U X Z project (canonical V lam n Q R parameters
      (.inr (.introspect,w)) (.inr (.sample,w))
      (AnswerParser.pairBits (CL.toBits y) a) (AnswerParser.pairBits (CL.toBits z) b)) = true ↔
      a.length ≤ R ∧ b.length ≤ R ∧ CLChecks.sampling (padded V hs w) (y,a) (z,b) := by
  rw [directed_canonical]
  simp only [route, ↓reduceIte]
  simp only [branch, show (1 : Fin 8).val = 1 from rfl, comp_apply, pair_apply, metadata,
    finiteFunction_apply, leftType, rightType, left, right, canonical, fst_apply, snd_apply,
    route, ↓reduceIte]
  change ClockedSourceChecks.sampling U (unary (ansBound 5 lam n), V.sampler.prog,
    7,w,2 ^ n,Q,R,V.sampler.dim (2 ^ n),AnswerParser.pairBits (CL.toBits y) a,
      AnswerParser.pairBits (CL.toBits z) b) = true ↔ _
  exact ClockedSourceChecks.sampling_depthFamily U V hV hn (by decide)
    (AuxiliarySourceScan.level_size_le hV.two_le hn (by decide : 6 < 7)) hs hQ hR w y z a b
end
end MIPRE.Introspection.AuxiliaryDecision

namespace MIPRE.Introspection.AuxiliaryDecision
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SourcePadding SourcePadding.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
/-- Introspect/Read retains the ordinary answer cutoff and full-register question. -/
theorem directed_reading (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) (V : Verifier 7) (lam n : ℕ)
    {Q R : ℕ} (hQ : 4 ≤ Q) (hR : 3 * R ≤ Q) (w : Bool)
    (y z zp : Fin Q → CL.𝔽₂) (a b : BitStr) :
    directed U X Z project (canonical V lam n Q R parameters
      (.inr (.introspect,w)) (.inr (.read,w))
      (AnswerParser.pairBits (CL.toBits y) a)
      (AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) b)) = true ↔
      a.length ≤ R ∧ b.length ≤ R ∧ CLChecks.reading (y,a) (z,zp,b) := by
  rw [directed_canonical]
  simp only [route, ↓reduceIte]
  exact readingCheck_vectors hQ hR (2 ^ n) (V.sampler.dim (2 ^ n)) y z zp a b
end
end MIPRE.Introspection.AuxiliaryDecision

namespace MIPRE.Introspection.AuxiliaryDecision
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SourcePadding SourcePadding.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
/-- The cross-Introspect branch runs the original decision program after
the full source-membership and original-answer guards. -/
theorem directed_cross (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n) (a b : BitStr) :
    let g : SourceCompiler.GuardInput :=
      (2 ^ n,Q,(2 ^ n)^lam,V.sampler.dim (2 ^ n),a,b)
    directed U X Z project (canonical V lam n Q ((2 ^ n)^lam) parameters
      (.inr (.introspect,false)) (.inr (.introspect,true)) a b) = true ↔
      SourceCompiler.GuardReady g ∧ V.decider.Accepts (2 ^ n)
        ((SourceCompiler.leftParts g).1.take (V.sampler.dim (2 ^ n)))
        ((SourceCompiler.rightParts g).1.take (V.sampler.dim (2 ^ n)))
        (SourceCompiler.leftParts g).2 (SourceCompiler.rightParts g).2 := by
  dsimp only
  rw [directed_canonical]
  simp only [route]
  exact ClockedSourceChecks.cross_original U V hV hn (V.sampler.dim (2 ^ n)) a b
end
end MIPRE.Introspection.AuxiliaryDecision

namespace MIPRE.Introspection.AuxiliaryDecision
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryAnswer AuxiliaryProgram SourcePadding SourcePadding.Program
open Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
theorem valid_bits {Q R : ℕ} (t : QuestionType P 7)
    (a : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr)
    (hf : TypedPredicate.fits t a = true) (hb : answerBound R a) : Valid Q R t (bits a) := by
  rcases t with p | ⟨t,w⟩
  · cases a <;> simp_all [TypedPredicate.fits, Valid]
  · cases t <;> cases a <;> simp_all [TypedPredicate.fits, Valid, bits, answerBound,
      AnswerParser.pairValid, AnswerParser.tripleValid,
      AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _),
      AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _),
      CL.length_toBits]
end
end MIPRE.Introspection.AuxiliaryDecision

namespace MIPRE.Introspection.AuxiliaryDecision
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryAnswer AuxiliaryProgram SourcePadding SourcePadding.Program
open Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
theorem directed_cross_complete (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * ((2 ^ n)^lam) ≤ Q)
    (x y : Fin Q → CL.𝔽₂) (a b : BitStr) (ha : a.length ≤ (2 ^ n)^lam)
    (hb : b.length ≤ (2 ^ n)^lam)
    (hx : SourceCompiler.InSource (V.sampler.dim (2 ^ n)) (CL.toBits x))
    (hy : SourceCompiler.InSource (V.sampler.dim (2 ^ n)) (CL.toBits y))
    (h : sourcePredicate V hs x y a b = true) :
    directed U X Z project (canonical V lam n Q ((2 ^ n)^lam) parameters
      (.inr (.introspect,false)) (.inr (.introspect,true))
      (bits (.pair x a)) (bits (.pair y b))) = true := by
  apply (directed_cross U X Z project V hV hn _ _).mpr
  constructor
  · simp only [SourceCompiler.GuardReady, SourceCompiler.inputDim, SourceCompiler.inputQ,
      SourceCompiler.inputR, SourceCompiler.inputIndex, SourceCompiler.inputLeft,
      SourceCompiler.inputRight, SourceCompiler.leftParts, SourceCompiler.rightParts,
      comp_apply, pair_apply, fst_apply, snd_apply, DynamicParser.pairParts_apply, bits,
      AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]
    exact ⟨hs,(hV.1 _ ((two_le_exp_index_iff n).mpr hn)).1,
      valid_bits (.inr (.introspect,false) : QuestionType P 7) (.pair x a) rfl ha,
      valid_bits (.inr (.introspect,true) : QuestionType P 7) (.pair y b) rfl hb,
      hx,hy,AnswerParser.pairBits_lt_outer _ _ hQ hR _ _ (CL.length_toBits _) ha,
      AnswerParser.pairBits_lt_outer _ _ hQ hR _ _ (CL.length_toBits _) hb⟩
  · simp only [SourceCompiler.leftParts, SourceCompiler.rightParts, comp_apply, pair_apply,
      SourceCompiler.inputQ, SourceCompiler.inputLeft, SourceCompiler.inputRight, fst_apply,
      snd_apply, DynamicParser.pairParts_apply, bits,
      AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]
    simpa only [sourcePredicate, decide_eq_true_eq, toBits_pull_first] using h
end
end MIPRE.Introspection.AuxiliaryDecision

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryDecision
open Cost Cost.PolyTimeFun AuxiliaryAnswer AuxiliaryProgram SourcePadding SourcePadding.Program
open Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
theorem _root_.solution (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (hQ : 4 ≤ Q) (hR : 3 * ((2 ^ n)^lam) ≤ Q)
    (π : BitStr → Fin Q → CL.𝔽₂) (t u : QuestionType P 7)
    (a b : ParsedAnswer (Fin Q → CL.𝔽₂) BitStr BitStr)
    (hfa : TypedPredicate.fits t a = true) (hfb : TypedPredicate.fits u b = true)
    (ha : answerBound ((2 ^ n)^lam) a) (hb : answerBound ((2 ^ n)^lam) b)
    (hga : PrefixGuard.holds (padded V hs) t a) (hgb : PrefixGuard.holds (padded V hs) u b)
    (hsa : sourceOutput (V.sampler.dim (2 ^ n)) t a)
    (hsb : sourceOutput (V.sampler.dim (2 ^ n)) u b)
    (hp : ∀ p c, (p = X ∨ p = Z) → t = .inl p → a = .pauli c →
      project (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) =
        CL.toBits (π c))
    (h : AuxiliaryQuotient.directed (padded V hs) X Z π (sourcePredicate V hs) t u a b = true) :
    directed U X Z project
      (canonical V lam n Q ((2 ^ n)^lam) parameters t u (bits a) (bits b)) = true := by
  rw [directed_canonical]
  generalize htu : (t,u) = tu
  fun_cases route X Z tu
  case case2 => rfl
  case case4 => rfl
  case case6 => rfl
  case case8 => rfl
  case case10 => rfl
  case case12 => rfl
  case case14 => rfl
  all_goals rcases Prod.mk.inj htu with ⟨rfl,rfl⟩
  all_goals cases a <;> cases b <;> simp_all only [TypedPredicate.fits, Bool.false_eq_true]
  case case1.pauli.pair w a z b =>
    simp only [AuxiliaryQuotient.directed, ↓reduceIte, decide_eq_true_eq] at h
    have hp' := hp Z a (Or.inr rfl) rfl rfl
    simp only [bits] at hp'
    rw [h] at hp'
    have he := (directed_z_sample U X Z project V lam n Q ((2 ^ n)^lam) w a z b).mpr hp'
    simpa only [directed_canonical, route, bits, ↓reduceIte] using he
  case case3.pair.pair w y a z b =>
    simp only [AuxiliaryQuotient.directed, ↓reduceIte, decide_eq_true_eq] at h
    have he := (directed_sampling (parameters := parameters) U X Z project V hV hn hs hQ hR w y z a b).mpr ⟨ha,hb,h⟩
    simpa only [directed_canonical, route, bits, ↓reduceIte] using he
  case case5.pair.read w y a z zp b =>
    simp only [AuxiliaryQuotient.directed, ↓reduceIte, decide_eq_true_eq] at h
    have he := (directed_reading (parameters := parameters) U X Z project V lam n hQ hR w y z zp a b).mpr ⟨ha,hb,h⟩
    simpa only [directed_canonical, route, bits, ↓reduceIte] using he
  case case7.hide.read k w v hkv y yp x z zp a =>
    have hk : k.val = 6 := by omega
    simp only [AuxiliaryQuotient.directed, hkv.2, and_self, ↓reduceIte,
      decide_eq_true_eq] at h
    have hkFin : k = 6 := Fin.ext hk
    subst k
    have he := (directed_last (parameters := parameters) (R := (2 ^ n)^lam) U X Z project V hV hn hs v 6 hkv.2 y yp x z zp a).mpr
      ⟨hga,hgb,h⟩
    simpa only [directed_canonical, route, bits, hkv.2, and_self, ↓reduceIte] using he
  case case9.hide.hide k w j v hkv y yp x z zp r =>
    simp only [AuxiliaryQuotient.directed, hkv.2, and_self, ↓reduceIte,
      decide_eq_true_eq] at h
    have hgb' : ∃ a, ((padded V hs v).truncate (k.val+1)).eval a =
        (padded V hs v).outputPrefix (k.val+1) z := by
      rw [hkv.2]
      exact hgb
    have he := (directed_next (parameters := parameters) (R := (2 ^ n)^lam) U X Z project V hV hn hs v k j hkv.2 y yp x z zp r).mpr
      ⟨hga,hgb',h⟩
    simpa only [directed_canonical, route, bits, hkv.2, and_self, ↓reduceIte] using he
  case case11.pauli.hide p k w hpk a y yp x =>
    have hk : k = 0 := Fin.ext hpk.2
    subst k
    simp only [AuxiliaryQuotient.directed, Fin.val_zero, and_self, ↓reduceIte,
      decide_eq_true_eq] at h
    have he := (directed_first U X Z project V hV hn hs w (π a) y yp x a
      (hp X a (Or.inl rfl) rfl rfl)).mpr h
    simpa only [directed_canonical, route, bits, Fin.val_zero, and_self, ↓reduceIte] using he
  case case13.pair.pair x a y b =>
    have he := directed_cross_complete (parameters := parameters) U X Z project V hV hn hs hQ hR x y a b
      ha hb hsa hsb h
    simpa only [directed_canonical, route] using he
end MIPRE.Introspection.AuxiliaryDecision
