-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryDecision.directed_next
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:09:03.150066+00:00
-- url     : https://prove2.me/submissions/fff919d9-9b19-429d-bcd4-9a3c9ba26a1c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryDecisionCorrect.lean (solution of MIPRE.Introspection.AuxiliaryDecision.directed_next);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDecisionCorrect
import Theorems.Thm_MIPRE_CL_CLFun_ExactlyOn_directSum
import Theorems.Thm_MIPRE_CL_CLFun_zeroOn_exactlyOn
import Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Introspection_AuxiliaryDecision_directed_apply
import Theorems.Thm_MIPRE_Introspection_AuxiliaryHiding_check_correct
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_ofBits_take_first
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_toBits_push_first
import Theorems.Thm_MIPRE_Introspection_SourceCompiler_bounded_dimensionResult
import Theorems.Thm_MIPRE_Introspection_SourcePadding_Program_factorFromContext_legal
import Theorems.Thm_MIPRE_Introspection_SourcePadding_Program_matrix_correct
import Theorems.Thm_MIPRE_Introspection_SourcePadding_eval_truncate_embed_zeroOn
import Theorems.Thm_MIPRE_Introspection_SourcePadding_mapOfPrefix_embed_zeroOn

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.supportedOn {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    P.SupportedOn T := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
/-- Embedded factors still partition precisely the embedded original register. -/
theorem ExactlyOn.embed (e : ι ↪ κ) {P : CLFun F ι ℓ} {S : Finset ι}
    (hP : P.ExactlyOn S) : (P.embed e).ExactlyOn (S.map e) := by
  induction P generalizing S with
  | zero =>
    change S = ∅ at hP
    simp [CLFun.embed, hP]
  | cons U L next ih =>
    refine ⟨Finset.map_subset_map.mpr hP.1, fun x => ?_⟩
    rw [← Finset.map_sdiff]
    exact ih _ (hP.2 _)
end
end MIPRE.CL.CLFun

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

namespace MIPRE.Introspection.SourcePadding
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F I J A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  {ℓ : ℕ} (e : I ↪ J) (L : Bool → CL.CLFun F I ℓ)
  (D : (I → F) → (I → F) → A → A → Bool)
theorem depthFamily_exactlyOn (hℓ : 0 < ℓ) (hL : ∀ w, (L w).ExactlyOn univ) (w : Bool) :
    (depthFamily e L w).ExactlyOn univ := by
  have hz := CL.CLFun.zeroOn_exactlyOn (F := F) (univ.map e)ᶜ ℓ (by omega)
  have hh := ((hL w).embed e).directSum hz (Finset.disjoint_left.mpr fun i hi hci => (Finset.mem_compl.mp hci) hi)
  simpa [depthFamily, family] using hh
end
end MIPRE.Introspection.SourcePadding

namespace MIPRE.Introspection.AuxiliarySource
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear
theorem query_apply (U : ClockedUniversalMachine) (kind : ℕ) (y : BitStr)
    (b : Unary) (S : Prog) (n : ℕ) (w : Bool) (j : ℕ) (u : BitStr) :
    query U kind (y, b, S, n, w, j, u) =
      clockedResult S (encode (n, kind, Player.ofBool w, j, u, y)) b.length := by
  cases w <;> rfl
end
end MIPRE.Introspection.AuxiliarySource

namespace MIPRE.Introspection.AuxiliarySource
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear
theorem linear_correct (U : ClockedUniversalMachine) (y v : BitStr)
    (b : Unary) (S : Prog) (n : ℕ) (w : Bool) (j : ℕ) (u : BitStr)
    (h : clockedResult S (encode (n, CL.Sampler.Query.linear (Player.ofBool w) j u y)) b.length =
      .cons (encode true) (encode v)) :
    linear U (y, b, S, n, w, j, u) = v := by
  simp only [linear, comp_apply, query_apply]
  change readBits (treeTail (clockedResult S
    (encode (n, CL.Sampler.Query.linear (Player.ofBool w) j u y)) b.length)) = v
  rw [h, treeTail_cons, readBits_encode]
end
end MIPRE.Introspection.AuxiliarySource

namespace MIPRE.Introspection.SourcePadding
noncomputable section
open Finset Classical CL
variable {F I J : Type*} [Field F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
theorem depthFamily_eval_truncate {ℓ : ℕ} (e : I ↪ J) (L : Bool → CLFun F I ℓ)
    (w : Bool) (j : ℕ) (x : J → F) :
    ((depthFamily e L w).truncate j).eval x =
      push e (((L w).truncate j).eval (pull e x)) :=
  eval_truncate_embed_zeroOn e (L w) _
    (Finset.disjoint_left.mpr fun i hi hci => (Finset.mem_compl.mp hci) hi) j x
end
end MIPRE.Introspection.SourcePadding

namespace MIPRE.Introspection.SourcePadding
noncomputable section
open Finset Classical CL
variable {F I J : Type*} [Field F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
theorem pull_attained_prefix {ℓ : ℕ} (e : I ↪ J) (L : Bool → CLFun F I ℓ)
    (w : Bool) (j : ℕ) (u : J → F)
    (hu : ∃ x, u = ((depthFamily e L w).truncate j).eval x) :
    ∃ x, pull e u = ((L w).truncate j).eval x := by
  obtain ⟨x, rfl⟩ := hu
  refine ⟨pull e x, ?_⟩
  rw [depthFamily_eval_truncate, pull_push]
end
end MIPRE.Introspection.SourcePadding

namespace MIPRE.Introspection.SourcePadding
noncomputable section
open Finset Classical CL
variable {F I J : Type*} [Field F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
theorem depthFamily_mapOfPrefix {ℓ : ℕ} (e : I ↪ J) (L : Bool → CLFun F I ℓ)
    (w : Bool) (j : ℕ) (u y : J → F) :
    (depthFamily e L w).mapOfPrefix j u y =
      push e ((L w).mapOfPrefix j (pull e u) (pull e y)) := by
  exact mapOfPrefix_embed_zeroOn e (L w) _
    (Finset.disjoint_left.mpr fun i hi hci => (Finset.mem_compl.mp hci) hi) j u y
end
end MIPRE.Introspection.SourcePadding

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram
theorem sourceContext_apply (s b : Unary) (S : Prog) (n : ℕ) (w : Bool) (j : ℕ) (u : BitStr) :
    sourceContext (s, b, S, n, w, j, u) = (b, S, n, w, j, u.take s.length) := rfl
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram
theorem linear_apply (U : ClockedUniversalMachine) (y : BitStr) (s : Unary)
    (ctx : AuxiliarySource.Context) :
    linear U (y, s, ctx) = AuxiliarySource.linear U
      (y.take s.length, sourceContext (s, ctx)) ++
      List.replicate ((AuxiliarySource.inputPrefix ctx).length - s.length) false := by
  simp [linear, suffixWidth, fullWidth, sourceWidth]
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram
theorem toBits_pull_first {s Q : ℕ} (h : s ≤ Q) (x : Fin Q → CL.𝔽₂) :
    CL.toBits (CL.pull (firstEmbedding h) x) = (CL.toBits x).take s := by
  rw [← ofBits_take_first h x, CL.toBits_ofBits]
  simp [CL.length_toBits, Nat.min_eq_left h]
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram
theorem linear_correct (U : ClockedUniversalMachine) {s Q : ℕ} (h : s ≤ Q)
    (ctx : AuxiliarySource.Context) (u y : Fin Q → CL.𝔽₂) (v : Fin s → CL.𝔽₂)
    (hu : AuxiliarySource.inputPrefix ctx = CL.toBits u)
    (hv : AuxiliarySource.linear U
      (CL.toBits (CL.pull (firstEmbedding h) y), sourceContext (unary s, ctx)) = CL.toBits v) :
    linear U (CL.toBits y, unary s, ctx) = CL.toBits (CL.push (firstEmbedding h) v) := by
  rw [linear_apply, length_unary, ← toBits_pull_first h, hv, hu, CL.length_toBits,
    toBits_push_first]
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram
theorem dimension_correct (U : ClockedUniversalMachine) (ctx : AuxiliarySource.Context) (s : ℕ)
    (h : clockedResult (AuxiliarySource.source ctx)
      (encode (AuxiliarySource.index ctx, CL.Sampler.Query.dimension))
      (AuxiliarySource.budget ctx).length = .cons (encode true) (encode s)) :
    dimension U ctx = s := by
  simp only [dimension, comp_apply, pair_apply, const_apply, encoded_apply, ClockedQuery.run_apply]
  rw [h, treeTail_cons, readNat_encode]
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram
theorem adapt_correct (U : ClockedUniversalMachine) (ctx : AuxiliarySource.Context) (s : ℕ)
    (hs : s ≤ (AuxiliarySource.inputPrefix ctx).length) (hd : dimension U ctx = s) :
    adapt U ctx = (unary s, ctx) := by
  simp only [adapt, pair_apply, comp_apply, id_apply, hd, DynamicParser.boundedOffset_apply,
    Nat.min_eq_left hs]
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear AuxiliaryProgram
theorem matrixFromContext_correct (U : ClockedUniversalMachine)
    (ctx : AuxiliarySource.Context) (s : ℕ)
    (hs : s ≤ (AuxiliarySource.inputPrefix ctx).length) (hd : dimension U ctx = s) :
    matrixFromContext U ctx = matrix U (unary s, ctx) := by
  rw [matrixFromContext, comp_apply, adapt_correct U ctx s hs hd]
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.AuxiliarySource
noncomputable section
open Cost CL.Detyping
theorem linear_query_size_le (R : ℕ) (hR : 1 ≤ R) (w : Player) (j : ℕ) (u y : BitStr)
    (hj : Nat.size j ≤ R) (hu : u.length ≤ R) (hy : y.length ≤ R) :
    esize (CL.Sampler.Query.linear w j u y) + 1 ≤ 64 * R := by
  have hw : esize w ≤ 3 := by cases w <;> decide
  have hjb := esize_nat_le j
  have hub := esize_bitStr_le u
  have hyb := esize_bitStr_le y
  change esize ((2 : ℕ), w, j, u, y) + 1 ≤ _
  simp only [esize_prod]
  have htwo : esize (2 : ℕ) = 7 := by decide
  rw [htwo]
  omega
end
end MIPRE.Introspection.AuxiliarySource

namespace MIPRE.Introspection.AuxiliarySource
noncomputable section
open Cost CL.Detyping
theorem query_cost_le {lam n : ℕ} (hl : 1 ≤ lam) (hn : 1 ≤ n) (b : ℕ)
    (hb : b ≤ 64 * (2 ^ n) ^ lam) : (2 ^ n) ^ lam * b ^ lam ≤ ansBound 5 lam n := by
  let u := lam * n
  have hlu : lam ≤ u := by dsimp [u]; nlinarith
  have hu : 1 ≤ u := hl.trans hlu
  have hR : (2 ^ n) ^ lam = 2 ^ u := by rw [← pow_mul]; congr 1; exact Nat.mul_comm _ _
  have hs : b ≤ 2 ^ (6 + u) := by simpa [hR, pow_add] using hb
  have he : u + (6 + u) * lam ≤ (u + 1) ^ 5 := by
    have hc : 8 ≤ (u + 1) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (u + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc u + (6 + u) * lam ≤ u + (6 + u) * u := by gcongr
      _ ≤ 8 * (u + 1) ^ 2 := by nlinarith
      _ ≤ (u + 1) ^ 3 * (u + 1) ^ 2 := Nat.mul_le_mul_right _ hc
      _ = (u + 1) ^ 5 := by ring
  calc (2 ^ n) ^ lam * b ^ lam ≤ 2 ^ u * (2 ^ (6 + u)) ^ lam := by rw [hR]; gcongr
    _ = 2 ^ (u + (6 + u) * lam) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ ((u + 1) ^ 5) := Nat.pow_le_pow_right (by decide) he
end
end MIPRE.Introspection.AuxiliarySource

namespace MIPRE.Introspection.AuxiliarySource
noncomputable section
open Cost CL.Detyping
theorem bounded_query_result {ℓ lam n : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) (q : CL.Sampler.Query) (result : Data)
    (hq : esize q + 1 ≤ 64 * (2 ^ n) ^ lam)
    (hr : ∃ t, V.sampler.prog.Runs (encode (2 ^ n, q)) result t) :
    clockedResult V.sampler.prog (encode (2 ^ n, q)) (ansBound 5 lam n) =
      .cons (encode true) result := by
  obtain ⟨r, t, ht, hr'⟩ := (hV.1 (2 ^ n) ((two_le_exp_index_iff n).mpr hn)).2.1 (encode q)
  obtain ⟨tu, hu⟩ := hr
  rw [ClockProgram.clockedResult_eq_iff]
  exact ⟨t, ht.trans (query_cost_le (by have := hV.two_le; omega) hn _ hq),
    (hr'.deterministic hu).1 ▸ hr'⟩
end
end MIPRE.Introspection.AuxiliarySource

namespace MIPRE.Introspection.AuxiliarySource
noncomputable section
open Cost CL.Detyping
theorem bounded_linear_result {ℓ lam n : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) (w : Player) (j : ℕ) (u y : BitStr) (hj : 1 ≤ j) (hjℓ : j ≤ ℓ)
    (hjR : Nat.size j ≤ (2 ^ n) ^ lam)
    (hu : ∃ x, u = CL.toBits (((V.sampler.cl (2 ^ n) w).truncate (j - 1)).eval x))
    (hy : y.length = V.sampler.dim (2 ^ n)) :
    clockedResult V.sampler.prog (encode (2 ^ n, CL.Sampler.Query.linear w j u y))
      (ansBound 5 lam n) = .cons (encode true) (encode (CL.toBits
        ((V.sampler.cl (2 ^ n) w).mapOfPrefix (j - 1)
          (CL.ofBits (V.sampler.dim (2 ^ n)) u) (CL.ofBits (V.sampler.dim (2 ^ n)) y)))) := by
  have hs := (hV.1 (2 ^ n) ((two_le_exp_index_iff n).mpr hn)).1
  have hul : u.length = V.sampler.dim (2 ^ n) := by
    obtain ⟨x, rfl⟩ := hu
    exact CL.length_toBits _
  apply bounded_query_result V hV hn
  · exact linear_query_size_le _ (Nat.one_le_pow _ _ (by positivity)) w j u y hjR (hul ▸ hs) (hy ▸ hs)
  · exact V.sampler.runs_linear _ w j u y hj hjℓ hu hy
end
end MIPRE.Introspection.AuxiliarySource

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost LowDegree.BinaryLinear AuxiliaryProgram
theorem queryContext_dimension (U : ClockedUniversalMachine) {ℓ lam n : ℕ}
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (w : Bool) (j : ℕ) {Q : ℕ} (u : Fin Q → CL.𝔽₂) :
    dimension U (queryContext V lam n w j u) = V.sampler.dim (2 ^ n) := by
  apply dimension_correct
  simpa only [queryContext, AuxiliarySource.source, AuxiliarySource.index,
    AuxiliarySource.budget, Cost.PolyTimeFun.comp_apply, Cost.PolyTimeFun.fst_apply,
    Cost.PolyTimeFun.snd_apply, length_unary, SourceCompiler.dimensionResult] using
      SourceCompiler.bounded_dimensionResult V hV hn
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost LowDegree.BinaryLinear AuxiliaryProgram
theorem source_prefix_attained {ℓ n Q : ℕ} (V : Verifier ℓ)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (j : ℕ) (u : Fin Q → CL.𝔽₂)
    (hu : ∃ x, u = ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate j).eval x) :
    ∃ x, (CL.toBits u).take (V.sampler.dim (2 ^ n)) =
      CL.toBits (((V.sampler.cl (2 ^ n) (Player.ofBool w)).truncate j).eval x) := by
  obtain ⟨x, hx⟩ := pull_attained_prefix (firstEmbedding hQ) (sourceFamily V n) w j u hu
  refine ⟨x, ?_⟩
  rw [← toBits_pull_first hQ, hx]
  rfl
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost LowDegree.BinaryLinear AuxiliaryProgram
theorem linear_legal (U : ClockedUniversalMachine) {ℓ lam n Q : ℕ}
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (j : ℕ) (hj : j < ℓ)
    (hjR : Nat.size (j + 1) ≤ (2 ^ n) ^ lam) (u y : Fin Q → CL.𝔽₂)
    (hu : ∃ x, u = ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate j).eval x) :
    linear U (CL.toBits y, unary (V.sampler.dim (2 ^ n)), queryContext V lam n w j u) =
      CL.toBits ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).mapOfPrefix j u y) := by
  rw [depthFamily_mapOfPrefix]
  apply linear_correct U hQ _ u y _ rfl
  have hc := AuxiliarySource.bounded_linear_result V hV hn (Player.ofBool w) (j + 1)
    ((CL.toBits u).take (V.sampler.dim (2 ^ n)))
    ((CL.toBits y).take (V.sampler.dim (2 ^ n))) (by omega) (by omega) hjR
    (by simpa using source_prefix_attained V hQ w j u hu)
    (by simp [CL.length_toBits, Nat.min_eq_left hQ])
  have hr := AuxiliarySource.linear_correct U _ _ (unary (ansBound 5 lam n))
    V.sampler.prog (2 ^ n) w (j + 1) ((CL.toBits u).take (V.sampler.dim (2 ^ n)))
    (by simpa only [length_unary] using hc)
  simpa only [queryContext, sourceContext_apply, length_unary, toBits_pull_first,
    Nat.add_sub_cancel, ofBits_take_first hQ, sourceFamily] using hr
end
end MIPRE.Introspection.SourcePadding.Program

namespace MIPRE.Introspection.SourcePadding.Program
noncomputable section
open Cost LowDegree.BinaryLinear AuxiliaryProgram
theorem matrixFromContext_legal (U : ClockedUniversalMachine) {ℓ lam n Q : ℕ}
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (j : ℕ) (hj : j < ℓ)
    (hjR : Nat.size (j + 1) ≤ (2 ^ n) ^ lam) (u : Fin Q → CL.𝔽₂)
    (hu : ∃ x, u = ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate j).eval x) :
    matrixFromContext U (queryContext V lam n w j u) =
      matrixBits (LinearMap.toMatrix'
        ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).mapOfPrefix j u)) := by
  rw [matrixFromContext_correct U _ _ (by simpa [queryContext, AuxiliarySource.inputPrefix] using hQ)
    (queryContext_dimension U V hV hn w j u)]
  apply matrix_correct U (unary (V.sampler.dim (2 ^ n)), queryContext V lam n w j u)
    _ (CL.length_toBits u)
  intro y
  exact linear_legal U V hV hn hQ w j hj hjR u y hu
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

namespace MIPRE.Introspection.AuxiliarySourceScan
noncomputable section
open Cost SourcePadding SourcePadding.Program AuxiliaryProgram
/-- Any initial context prefix and level are replaced before the queried
stage. Only its fixed source, clock, index and player matter. -/
theorem queriesCorrectAt (U : ClockedUniversalMachine) {lam n Q : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool)
    (initialLevel : ℕ) (initial : Fin Q → CL.𝔽₂) (j : ℕ) (hj : j < 7) :
    AuxiliaryScan.QueriesCorrectAt (factorFromContext U) (matrixFromContext U)
      (queryContext V lam n w initialLevel initial)
      (depthFamily (firstEmbedding hQ) (sourceFamily V n) w) j := by
  intro u hu
  have ha : ∃ x, u = ((depthFamily (firstEmbedding hQ) (sourceFamily V n) w).truncate j).eval x := by
    obtain ⟨x, hx⟩ := hu
    exact ⟨x, hx.symm⟩
  have hjR := level_size_le hV.two_le hn hj
  change factorFromContext U (queryContext V lam n w j u) = _ ∧
    matrixFromContext U (queryContext V lam n w j u) = _
  exact ⟨factorFromContext_legal U V hV hn hQ w j hj hjR u ha,
    matrixFromContext_legal U V hV hn hQ w j hj hjR u ha⟩
end
end MIPRE.Introspection.AuxiliarySourceScan

namespace MIPRE.Introspection.AuxiliaryDecision
noncomputable section
open Cost Cost.PolyTimeFun AuxiliaryProgram SourcePadding SourcePadding.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
theorem padded_supported {n Q : ℕ} (V : Verifier 7)
    (hQ : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) :
    (padded V hQ w).SupportedOn Finset.univ :=
  (depthFamily_exactlyOn (firstEmbedding hQ) (sourceFamily V n) (by decide)
    (fun w => V.sampler.cl_exactlyOn _ _) w).supportedOn
end
end MIPRE.Introspection.AuxiliaryDecision

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryDecision
open Cost Cost.PolyTimeFun AuxiliaryProgram SourcePadding SourcePadding.Program
variable {P : Type*} [Fintype P] [DecidableEq P] [SizedEncoding P]
variable {parameters : Parameters}
theorem _root_.solution (U : ClockedUniversalMachine) (X Z : P)
    (project : PolyTimeFun (Input P 7) BitStr) {lam n Q R : ℕ}
    (V : Verifier 7) (hV : V.IsBounded lam) (hn : 1 ≤ n)
    (hs : V.sampler.dim (2 ^ n) ≤ Q) (w : Bool) (k j : Fin 7) (hk : k.val + 1 = j.val)
    (y yp x z zp t : Fin Q → CL.𝔽₂) :
    directed U X Z project (canonical V lam n Q R parameters (.inr (.hide k,w)) (.inr (.hide j,w))
      (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits x))
      (AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) (CL.toBits t))) = true ↔
      (∃ a, ((padded V hs w).truncate k.val).eval a = (padded V hs w).outputPrefix k.val y) ∧
      (∃ a, ((padded V hs w).truncate (k.val+1)).eval a = (padded V hs w).outputPrefix (k.val+1) z) ∧
      AuxiliaryQuotient.hidingNext (padded V hs w) k.val (y,yp,x) (z,zp,t) := by
  rw [directed_canonical]
  simp only [route, hk, and_self, ↓reduceIte]
  simp only [branch, show (4 : Fin 8).val = 4 from rfl, choose_apply, comp_apply, snd_apply, metadata, finiteFunction_apply,
    pair_apply, leftType, rightType, left, right, canonical, fst_apply, route, hk,
    and_self, ↓reduceIte, nextBranch]
  simp only [sourceContext, contextWith, metadata, comp_apply, pair_apply, finiteFunction_apply,
    leftType, rightType, left, right, fst_apply, snd_apply, route, hk, and_self, ↓reduceIte]
  simp only [leftTriple, rightTriple, leftBits, rightBits, left, right, width, bounds, context,
    comp_apply, pair_apply, fst_apply, snd_apply, DynamicParser.tripleParts_apply]
  change AuxiliaryHiding.check (factorFromContext U) (matrixFromContext U) k.val (queryContext V lam n w 0 (0 : Fin Q → CL.𝔽₂), AnswerParser.tripleParts Q
    (AnswerParser.tripleBits (CL.toBits y) (CL.toBits yp) (CL.toBits x)), AnswerParser.tripleParts Q
    (AnswerParser.tripleBits (CL.toBits z) (CL.toBits zp) (CL.toBits t))) = true ↔ _
  rw [AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _),
    AnswerParser.tripleParts_tripleBits _ _ _ _ (CL.length_toBits _) (CL.length_toBits _)]
  rw [← hk]
  exact AuxiliaryHiding.check_correct _ _ _ (padded_supported V hs w) k.val y yp x z zp t
    (fun i hi => AuxiliarySourceScan.queriesCorrectAt U V hV hn hs w 0 0 i (by omega))
end MIPRE.Introspection.AuxiliaryDecision
