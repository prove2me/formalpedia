-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryProgram.samplingProg_depthFamily
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:08:10.241387+00:00
-- url     : https://prove2.me/submissions/69a4fd9e-a11a-481c-b49b-7cbd648c6cc3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliarySamplingCorrect.lean (solution of MIPRE.Introspection.AuxiliaryProgram.samplingProg_depthFamily);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
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
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingProgram
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterBits
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingCorrect
import Theorems.Thm_MIPRE_CL_CLFun_SupportedOn_eval_directSum
import Theorems.Thm_MIPRE_CL_CLFun_zeroOn_exactlyOn
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_CL_pull_proj_compl
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Introspection_AnswerParser_field_append_injective
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_ofBits_take_first
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_samplingProg_accepts_iff
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_toBits_push_first

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
variable [Fintype ι] [Fintype κ]
/-- The embedded CL function acts only on its original coordinates. -/
theorem eval_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (x : κ → F) :
    (P.embed e).eval x = push e (P.eval (pull e x)) := by
  induction P generalizing x with
  | zero => simp [embed]
  | cons S L next ih =>
    simp only [embed, eval_cons, RegLinear.embed_apply, pull_push, ih,
      pull_proj_compl, push_add]
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

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem pairBits_injective {y a z b : BitStr} (h : pairBits y a = pairBits z b) :
    y = z ∧ a = b := by
  obtain ⟨hy, ha⟩ := field_append_injective y z (field a) (field b) h
  exact ⟨hy, (field_append_injective a b [] [] (by simpa using ha)).1⟩
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem pairCheck_apply (Q R : ℕ) (bs : BitStr) :
    pairCheck Q R bs = decide (pairValid Q R bs) := by
  simp only [pairCheck, pairValid, PolyTimeFun.ite_apply, ap₂_apply, comp_apply,
    encoded_apply, treeEq_apply, pairBitsProg_apply, pairPartsProg_apply, fst_apply,
    snd_apply, lengthNat_apply, SAT.ArrayProg.eqNat_apply, leNat_apply, const_apply,
    encode_injective.eq_iff, decide_eq_true_eq]
  rw [decide_and_if, decide_and_if]
  rfl
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem pairCheck_iff (Q R : ℕ) (bs : BitStr) : pairCheck Q R bs = true ↔
    ∃ y a, y.length = Q ∧ a.length ≤ R ∧ bs = pairBits y a := by
  rw [pairCheck_apply, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hy, ha⟩
    exact ⟨_, _, hy, ha, h⟩
  · rintro ⟨y, a, hy, ha, rfl⟩
    simp [pairValid, pairParts_pairBits Q y a hy, hy, ha]
end
end MIPRE.Introspection.AnswerParser

namespace MIPRE.Introspection.AnswerParser
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
/-- In particular, an encoded pair with a wrong register length or long `a` is rejected. -/
theorem pairCheck_pairBits (Q R : ℕ) (y a : BitStr) :
    pairCheck Q R (pairBits y a) = true ↔ y.length = Q ∧ a.length ≤ R := by
  rw [pairCheck_iff]
  constructor
  · rintro ⟨z, b, hz, hb, he⟩
    obtain ⟨rfl, rfl⟩ := pairBits_injective he
    exact ⟨hz, hb⟩
  · rintro ⟨hy, ha⟩
    exact ⟨y, a, hy, ha, rfl⟩
end
end MIPRE.Introspection.AnswerParser

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

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem reindexed_cons (n : ℕ) (d : Data) :
    reindexed (.cons (encode n) d) = .cons (encode (2 ^ n)) d := by
  simp only [reindexed, indexReader, comp_apply, treeHead_cons, treeTail_cons, readNat_encode]
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem InSource_padding {s Q : ℕ} {y : BitStr} (hy : y.length = Q) (h : InSource s y) :
    y = y.take s ++ List.replicate (Q-s) false := by
  rw [← hy, ← h]
  exact (List.take_append_drop s y).symm
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

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem outerCheck_iff (x : GuardInput) : outerCheck x = true ↔
    (inputLeft x).length < 8 * inputQ x ∧ (inputRight x).length < 8 * inputQ x := by
  simp only [outerCheck, andCheck_iff, ap₂_apply, comp_apply, leNat_apply,
    decide_eq_true_eq, inc_apply, lengthNat_apply, SourceCompiler.eight_apply,
    Nat.add_one_le_iff]
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem toBits_injective {Q : ℕ} : Function.Injective (@CL.toBits Q) := by
  intro x y h
  simpa only [CL.ofBits_toBits] using congrArg (CL.ofBits Q) h
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts readInput)
theorem samplingCall_apply (x : SamplingInput) : samplingCall x =
    encode (inputIndex x.2.2, CL.Sampler.Query.marginal (Player.ofBool x.2.1) x.1
      ((rightParts x.2.2).1.take (inputDim x.2.2))) := by
  cases hw : x.2.1 <;>
    simp [samplingCall,samplingFields,samplingRole,samplingLevel,DynamicParser.takeBits_apply,
      Player.ofBool,hw,encode_prod]
  <;> rfl
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts readInput)
theorem samplingExpected_apply (x : SamplingInput) : samplingExpected x =
    .cons (encode true) (encode ((leftParts x.2.2).1.take (inputDim x.2.2))) := by
  simp [samplingExpected,samplingFields,DynamicParser.takeBits_apply]
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.SourcePadding
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F I J A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  {ℓ : ℕ} (e : I ↪ J) (L : Bool → CL.CLFun F I ℓ)
  (D : (I → F) → (I → F) → A → A → Bool)
theorem supported_embed {k : ℕ} (P : CL.CLFun F I k) (S : Finset I)
    (hP : P.SupportedOn S) : (P.embed e).SupportedOn (S.map e) := by
  induction P generalizing S with
  | zero => trivial
  | cons U M next ih =>
    refine ⟨Finset.map_subset_map.mpr hP.1, fun x => ?_⟩
    rw [← Finset.map_sdiff]
    exact ih _ _ (hP.2 _)
end
end MIPRE.Introspection.SourcePadding

namespace MIPRE.Introspection.SourcePadding
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F I J A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  {ℓ : ℕ} (e : I ↪ J) (L : Bool → CL.CLFun F I ℓ)
  (D : (I → F) → (I → F) → A → A → Bool)
theorem depthFamily_eval (hℓ : 0 < ℓ) (hL : ∀ w, (L w).SupportedOn univ)
    (w : Bool) (x : J → F) : (depthFamily e L w).eval x = (family e L w).eval x := by
  have hz := (CL.CLFun.zeroOn_exactlyOn (F := F) (univ.map e)ᶜ ℓ (by omega)).supportedOn
  rw [depthFamily, family, (supported_embed e (L w) univ (hL w)).eval_directSum hz
    (Finset.disjoint_left.mpr fun i hi hci => (Finset.mem_compl.mp hci) hi), CL.CLFun.eval_zeroOn, add_zero]
end
end MIPRE.Introspection.SourcePadding

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost
/-- A full-register output equals a zero-extended source output exactly when
its suffix is zero and its retained prefix agrees. -/
theorem source_bits_iff {s Q : ℕ} (h : s ≤ Q) (y : Fin Q → CL.𝔽₂) (x : Fin s → CL.𝔽₂) :
    SourceCompiler.InSource s (CL.toBits y) ∧ (CL.toBits y).take s = CL.toBits x ↔
      y = CL.push (firstEmbedding h) x := by
  constructor
  · rintro ⟨hs,he⟩
    apply toBits_injective
    rw [toBits_push_first,SourceCompiler.InSource_padding (CL.length_toBits y) hs,he]
  · intro he
    subst y
    rw [toBits_push_first]
    simp [SourceCompiler.InSource,CL.length_toBits]
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts)
theorem marginal_query_size_le (R : ℕ) (hR : 1 ≤ R) (w : Player) (j : ℕ) (z : BitStr)
    (hj : Nat.size j ≤ R) (hz : z.length ≤ R) :
    esize (CL.Sampler.Query.marginal w j z) + 1 ≤ 32 * R := by
  have hw : esize w ≤ 3 := by cases w <;> decide
  have hjb := esize_nat_le j
  have hzb := esize_bitStr_le z
  change esize ((1 : ℕ),w,j,z,([] : BitStr)) + 1 ≤ _
  simp only [esize_prod]
  have hone : esize (1 : ℕ) = 5 := by decide
  have hnil : esize ([] : BitStr) = 1 := rfl
  rw [hone,hnil]
  omega
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts)
/-- A legal marginal query fits the same exponent-five clock as the source
decider. Its level enters through the length of its binary encoding. -/
theorem bounded_marginal_result {ℓ lam n : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) (w : Player) (j : ℕ) (z : BitStr) (hj : 1 ≤ j) (hjℓ : j ≤ ℓ)
    (hjR : Nat.size j ≤ (2^n)^lam) (hz : z.length = V.sampler.dim (2^n)) :
    clockedResult V.sampler.prog (encode (2^n,CL.Sampler.Query.marginal w j z)) (ansBound 5 lam n) =
      .cons (encode true) (encode (CL.toBits
        (((V.sampler.cl (2^n) w).truncate j).eval (CL.ofBits (V.sampler.dim (2^n)) z)))) := by
  have hn' := (two_le_exp_index_iff n).mpr hn
  have hs : z.length ≤ (2^n)^lam := hz ▸ (hV.1 (2^n) hn').1
  have hb := marginal_query_size_le ((2^n)^lam) (Nat.one_le_pow _ _ (by positivity)) w j z hjR hs
  obtain ⟨r,t,ht,hr⟩ := (hV.1 (2^n) hn').2.1 (encode (CL.Sampler.Query.marginal w j z))
  obtain ⟨tu,hu⟩ := V.sampler.runs_marginal (2^n) w j z hj hjℓ hz
  rw [ClockProgram.clockedResult_eq_iff]
  refine ⟨t,ht.trans (size_cost_le (by have := hV.two_le; omega) hn _ hb),?_⟩
  exact (hr.deterministic hu).1 ▸ hr
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts)
theorem samplingResult_marginal {ℓ lam n Q R : ℕ} (V : Verifier ℓ) (hV : V.IsBounded lam)
    (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hℓR : Nat.size ℓ ≤ (2^n)^lam)
    (hQ : V.sampler.dim (2^n) ≤ Q) (w : Bool) (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    samplingResult 5 lam V.sampler.prog
      (ℓ,w,n,Q,R,V.sampler.dim (2^n),AnswerParser.pairBits (CL.toBits y) a,
        AnswerParser.pairBits (CL.toBits z) b) =
      .cons (encode true) (encode (CL.toBits ((V.sampler.cl (2^n) (Player.ofBool w)).eval
        (CL.pull (firstEmbedding hQ) z)))) := by
  rw [samplingResult,samplingCall_apply]
  simp only [inputIndex,inputDim,inputQ,inputRight,rightParts,comp_apply,pair_apply,fst_apply,snd_apply,
    DynamicParser.pairParts_apply,AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]
  have he : ClockSimulation.reindexed (encode
      (n,CL.Sampler.Query.marginal (Player.ofBool w) ℓ
        ((CL.toBits z).take (V.sampler.dim (2^n))))) = encode
      (2^n,CL.Sampler.Query.marginal (Player.ofBool w) ℓ
        ((CL.toBits z).take (V.sampler.dim (2^n)))) := ClockSimulation.reindexed_cons n _
  have hi : ClockSimulation.indexReader (encode
      (n,CL.Sampler.Query.marginal (Player.ofBool w) ℓ
        ((CL.toBits z).take (V.sampler.dim (2^n))))) = n := readNat_encode n
  rw [he,hi,bounded_marginal_result V hV hn (Player.ofBool w) ℓ _ hℓ le_rfl hℓR
    (by simp [List.length_take,Nat.min_eq_left hQ]),ofBits_take_first hQ]
  simp only [CL.CLFun.truncate_self]
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts)
theorem samplingReady_vectors {s Q R ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hs : s ≤ Q)
    (hQ : 4 ≤ Q) (hR : 3*R ≤ Q) (n : ℕ) (w : Bool)
    (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    SamplingReady (ℓ,w,n,Q,R,s,AnswerParser.pairBits (CL.toBits y) a,
      AnswerParser.pairBits (CL.toBits z) b) ↔
      a.length ≤ R ∧ b.length ≤ R ∧ SourceCompiler.InSource s (CL.toBits y) ∧ a = b := by
  simp only [SamplingReady,hℓ,hs,true_and,outerCheck_iff,pairLeft,pairRight,
    inputDim,inputQ,inputR,inputLeft,inputRight,leftParts,rightParts,
    comp_apply,pair_apply,fst_apply,snd_apply,DynamicParser.pairCheck_apply,
    DynamicParser.pairParts_apply,
    AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _)]
  have hp (v : Fin Q → CL.𝔽₂) (c : BitStr) :
      decide (AnswerParser.pairValid Q R (AnswerParser.pairBits (CL.toBits v) c)) = true ↔
        c.length ≤ R := by
    rw [← AnswerParser.pairCheck_apply,AnswerParser.pairCheck_pairBits]
    simp
  rw [hp,hp]
  constructor
  · rintro ⟨_,ha,hb,rest⟩
    exact ⟨ha,hb,rest⟩
  · rintro ⟨ha,hb,rest⟩
    exact ⟨⟨AnswerParser.pairBits_lt_outer Q R hQ hR _ _ (CL.length_toBits _) ha,
      AnswerParser.pairBits_lt_outer Q R hQ hR _ _ (CL.length_toBits _) hb⟩,ha,hb,rest⟩
end
end MIPRE.Introspection.AuxiliaryProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryProgram
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts)
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution {ℓ lam n Q R : ℕ} (U : ClockedUniversalMachine)
    (V : Verifier ℓ) (hV : V.IsBounded lam) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hℓR : Nat.size ℓ ≤ (2^n)^lam) (hs : V.sampler.dim (2^n) ≤ Q)
    (hQ : 4 ≤ Q) (hR : 3*R ≤ Q) (w : Bool) (y z : Fin Q → CL.𝔽₂) (a b : BitStr) :
    (∃ t, (samplingProg 5 lam U V.sampler.prog).Runs
      (encode (ℓ,w,n,Q,R,V.sampler.dim (2^n),AnswerParser.pairBits (CL.toBits y) a,
        AnswerParser.pairBits (CL.toBits z) b)) (encode true) t) ↔
      a.length ≤ R ∧ b.length ≤ R ∧
      CLChecks.sampling (SourcePadding.depthFamily (firstEmbedding hs)
        (fun w => V.sampler.cl (2^n) (Player.ofBool w)) w) (y,a) (z,b) := by
  rw [samplingProg_accepts_iff]
  simp only [SamplingRawReady,readSamplingInput_encode,true_and]
  rw [samplingReady_vectors hℓ hs hQ hR,
    samplingResult_marginal V hV hn hℓ hℓR hs,samplingExpected_apply]
  simp only [inputDim,leftParts,inputQ,inputLeft,comp_apply,pair_apply,fst_apply,snd_apply,
    DynamicParser.pairParts_apply,
    AnswerParser.pairParts_pairBits _ _ _ (CL.length_toBits _),Data.cons.injEq,
    true_and,encode_injective.eq_iff]
  rw [CLChecks.sampling,SourcePadding.depthFamily_eval (firstEmbedding hs)
    (fun w => V.sampler.cl (2^n) (Player.ofBool w)) hℓ
    (fun w => (V.sampler.cl_exactlyOn (2^n) (Player.ofBool w)).supportedOn),
    SourcePadding.family,CL.CLFun.eval_embed]
  constructor
  · rintro ⟨⟨ha,hb,hy,hab⟩,he⟩
    exact ⟨ha,hb,(source_bits_iff hs y _).mp ⟨hy,he.symm⟩,hab⟩
  · rintro ⟨ha,hb,hy,hab⟩
    obtain ⟨hys,he⟩ := (source_bits_iff hs y _).mpr hy
    exact ⟨⟨ha,hb,hys,hab⟩,he.symm⟩
end MIPRE.Introspection.AuxiliaryProgram
