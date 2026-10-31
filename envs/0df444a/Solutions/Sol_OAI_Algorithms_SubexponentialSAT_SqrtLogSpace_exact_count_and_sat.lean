-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:05:16.548991+00:00
-- url     : https://prove2.me/submissions/8454f820-084a-483e-8131-259df6305483

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CompileSpace_compile_word_answer_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_frontend_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeLargeEntry_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete finite CNF syntax and semantics for the candidate SAT argument. -/

namespace SubexponentialSAT.SAT

universe u

variable {V : Type u}

variable [DecidableEq V]

section Decidable

section Finite

variable [Fintype V]

theorem count_le (F : CNF V) : count F ≤ 2 ^ Fintype.card V := by
  calc
    count F ≤ (Finset.univ : Finset (Assignment V)).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ Fintype.card V := by simp [Assignment ]

end Finite
end Decidable
end SubexponentialSAT.SAT

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem encodeList_injective {α : Type*} {enc : α → List Bool}
    (hinj : Function.Injective enc) : Function.Injective (encodeList enc) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs <;> simp_all [encodeList]
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [encodeList] at h
      | cons b bs =>
          have ht : frame (enc a) ++ encodeList enc as =
              frame (enc b) ++ encodeList enc bs := by
            simpa only [encodeList, List.cons.injEq, true_and] using h
          obtain ⟨hab, htail⟩ := frame_append_injective ht
          exact congrArg₂ List.cons (hinj hab) (ih htail)

theorem cnfNumbers_injective {n : ℕ} :
    Function.Injective (cnfNumbers (n := n)) := by
  intro F G h
  apply Finset.image_injective clauseNumbers_injective
  have hs := congrArg List.toFinset h
  simpa [cnfNumbers] using hs

theorem encodeCNFBody_injective {n : ℕ} :
    Function.Injective (encodeCNFBody (n := n)) :=
  (encodeList_injective (encodeList_injective encodeNat_injective)).comp
    cnfNumbers_injective

theorem encodeCNF_injective {n : ℕ} : Function.Injective (encodeCNF (n := n)) := by
  intro F G h
  apply encodeCNFBody_injective
  exact List.append_cancel_left h

theorem encodeCNF_numVariables {n m : ℕ} (F : SAT.CNF (Fin n)) (G : SAT.CNF (Fin m))
    (h : encodeCNF F = encodeCNF G) : n = m := by
  have hr := congrArg (fun bits => (readNat bits).map Prod.fst) h
  simpa [encodeCNF] using hr

theorem formulaBitLength_lower {n : ℕ} (F : SAT.CNF (Fin n)) :
    n + F.card + 2 ≤ formulaBitLength F := by
  have h := length_encodeList_lower (encodeList encodeNat) (cnfNumbers F)
  rw [length_cnfNumbers] at h
  rw [formulaBitLength_eq]
  change F.card + 1 ≤ (encodeCNFBody F).length at h
  omega

theorem numVariables_le_formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) :
    n ≤ formulaBitLength F := by
  have := formulaBitLength_lower F
  omega

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ABI
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed disjoint register and stack banks for the counting machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI

theorem countStack_ne_answerStack : countStack ≠ answerStack := by decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem digits_two_eq_map_toNat (a : ℕ) :
    Nat.digits 2 a = a.bits.map Bool.toNat := by
  rw [Nat.digits_two_eq_bits]
  induction a.bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all

@[simp] theorem countWord_decode (a : ℕ) :
    Nat.ofDigits 2 ((countWord a).map Bool.toNat) = a := by
  by_cases h : a = 0
  · subst a
    rfl
  · rw [countWord, ite_eq_right h, ← digits_two_eq_map_toNat]
    exact Nat.ofDigits_digits 2 a

@[simp] theorem countWord_toNat (a : ℕ) : BinaryArithmetic.toNat (countWord a) = a := by
  have h (word : List Bool) :
      BinaryArithmetic.toNat word = Nat.ofDigits 2 (word.map Bool.toNat) := by
    induction word with
    | nil => rfl
    | cons b word ih =>
        cases b <;> simp [BinaryArithmetic.toNat, BinaryArithmetic.bitVal, ih,
          Nat.ofDigits]
  rw [h, countWord_decode]

theorem countWord_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (countWord a).length ≤ n + 1 := by
  by_cases h : a = 0
  · simp [countWord, h]
  · simpa only [countWord, ite_eq_right h, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

theorem countWord_count_length {n : ℕ} (F : SAT.CNF (Fin n)) :
    (countWord (SAT.count F)).length ≤ n + 1 :=
  countWord_length_le (by simpa using SAT.count_le F)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_StatementScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The exact square-root-logarithm runtime scale

These are numerical definitions and elementary lemmas only.  In particular,
this module supplies no SAT algorithm and makes no computational existence claim.
The logarithms in the target are natural logarithms, including at small inputs.
-/

namespace SubexponentialSAT.SqrtLog.Statement

noncomputable section

theorem runtimeScale_nonneg (n : ℕ) : 0 ≤ runtimeScale n := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
    (Real.sqrt_nonneg _)

theorem runtimeBound_nonneg {constant : ℝ} (hc : 0 ≤ constant)
    (exponentConstant : ℝ) (degree inputBits numVars : ℕ) :
    0 ≤ runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  positivity

theorem runtimeBound_mono_exponent {constant a b : ℝ} (hc : 0 ≤ constant)
    (hab : a ≤ b) (degree inputBits numVars : ℕ) :
    runtimeBound constant a degree inputBits numVars ≤
      runtimeBound constant b degree inputBits numVars := by
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right hab (runtimeScale_nonneg numVars)
  · exact mul_nonneg hc (pow_nonneg (by positivity) degree)

end

end SubexponentialSAT.SqrtLog.Statement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem positivity_eval {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = []) :
    Eval (positivity ports answer) (8 * (a.stacks ports.counter).length + 8)
      a (positivityResult ports answer a) := by
  simpa only [positivity, positivityResult, Nat.add_assoc] using
    Eval.seq (CounterForPrograms.test_eval ports a hs)
      (Eval.base (StructuredProgram.Eval.atom
        (.push answer (ports.register 2)) (CounterForPrograms.testResult ports a)))

theorem positivityResult_stacks {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = []) :
    (positivityResult ports answer a).stacks = Function.update a.stacks answer
      ((!CounterPrograms.isZero (a.stacks ports.counter)) :: a.stacks answer) := by
  simp only [positivityResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    CounterForPrograms.testResult_flag, CounterForPrograms.testResult_stacks ports a hs]

theorem positivityResult_count {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = [])
    (ha : ports.counter ≠ answer) :
    (positivityResult ports answer a).stacks ports.counter = a.stacks ports.counter := by
  rw [positivityResult_stacks ports answer a hs, Function.update_of_ne ha]

theorem positivityResult_answer {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) (hs : a.stacks ports.scratch = [])
    (ha : a.stacks answer = []) :
    (positivityResult ports answer a).stacks answer =
      [decide (0 < BinaryArithmetic.toNat (a.stacks ports.counter))] := by
  rw [positivityResult_stacks ports answer a hs, Function.update_self, ha]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [CounterPrograms.isZero_eq_false_iff, CounterPrograms.value_eq_toNat]

theorem clearOutput_eval (port : Fin 1220) (a : State 80 1220) :
    Eval (clearOutput port) (2 * (a.stacks port).length + 3) a
      (clearOutputState port a) :=
  .call _ (ListRegisterProgram.clear_run port 72 73 a.regs a.stacks)

theorem answerReady_count (a : State 80 1220) :
    (answerReady a).stacks ABI.countStack = a.stacks ABI.countStack := by
  simp [answerReady, clearOutputState, ABI.countStack, ABI.answerStack, ABI.positivityScratch]

theorem answerReady_scratch (a : State 80 1220) :
    (answerReady a).stacks ABI.positivityScratch = [] := by
  simp [answerReady, clearOutputState]

theorem answerReady_answer (a : State 80 1220) :
    (answerReady a).stacks ABI.answerStack = [] := by
  simp [answerReady, clearOutputState, ABI.answerStack, ABI.positivityScratch]

theorem answerCommand_eval (a : State 80 1220) :
    Eval answerCommand (answerSteps a - 1) a (answerResult a) := by
  have hp := positivity_eval positivityPorts ABI.answerStack (answerReady a)
    (answerReady_scratch a)
  have hs := clearOutput_eval ABI.positivityScratch (clearOutputState ABI.answerStack a)
  have ha := clearOutput_eval ABI.answerStack a
  have h := ha.seq (hs.seq hp)
  have he : (clearOutputState ABI.answerStack a).stacks ABI.positivityScratch =
      a.stacks ABI.positivityScratch := by
    simp [clearOutputState, ABI.answerStack, ABI.positivityScratch]
  convert h using 1
  · rfl
  · simp only [answerSteps, positivityPorts, answerReady_count, he]
    omega
  · rfl

theorem answerResult_count (a : State 80 1220) :
    (answerResult a).stacks ABI.countStack = a.stacks ABI.countStack := by
  exact (positivityResult_count positivityPorts ABI.answerStack (answerReady a)
    (answerReady_scratch a) ABI.countStack_ne_answerStack).trans (answerReady_count a)

theorem answerResult_answer (a : State 80 1220) :
    (answerResult a).stacks ABI.answerStack =
      [decide (0 < BinaryArithmetic.toNat (a.stacks ABI.countStack))] := by
  have h := positivityResult_answer positivityPorts ABI.answerStack (answerReady a)
    (answerReady_scratch a) (answerReady_answer a)
  simpa only [answerResult, positivityPorts, answerReady_count] using h

theorem copyWord_eval (src dst scratch : Fin 1220) (a : State 80 1220)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (htd : scratch ≠ dst)
    (hblank : a.stacks scratch = []) :
    Eval (copyWord src dst scratch) (7 * (a.stacks src).length + 5) a
      (copiedWord src dst a) :=
  Eval.call _ (ListRegisterProgram.copy_run src dst scratch 72 73 hsd hst htd
    (by decide) a.regs a.stacks hblank)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
@[simp] theorem decoded_encode (scope : List ℕ) :
    decoded (Encoding.encodeList Encoding.encodeNat scope) = scope := by
  classical
  unfold decoded
  split
  · rename_i h
    exact Encoding.encodeList_injective Encoding.encodeNat_injective (Classical.choose_spec h)
  · rename_i h
    exact (h ⟨scope,rfl⟩).elim

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionRuntime
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical closure lemmas for the actual cutoff and identifier wrappers.
These assign no running time to an unimplemented operation. -/
namespace SubexponentialSAT.SqrtLog.Execution

open Statement

theorem runtimeBound_mono_degree {C A : ℝ} (hC : 0 ≤ C)
    {d e : ℕ} (hde : d ≤ e) (L n : ℕ) :
    runtimeBound C A d L n ≤ runtimeBound C A e L n := by
  unfold runtimeBound
  have hbase : (1 : ℝ) ≤ (L : ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hde) hC)
    (by positivity)

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial time envelopes for the actual conditioned stream. The
same original assembled resource pays the support/tuple work; all remaining
scalars and retained words enter only fixed polynomial coefficients. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
open SqrtLog SubexpLiftRing SubexpQuarticRing
open CostAssembly.Polynomial QueryStreamCorrect


open SqrtLog SqrtLog.Statement



open Filter SqrtLog SqrtLog.Statement


open SqrtLog SqrtLog.Statement
/-- Adding finitely many source phases preserves the same scale. -/
theorem runtimeBound_add_bound (C D A B : ℝ) (d e inputLength n : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    runtimeBound C A d inputLength n + runtimeBound D B e inputLength n ≤
      runtimeBound (C+D) (A+B) (d+e) inputLength n := by
  have hc := (runtimeBound_mono_exponent hC (show A ≤ A+B by linarith)
    d inputLength n).trans (Execution.runtimeBound_mono_degree hC
      (show d ≤ d+e by omega) inputLength n)
  have hd := (runtimeBound_mono_exponent hD (show B ≤ A+B by linarith)
    e inputLength n).trans (Execution.runtimeBound_mono_degree hD
      (show e ≤ d+e by omega) inputLength n)
  apply (add_le_add hc hd).trans_eq
  unfold runtimeBound
  ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

theorem frontendBound_polynomial {n : ℕ} (F : SAT.CNF (Fin n)) :
    frontendBound F ≤ 4000 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  have hn := Encoding.numVariables_le_formulaBitLength F
  have hb : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
    rw [Encoding.formulaBitLength_eq]
    omega
  have hn2 := Nat.pow_le_pow_left hn 2
  have hb2 := Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2
  dsimp [frontendBound, FrontendProgram.initializeBound]
  nlinarith


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FiniteFallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Generic finite scanner selectively adapted from the reviewed canceled source
`CountingDraft/FiniteWordScanner.lean`; no obsolete endpoint or rate is imported.

Fixed finite control for bounded input prefixes and complete binary output words.
The transition table is chosen before any runtime input. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner


theorem bounded_fold (M : ℕ) (pref word : List Bool)
    (h : pref.length + word.length ≤ M) :
    word.foldl (boundedNext M)
      (some ⟨pref, by omega⟩) =
        some ⟨pref ++ word, by simpa using h⟩ := by
  induction word generalizing pref with
  | nil => simp
  | cons bit word ih =>
      have hp : pref.length < M := by
        simp only [List.length_cons] at h
        omega
      have ht : (pref ++ [bit]).length + word.length ≤ M := by
        simp only [List.length_append, List.length_singleton] at *
        simp only [List.length_cons] at h
        omega
      simpa [boundedNext, hp, List.append_assoc] using ih (pref ++ [bit]) ht

theorem bounded_fold_empty (M : ℕ) (word : List Bool) (h : word.length ≤ M) :
    word.foldl (boundedNext M) (some ⟨[], Nat.zero_le M⟩) = some ⟨word, h⟩ := by
  simpa using bounded_fold M [] word (by simpa using h)



open BitProgram

variable {qCount : ℕ}

variable (L : ℕ) (start : Fin qCount) (next : Fin qCount → Bool → Fin qCount)
  (out : Fin qCount → List Bool) (hout : ∀ q, (out q).length ≤ L)

theorem consume (q : Fin qCount) (value present bit : Bool) (word : List Bool) :
    Trace (program L start next out hout) 3
      (cfg L q 0 (by omega) value present (bit :: word))
      (cfg L (next q bit) 0 (by omega) bit true word) := by
  refine .cons (b := cfg L q 1 (by omega) bit true word) ?_
    (.cons (b := cfg L q 2 (by omega) bit true word) ?_ (.cons ?_ (.refl _)))
  · simp [step, program, cfg, execInstr, readRegs]
  · simp [step, program, cfg, execInstr, regs]
  · cases bit <;> simp [step, program, cfg, execInstr, regs]

theorem begin_output (q : Fin qCount) (value present : Bool) :
    Trace (program L start next out hout) 2
      (cfg L q 0 (by omega) value present [])
      (cfg L q 3 (by omega) false false []) := by
  refine .cons (b := cfg L q 1 (by omega) false false []) ?_ (.cons ?_ (.refl _))
  · simp [step, program, cfg, execInstr, readRegs]
  · simp [step, program, cfg, execInstr]

theorem finish_output (q : Fin qCount) (value : Bool) :
    Trace (program L start next out hout) 2
      (cfg L q (2 * (out q).length + 3) (by have := hout q; omega)
        value false (out q))
      (terminal (program L start next out hout) (out q)) := by
  refine .cons (b := cfg L q (2 * (out q).length + 4) (by have := hout q; omega)
    false false (out q)) ?_ (.cons ?_ (.refl _))
  · simp [step, program, cfg, execInstr]
  · simp [step, program, cfg, execInstr, terminal]

theorem emit_pair (q : Fin qCount) (value bit : Bool) (rest done : List Bool)
    (h : out q = (bit :: rest).reverse ++ done) :
    Trace (program L start next out hout) 2
      (cfg L q (2 * done.length + 3) (by have := hout q; simp [h] at this ⊢; omega)
        value false done)
      (cfg L q (2 * (bit :: done).length + 3)
        (by have := hout q; simp [h] at this ⊢; omega) bit false (bit :: done)) := by
  have hlen : (out q).length = rest.length + 1 + done.length := by simp [h]; omega
  have hbit : ((out q).reverse[done.length]?).getD false = bit := by
    simp [h, List.reverse_append]
  have hfirst : 2 * done.length + 3 < 2 * (out q).length + 3 := by omega
  have hsecond : 2 * done.length + 4 < 2 * (out q).length + 3 := by omega
  refine .cons (b := cfg L q (2 * done.length + 4)
    (by have := hout q; omega) bit false done) ?_ (.cons ?_ (.refl _))
  · simp [step, program, cfg, execInstr, hfirst, hbit,
      show 2 * done.length + 3 ≠ 1 by omega,
      show 2 * done.length + 3 ≠ 2 by omega]
  · simp [step, program, cfg, execInstr, hsecond, regs, Nat.mul_add,
      show 2 * done.length + 4 ≠ 1 by omega,
      show 2 * done.length + 4 ≠ 2 by omega]

theorem emit (q : Fin qCount) (rest done : List Bool) (value : Bool)
    (h : out q = rest.reverse ++ done) :
    Trace (program L start next out hout) (2 * rest.length + 2)
      (cfg L q (2 * done.length + 3) (by have := hout q; simp [h] at this ⊢; omega)
        value false done)
      (terminal (program L start next out hout) (out q)) := by
  induction rest generalizing done value with
  | nil => simpa [h] using finish_output L start next out hout q value
  | cons bit rest ih =>
      have hnext : out q = rest.reverse ++ (bit :: done) := by
        simpa [List.reverse_cons, List.append_assoc] using h
      have ht := (emit_pair L start next out hout q value bit rest done h).trans
        (ih (bit :: done) bit hnext)
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem trace (q : Fin qCount) (word : List Bool) (value present : Bool) :
    Trace (program L start next out hout)
      (3 * word.length + 2 * (out (word.foldl next q)).length + 4)
      (cfg L q 0 (by omega) value present word)
      (terminal (program L start next out hout) (out (word.foldl next q))) := by
  induction word generalizing q value present with
  | nil =>
      rw [List.foldl_nil]
      have ht := (begin_output L start next out hout q value present).trans
        (emit L start next out hout q (out q).reverse [] false (by simp))
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      simp only [List.length_reverse, List.length_nil]
      omega
  | cons bit word ih =>
      have ht := (consume L start next out hout q value present bit word).trans
        (ih (next q bit) bit true)
      simpa [List.foldl_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ht

theorem initial_trace (word : List Bool) :
    Trace (program L start next out hout)
      (3 * word.length + 2 * (out (word.foldl next start)).length + 4)
      (initial (program L start next out hout) word)
      (terminal (program L start next out hout) (out (word.foldl next start))) := by
  simpa [initial, program, cfg, regs] using
    trace L start next out hout start word false false


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback

open BitProgram Scanner
open scoped BigOperators

theorem smallEncode_injective (B : ℕ) : Function.Injective (smallEncode (B := B)) := by
  rintro ⟨n, F⟩ ⟨m, G⟩ h
  have hn : n = m := Fin.ext (Encoding.encodeCNF_numVariables F G h)
  subst m
  have hF : F = G := Encoding.encodeCNF_injective h
  subst G
  rfl

theorem tableCount_code (B : ℕ) (G : SmallFormula B) :
    tableCount B (smallEncode G) = SAT.count G.2 := by
  classical
  have heq (F : SmallFormula B) : smallEncode F = smallEncode G ↔ F = G :=
    (smallEncode_injective B).eq_iff
  simp [tableCount, heq]

/-- The real scanner consumes the canonical input and emits every count bit. -/
theorem countProgram_trace (B : ℕ) (F : SmallFormula B) :
    Trace (countProgram B)
      (3 * (smallEncode F).length + 2 * (countWord (SAT.count F.2)).length + 4)
      (initial (countProgram B) (smallEncode F))
      (terminal (countProgram B) (countWord (SAT.count F.2))) := by
  let e := Fintype.equivFin (Option (BoundedWord (inputBound B)))
  have hlen : (smallEncode F).length ≤ inputBound B :=
    length_le_finiteOutputBound _ F
  have heval : (smallEncode F).foldl
      (fun q bit => e (boundedNext (inputBound B) (e.symm q) bit))
      (e (some ⟨[], Nat.zero_le _⟩)) = e (some ⟨smallEncode F, hlen⟩) := by
    rw [List.foldl_hom e (g₁ := boundedNext (inputBound B)) (by intro q bit; simp)]
    rw [bounded_fold_empty _ _ hlen]
  have ht := initial_trace (finiteOutputBound (outputTable B))
    (e (some ⟨[], Nat.zero_le _⟩))
    (fun q bit => e (boundedNext (inputBound B) (e.symm q) bit))
    (fun q => outputTable B (e.symm q))
    (fun q => length_le_finiteOutputBound (outputTable B) (e.symm q)) (smallEncode F)
  rw [heval] at ht
  simpa [countProgram, outputTable, tableCount_code, e] using ht

theorem canonical_count_trace {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B) :
    Trace (countProgram B)
      (3 * Encoding.formulaBitLength F + 2 * (countWord (SAT.count F)).length + 4)
      (initial (countProgram B) (Encoding.encodeCNF F))
      (terminal (countProgram B) (countWord (SAT.count F))) :=
  countProgram_trace B ⟨⟨n, by omega⟩, F⟩

open StructuredCalls

theorem resetScanner_eval (a : State 80 1220) :
    Eval resetScanner 2 a ⟨resetScannerRegs a.regs, a.stacks⟩ :=
  .base (.seq (.atom _ _) (.atom _ _))

/-- The finite scanner is callable after preprocessing, with arbitrary framed
registers and stacks. Its own initial registers are established by real steps. -/
theorem framedCountCommand_eval {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B)
    (a : State 80 1220) (hinput : a.stacks ABI.countStack = Encoding.encodeCNF F) :
    Eval (framedCountCommand B)
      (3 * Encoding.formulaBitLength F + 2 * (countWord (SAT.count F)).length + 6)
      a (scannerState a (countWord (SAT.count F))) := by
  have hs : Function.Injective (fun _ : Fin 1 => ABI.countStack) :=
    fun _ _ _ => Subsingleton.elim _ _
  let frame : State 80 1220 := ⟨resetScannerRegs a.regs, a.stacks⟩
  have he (word : List Bool) :
      embedState (Fin.castAdd 78) (fun _ : Fin 1 => ABI.countStack) frame
        (StructuredProgram.ioState 0 word) = scannerState a word := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 2 78) hs
    · intro i
      fin_cases i <;> simp [scannerState, resetScannerRegs]
    · intro i hi
      rfl
    · intro i
      simp [scannerState, Fin.eq_zero i]
    · intro i hi
      have hne : i ≠ ABI.countStack := fun h => hi ⟨0, h.symm⟩
      simp [scannerState, frame, hne]
  have hc := eval_call_lifted (countProgram B) (Fin.castAdd 78)
    (fun _ : Fin 1 => ABI.countStack) frame (Fin.castAdd_injective 2 78) hs
    (a := StructuredProgram.ioState 0 (Encoding.encodeCNF F))
    (b := StructuredProgram.ioState 0 (countWord (SAT.count F)))
    (canonical_count_trace F hn)
  rw [he, he] at hc
  have hi : scannerState a (Encoding.encodeCNF F) = frame := by
    simp [scannerState, ← hinput, frame]
  rw [hi] at hc
  have ht := (resetScanner_eval a).seq hc
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try rfl
  all_goals omega

theorem framedCommand_eval {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B)
    (a : State 80 1220) (hinput : a.stacks ABI.countStack = Encoding.encodeCNF F) :
    Eval (framedCommand B)
      (3 * Encoding.formulaBitLength F + 10 * (countWord (SAT.count F)).length +
        2 * (a.stacks ABI.answerStack).length +
        2 * (a.stacks ABI.positivityScratch).length + 20)
      a (framedResult a (countWord (SAT.count F))) := by
  have ht := (framedCountCommand_eval F hn a hinput).seq
    (Native.answerCommand_eval (scannerState a (countWord (SAT.count F))))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try rfl
  simp only [Native.answerSteps, scannerState, Function.update_self,
    Function.update_of_ne (show ABI.answerStack ≠ ABI.countStack by decide),
    Function.update_of_ne (show ABI.positivityScratch ≠ ABI.countStack by decide)]
  omega

theorem framedResult_count (a : State 80 1220) (word : List Bool) :
    (framedResult a word).stacks ABI.countStack = word := by
  simp only [framedResult, Native.answerResult_count, scannerState, Function.update_self]

theorem framedResult_answer (a : State 80 1220) (word : List Bool) :
    (framedResult a word).stacks ABI.answerStack =
      [decide (0 < BinaryArithmetic.toNat word)] := by
  simp only [framedResult, Native.answerResult_answer, scannerState, Function.update_self]

theorem cutoff_fold_replicate (B n : ℕ) (q : Fin (B + 2)) :
    ((List.replicate n true).foldl (cutoffNext B) q).val = min (B + 1) (q.val + n) := by
  induction n generalizing q with
  | zero => simp; omega
  | succ n ih =>
    simp only [List.replicate_succ, List.foldl_cons, ih, cutoffNext, ite_true, if_true]
    omega

theorem cutoff_fold_header (B n : ℕ) :
    cutoffOut B ((Encoding.encodeNat n).foldl (cutoffNext B) ⟨0, by omega⟩) =
      [decide (n ≤ B)] := by
  have h := cutoff_fold_replicate B n (⟨0, by omega⟩ : Fin (B + 2))
  simp only [Encoding.encodeNat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    cutoffOut, cutoffNext, Bool.false_eq_true, ite_false, Nat.add_zero]
  simp only [Nat.zero_add] at h
  rw [h]
  have he : min (B + 1) (min (B + 1) n) ≤ B ↔ n ≤ B := by omega
  simp only [he]

theorem cutoffScanner_trace (B n : ℕ) (r : Fin 2 → Bool) :
    Trace (cutoffScanner B) (3 * (Encoding.encodeNat n).length + 6)
      ((⟨r, fun _ => Encoding.encodeNat n⟩ : State 2 1).withPC
        (some (cutoffScanner B).entry))
      ((StructuredProgram.ioState 0 [decide (n ≤ B)]).withPC none) := by
  have hr : Scanner.regs (r 0) (r 1) = r := by
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have h := Scanner.trace 1 (⟨0, by omega⟩ : Fin (B + 2)) (cutoffNext B)
    (cutoffOut B) (by intro q; rfl) ⟨0, by omega⟩ (Encoding.encodeNat n) (r 0) (r 1)
  rw [cutoff_fold_header] at h
  simpa [cutoffScanner, Scanner.cfg, Scanner.program, hr, terminal,
    StructuredProgram.ioState, StructuredProgram.State.withPC] using h

theorem cutoffPrepare_eval (a : State 80 1220) :
    Eval cutoffPrepare (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 6)
      a (cutoffPrepared a) := by
  have h := (Native.clearOutput_eval 270 a).seq
    (Native.clearOutput_eval 271 (Native.clearOutputState 270 a))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try rfl
  simp [Native.clearOutputState]
  omega

theorem cutoffCommand_eval (B n : ℕ) (a : State 80 1220)
    (hn : a.stacks 258 = Encoding.encodeNat n) :
    Eval (cutoffCommand B)
      (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 10 * n + 28)
      a (cutoffResult a (decide (n ≤ B))) := by
  have hcopy := Native.copyWord_eval 258 270 271 (cutoffPrepared a)
    (by decide) (by decide) (by decide)
    (by simp [cutoffPrepared, Native.clearOutputState])
  have hs : Function.Injective (fun _ : Fin 1 => (270 : Fin 1220)) :=
    fun _ _ _ => Subsingleton.elim _ _
  have hp : projectState cutoffRegs (fun _ : Fin 1 => (270 : Fin 1220)) (cutoffCopied a) =
      (⟨(cutoffCopied a).regs ∘ cutoffRegs, fun _ => Encoding.encodeNat n⟩ : State 2 1) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      simp [projectState, cutoffCopied, Native.copiedWord, StackRoutines.copyStacks,
        cutoffPrepared, Native.clearOutputState, hn]
  have ht := cutoffScanner_trace B n ((cutoffCopied a).regs ∘ cutoffRegs)
  rw [← hp] at ht
  have hscan := eval_call_from_state (cutoffScanner B) cutoffRegs
    (fun _ : Fin 1 => (270 : Fin 1220)) (cutoffCopied a) cutoffRegs.injective hs ht
  have hpop := Eval.base (StructuredProgram.Eval.atom (.pop (270 : Fin 1220) 75 76)
    (cutoffScanned a (decide (n ≤ B))))
  have h := (cutoffPrepare_eval a).seq (hcopy.seq (hscan.seq hpop))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals try rfl
  simp only [cutoffPrepared, Native.clearOutputState, Function.update_of_ne
    (show (258 : Fin 1220) ≠ 271 by decide), Function.update_of_ne
    (show (258 : Fin 1220) ≠ 270 by decide), hn, Encoding.length_encodeNat]
  omega

theorem cutoffScanned_word (a : State 80 1220) (flag : Bool) :
    (cutoffScanned a flag).stacks 270 = [flag] :=
  embedState_stack _ _ _ _ (fun _ _ _ => Subsingleton.elim _ _) 0

theorem cutoffScanned_frame (a : State 80 1220) (flag : Bool) (i : Fin 1220)
    (hi : i ≠ 270) : (cutoffScanned a flag).stacks i = (cutoffCopied a).stacks i :=
  embedState_stack_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi hj.symm)

@[simp] theorem cutoffResult_flag (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).regs 75 = flag := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,
    execInstr, cutoffScanned_word, readRegs]

@[simp] theorem cutoffResult_work (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).stacks 270 = [] := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,
    execInstr, cutoffScanned_word]

@[simp] theorem cutoffResult_scratch (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).stacks 271 = [] := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    cutoffScanned_frame a flag 271 (by decide), cutoffCopied, Native.copiedWord,
    StackRoutines.copyStacks, cutoffPrepared, Native.clearOutputState]

theorem cutoffResult_frame (a : State 80 1220) (flag : Bool) (i : Fin 1220)
    (hw : i ≠ 270) (hs : i ≠ 271) : (cutoffResult a flag).stacks i = a.stacks i := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, hw,
    cutoffScanned_frame a flag i hw, cutoffCopied, Native.copiedWord,
    StackRoutines.copyStacks, cutoffPrepared, Native.clearOutputState, hs]

theorem dispatch_small_eval {B n : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (hn : n ≤ B) (a : State 80 1220)
    (hheader : a.stacks 258 = Encoding.encodeNat n)
    (hinput : a.stacks ABI.countStack = Encoding.encodeCNF F) :
    Eval (dispatchCommand B large)
      (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 10 * n +
        3 * Encoding.formulaBitLength F + 10 * (countWord (SAT.count F)).length +
        2 * (a.stacks ABI.answerStack).length +
        2 * (a.stacks ABI.positivityScratch).length + 49)
      a (framedResult (cutoffResult a true) (countWord (SAT.count F))) := by
  have hcut := cutoffCommand_eval B n a hheader
  simp only [decide_eq_true hn] at hcut
  have hc := framedCommand_eval F hn (cutoffResult a true)
    ((cutoffResult_frame a true ABI.countStack (by decide) (by decide)).trans hinput)
  have ht : Eval (dispatchCommand B large) _ a
      (framedResult (cutoffResult a true) (countWord (SAT.count F))) :=
    hcut.seq (Eval.ite_true (cutoffResult_flag a true) hc)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  rw [cutoffResult_frame a true ABI.answerStack (by decide) (by decide),
    cutoffResult_frame a true ABI.positivityScratch (by decide) (by decide)]
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The canonical frontend and actual fixed-cutoff dispatcher share one finite
program. The large command is supplied by the subsequent concrete integration. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

/-- Small inputs run the actual finite counting table and positivity scan after
the paid canonical frontend, retaining the ambient variable universe. -/
theorem entry_small_eval {cutoff n : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (hn : n ≤ cutoff) :
    ∃ steps b, Eval (entryCommand cutoff large) steps
        (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b ∧
      b.stacks ABI.countStack = countWord (SAT.count F) ∧
      b.stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
      steps + 1 ≤ 4100 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  obtain ⟨binary, steps, a, _, _, ht, he, ready⟩ := frontend_eval F
  have hdispatch := FiniteFallback.dispatch_small_eval large F hn a ready.header ready.input
  have h270 := ready.blank 270 (by decide) (by decide) (by decide) (by decide)
  have h271 := ready.blank 271 (by decide) (by decide) (by decide) (by decide)
  have ha := ready.blank ABI.answerStack (by decide) (by decide) (by decide) (by decide)
  have hs := ready.blank ABI.positivityScratch (by decide) (by decide) (by decide) (by decide)
  rw [h270, h271, ha, hs] at hdispatch
  refine ⟨_, _, he.seq hdispatch, FiniteFallback.framedResult_count _ _, ?_, ?_⟩
  · rw [FiniteFallback.framedResult_answer, countWord_toNat]
  · have hfront := ht.trans (frontendBound_polynomial F)
    have hword := countWord_count_length F
    have hnL := Encoding.numVariables_le_formulaBitLength F
    simp only [List.length_nil] at *
    nlinarith

theorem entry_small_trace {cutoff n : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (hn : n ≤ cutoff) :
    ∃ (steps : ℕ) (b : State 80 1220), Trace (entryProgram cutoff large) steps
        (initial (entryProgram cutoff large) (Encoding.encodeCNF F)) (b.withPC none) ∧
      b.stacks ABI.countStack = countWord (SAT.count F) ∧
      b.stacks ABI.answerStack = [decide (0 < SAT.count F)] ∧
      steps ≤ 4100 * (Encoding.formulaBitLength F + 1) ^ 2 ∧
      ∀ prefixSteps c, prefixSteps ≤ steps →
        Trace (entryProgram cutoff large) prefixSteps
          (initial (entryProgram cutoff large) (Encoding.encodeCNF F)) c →
        ∀ i, (c.stacks i).length ≤
          Encoding.formulaBitLength F + 4100 * (Encoding.formulaBitLength F + 1) ^ 2 := by
  obtain ⟨steps, b, he, hc, ha, ht⟩ := entry_small_eval large F hn
  refine ⟨steps + 1, b, compiled_halt_trace he ABI.countStack ABI.answerStack, hc, ha, ht, ?_⟩
  intro prefixSteps c hp htrace i
  exact StructuredSpace.local_stack_bound (entryProgram cutoff large)
    (steps := 4100 * (Encoding.formulaBitLength F + 1) ^ 2)
    (show dataBits (initial (entryProgram cutoff large) (Encoding.encodeCNF F)) ≤
      Encoding.formulaBitLength F by simp [Encoding.formulaBitLength])
    prefixSteps c (hp.trans ht) htrace i

/-- The actual small branch of the unified program produces both physical
outputs on the same primitive run, with all-prefix visited-cell space. -/
theorem entry_small_primitive {cutoff n : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (hn : n ≤ cutoff) :
    ∃ time : ℕ, ∃ final : LocatedCfg (GuardedCompiler.primitive (entryProgram cutoff large)),
      Computation.Trace (locatedStep (GuardedCompiler.primitive (entryProgram cutoff large)))
        time (locatedInit (GuardedCompiler.primitive (entryProgram cutoff large))
          (Encoding.encodeCNF F)) final ∧
      final.config.state = .inl (decide (0 < SAT.count F)) ∧
      final.config.tapes ABI.countStack =
        Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
      final.config.tapes ABI.answerStack =
        Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
      time ≤ 28700 * (Encoding.formulaBitLength F + 1) ^ 2 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace
          (locatedStep (GuardedCompiler.primitive (entryProgram cutoff large))) prefixSteps
          (locatedInit (GuardedCompiler.primitive (entryProgram cutoff large))
            (Encoding.encodeCNF F)) intermediate →
        visitedSpace intermediate ≤ 1220 * (2 * Encoding.formulaBitLength F +
          4100 * (Encoding.formulaBitLength F + 1) ^ 2 + 15) := by
  obtain ⟨steps, b, htrace, hcount, hanswer, htime, hspace⟩ := entry_small_trace large F hn
  obtain ⟨time, ht, final, hrun, hhalt, hc, ha, hs⟩ :=
    CompileSpace.compile_word_answer_space (entryProgram cutoff large) ABI.countStack
      htrace rfl hcount hanswer hspace
  refine ⟨time, final, hrun, hhalt, hc, ha, ?_, ?_⟩
  · calc
      time ≤ 7 * steps := ht
      _ ≤ 7 * (4100 * (Encoding.formulaBitLength F + 1) ^ 2) :=
        Nat.mul_le_mul_left 7 htime
      _ = _ := by ring
  · intro prefixSteps intermediate hp htr
    have h := hs prefixSteps intermediate hp htr
    change visitedSpace intermediate ≤ 1220 *
      (Encoding.formulaBitLength F + 4100 * (Encoding.formulaBitLength F + 1) ^ 2 +
        Encoding.formulaBitLength F + 15) at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeOuterBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The exact large-entry arithmetic join: paid canonical frontend, fixed
cutoff test, actual setup, disjoint DFS, full-word positivity and factor-seven
primitive compilation. These numerical bounds introduce no run contract. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
open OAI BitProgram StructuredCalls SqrtLog.Statement DisjointReuse

/-- One positive triple of constants covers both the actual large-run time
and the fixed finite fallback, uniformly including ambient n=0. -/
theorem runtime_with_fallback (C A : ℝ) (d : ℕ) (hC : 1≤C) (hA : 0≤A) :
    0<C+28700 ∧ 0<A+1 ∧ 0<d+2 ∧ ∀ n L : ℕ,
      runtimeBound C A d L n ≤ runtimeBound (C+28700) (A+1) (d+2) L n ∧
      ((28700*(L+1)^2 : ℕ) : ℝ) ≤ runtimeBound (C+28700) (A+1) (d+2) L n := by
  refine ⟨by linarith,by linarith,by omega,?_⟩
  intro n L
  have hsum : runtimeBound C A d L n+runtimeBound 28700 0 2 L n≤
      runtimeBound (C+28700) (A+1) (d+2) L n := by
    apply (QueryStreamBudgets.runtimeBound_add_bound C 28700 A 0 d 2 L n
      (by linarith) (by norm_num) hA (by norm_num)).trans
    simpa only [add_zero] using runtimeBound_mono_exponent
      (by linarith : 0≤C+28700) (by linarith : A≤A+1) (d+2) L n
  refine ⟨(le_add_of_nonneg_right (runtimeBound_nonneg (by norm_num) 0 2 L n)).trans hsum,?_⟩
  have h := (le_add_of_nonneg_left
    (runtimeBound_nonneg (by linarith : 0≤C) A d L n)).trans hsum
  simpa only [runtimeBound,zero_mul,Real.rpow_zero,mul_one,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using h

/-- The same fixed positive polynomial covers all large primitive visited
space and the actual finite fallback. No runtime or visit count is used. -/
theorem space_with_fallback (S : ℝ) (e : ℕ) (hS : 0≤S) :
    0<S+5022741 ∧ 0<e+2 ∧ ∀ L : ℕ,
      S*((L : ℝ)+1)^e≤(S+5022741)*((L : ℝ)+1)^(e+2) ∧
      ((5022740*(L+1)^2 : ℕ) : ℝ)≤(S+5022741)*((L : ℝ)+1)^(e+2) := by
  refine ⟨by linarith,by omega,?_⟩
  intro L
  have hbase : (1 : ℝ)≤(L : ℝ)+1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have he := pow_le_pow_right₀ hbase (show e≤e+2 by omega)
  have htwo := pow_le_pow_right₀ hbase (show 2≤e+2 by omega)
  refine ⟨mul_le_mul (by linarith) he (by positivity) (by linarith),?_⟩
  have h : (5022740 : ℝ)*((L : ℝ)+1)^2≤(S+5022741)*((L : ℝ)+1)^(e+2) :=
    mul_le_mul (by linarith) htwo (by positivity) (by linarith)
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeOuterBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Final
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact counting and SAT on one fixed primitive run, with the unchanged
ETH square-root-log time scale and polynomial all-prefix visited space. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem compiled_exact_count_and_sat (k : ℕ) (hk : 2 ≤ k) :
    ∃ (labels : ℕ) (program : BitProgram.Program 80 1220 labels)
      (C A S : ℝ) (d e : ℕ),
      program.outputStack = 1216 ∧
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
        ∃ (time : ℕ) (final : LocatedCfg (GuardedCompiler.primitive program)),
          Computation.Trace (locatedStep (GuardedCompiler.primitive program)) time
            (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F)) final ∧
          final.config.tapes (256 : Fin 1220) =
            Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
          final.config.tapes (1216 : Fin 1220) =
            Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
          final.config.state = Sum.inl (decide (0 < SAT.count F)) ∧
          BinaryArithmetic.toNat (countWord (SAT.count F)) = SAT.count F ∧
          (countWord (SAT.count F)).length ≤ n + 1 ∧
          (time : ℝ) ≤ OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength F) n ∧
          ∀ (prefixSteps : ℕ)
            (intermediate : LocatedCfg (GuardedCompiler.primitive program)), prefixSteps ≤ time →
            Computation.Trace (locatedStep (GuardedCompiler.primitive program)) prefixSteps
              (locatedInit (GuardedCompiler.primitive program) (Encoding.encodeCNF F))
              intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e := by
  obtain ⟨cutoff, C, A, d, S, e, hC, hA, hlarge⟩ := NativeLargeEntry.run k hk
  obtain ⟨hC', hA', hd', htimeBound⟩ :=
    NativeOuterBudgets.runtime_with_fallback C A d hC (by linarith)
  obtain ⟨hS', he', hspaceBound⟩ :=
    NativeOuterBudgets.space_with_fallback (S : ℝ) e (Nat.cast_nonneg S)
  refine ⟨_, Native.countingProgram cutoff k (NativeLeafProgram.command k),
    C + 28700, A + 1, (S : ℝ) + 5022741, d + 2, e + 2,
    rfl, hC', hA', hS', hd', he', ?_⟩
  intro n F hw
  by_cases hn : n ≤ cutoff
  · obtain ⟨time, final, htrace, hhalt, hcount, hanswer, htime, hprefix⟩ :=
      Native.entry_small_primitive (Native.outerCommand k (NativeLeafProgram.command k)) F hn
    refine ⟨time, final, htrace, hcount, hanswer, hhalt,
      countWord_toNat _, countWord_count_length F, ?_, ?_⟩
    · exact (Nat.cast_le.mpr htime).trans (htimeBound n (Encoding.formulaBitLength F)).2
    · intro prefixSteps intermediate hp htr
      have hsmall := hprefix prefixSteps intermediate hp htr
      have hpoly : 1220 * (2 * Encoding.formulaBitLength F +
          4100 * (Encoding.formulaBitLength F + 1) ^ 2 + 15) ≤
          5022740 * (Encoding.formulaBitLength F + 1) ^ 2 := by
        have hbase : Encoding.formulaBitLength F + 1 ≤
            (Encoding.formulaBitLength F + 1) ^ 2 := Nat.le_self_pow (by decide) _
        omega
      exact (Nat.cast_le.mpr (hsmall.trans hpoly)).trans
        (hspaceBound (Encoding.formulaBitLength F)).2
  · obtain ⟨time, final, htrace, hhalt, hcount, hanswer, htime, hprefix⟩ :=
      hlarge n F hw (by omega)
    refine ⟨time, final, htrace, hcount, hanswer, hhalt,
      countWord_toNat _, countWord_count_length F,
      htime.trans (htimeBound n (Encoding.formulaBitLength F)).1, ?_⟩
    intro prefixSteps intermediate hp htr
    have hreal : (visitedSpace intermediate : ℝ) ≤
        (S : ℝ) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e := by
      exact_mod_cast hprefix prefixSteps intermediate hp htr
    exact hreal.trans (hspaceBound (Encoding.formulaBitLength F)).1

/-- One fixed primitive machine exactly counts every bounded-width formula,
decides satisfiability, meets the square-root-logarithmic time bound, and uses
only polynomially many visited tape cells at every execution prefix. -/
theorem exact_count_and_sat_oai (k : ℕ) (hk : 2 ≤ k) :
    ∃ (machine : Computation.PrimitiveMachine)
      (countTape answerTape : Fin machine.tapeCount)
      (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
        ∃ (time : ℕ) (final : LocatedCfg machine),
          Computation.Trace (locatedStep machine) time
            (locatedInit machine (Encoding.encodeCNF F)) final ∧
          final.config.tapes countTape =
            Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
          final.config.tapes answerTape =
            Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
          final.config.state = Sum.inl (decide (0 < SAT.count F)) ∧
          BinaryArithmetic.toNat (countWord (SAT.count F)) = SAT.count F ∧
          (countWord (SAT.count F)).length ≤ n + 1 ∧
          (time : ℝ) ≤ OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound C A d
            (Encoding.formulaBitLength F) n ∧
          ∀ (prefixSteps : ℕ) (intermediate : LocatedCfg machine),
            prefixSteps ≤ time →
            Computation.Trace (locatedStep machine) prefixSteps
              (locatedInit machine (Encoding.encodeCNF F)) intermediate →
            (visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength F : ℝ) + 1) ^ e := by
  obtain ⟨labels, program, C, A, S, d, e, _hout, hC, hA, hS, hd, he, hrun⟩ :=
    compiled_exact_count_and_sat k hk
  refine ⟨GuardedCompiler.primitive program, (256 : Fin 1220), (1216 : Fin 1220),
    C, A, S, d, e, hC, hA, hS, hd, he, ?_⟩
  exact hrun

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat_oai
