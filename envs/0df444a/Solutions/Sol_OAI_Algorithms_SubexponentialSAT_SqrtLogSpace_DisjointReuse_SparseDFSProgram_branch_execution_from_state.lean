-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:07:11.80688+00:00
-- url     : https://prove2.me/submissions/1b7267d0-481d-48f1-b915-b1c36a4f6520

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DisjointBranchProgram_program_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DisjointBranchProgram_resultB_length_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFRecords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control skipping of framed CNF records

The program below has three Boolean registers, one Boolean stack, and eleven
fixed labels. It consumes an escaped frame or one tagged list item without
materializing the payload. The payload may itself encode a list of literals,
a clause, or a more deeply nested record. Every bound is proved for actual
`BitProgram.step` traces, rather than assigned to a semantic list operation.
-/

namespace SubexponentialSAT.ExecCNFRecords
open SubexponentialSAT.BitProgram

theorem capture_pop_start (b v p : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 0) v p (b :: input) output scratch) =
      some (copyCfg (some 1) b true input output scratch) := by
  simp [step, copyCfg, execInstr, readRegs]

theorem capture_present_start (v : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 1) v true input output scratch) =
      some (copyCfg (some 2) v true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_true_start (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 2) true true input output scratch) =
      some (copyCfg (some 3) true true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_push_start (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 3) true true input output scratch) =
      some (copyCfg (some 4) true true input output (true :: scratch)) := by
  simp [step, copyCfg, execInstr]

theorem capture_prefix (v p : Bool) (input output scratch : List Bool) :
    Trace captureProgram 4 (copyCfg (some 0) v p (true :: input) output scratch)
      (copyCfg (some 4) true true input output (true :: scratch)) :=
  .cons (capture_pop_start true v p input output scratch)
    (.cons (capture_present_start true input output scratch)
      (.cons (capture_true_start input output scratch)
        (.cons (capture_push_start input output scratch) (.refl _))))

theorem capture_record_trace (bits rest output scratch : List Bool) (v p : Bool) :
    Trace captureProgram (7 * bits.length + 9)
      (copyCfg (some 0) v p (true :: (Encoding.frame bits ++ rest)) output scratch)
      (copyCfg none false true rest output ((true :: Encoding.frame bits).reverse ++ scratch)) := by
  have h := (capture_prefix v p (Encoding.frame bits ++ rest) output scratch).trans
    (capture_frame_trace bits rest output (true :: scratch) true true)
  have ht : 4 + (7 * bits.length + 5) = 7 * bits.length + 9 := by omega
  simpa only [ht, List.reverse_cons, List.append_assoc, List.singleton_append] using h

/-- Copy a tagged record in original encoded order; scratch is restored empty. -/
theorem copy_record_trace (bits rest output : List Bool) (v p : Bool) :
    Trace copyProgram (13 * bits.length + 18)
      (copyCfg (some 0) v p (true :: (Encoding.frame bits ++ rest)) output [])
      (copyCfg none false false rest ((true :: Encoding.frame bits) ++ output) []) := by
  have hp : Trace captureProgram (7 * bits.length + 9)
      (copyCfg (some 0) v p (true :: (Encoding.frame bits ++ rest)) output [])
      (copyCfg none false true rest output (true :: Encoding.frame bits).reverse) := by
    simpa using capture_record_trace bits rest output [] v p
  have hq : Trace restoreCapturedProgram (3 * (true :: Encoding.frame bits).length + 3)
      (ProgramLinking.enter restoreCapturedProgram
        (copyCfg (l := 12) none false true rest output (true :: Encoding.frame bits).reverse))
      (copyCfg none false false rest ((true :: Encoding.frame bits) ++ output) []) := by
    simpa [ProgramLinking.enter, restoreCapturedProgram, StackRoutines.transferProgram, copyCfg]
      using restoreCaptured_trace rest output (true :: Encoding.frame bits).reverse false true
  have h := ProgramLinking.link_trace captureProgram restoreCapturedProgram hp rfl hq
  have hc : (7 * bits.length + 9) + (3 * (true :: Encoding.frame bits).length + 3) =
      13 * bits.length + 18 := by
    simp only [List.length_cons, Encoding.length_frame]
    omega
  have hzero : Fin.castAdd 4 (0 : Fin 12) = (0 : Fin 16) := rfl
  simpa only [hc, copyProgram, ProgramLinking.relabelCfg, ProgramLinking.relocatePc,
    copyCfg, hzero]
    using h

end SubexponentialSAT.ExecCNFRecords

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFSemanticHelpers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact list identities used when composing executable CNF filters. -/
namespace SubexponentialSAT.Encoding
universe u

/-- Filtering discards complete frames; this bound needs no property of the
payload encoder. -/
theorem length_encodeList_filter_le {α : Type u} (enc : α → List Bool)
    (keep : α → Bool) (values : List α) :
    (encodeList enc (values.filter keep)).length ≤ (encodeList enc values).length := by
  induction values with
  | nil => simp
  | cons a values ih =>
    cases h : keep a with
    | false =>
      simp [ h, length_encodeList_cons] ; omega
    | true =>
      simp [ h, length_encodeList_cons] ; omega

end SubexponentialSAT.Encoding

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

/-- Clause deduplication retains a subsequence of the original payloads. -/
theorem length_encodeList_dedupClauses_le (enc : Clause α → List Bool) (F : Formula α) :
    (Encoding.encodeList enc (dedupClauses F)).length ≤
      (Encoding.encodeList enc F).length := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    by_cases h : F.any (fun D => equivalent C D) = true
    · simp [dedupClauses, h, Encoding.length_encodeList_cons] ; omega
    · simp [dedupClauses, h, Encoding.length_encodeList_cons] ; omega

/-- Absorption cannot increase the serialized formula length, even when the
payload encoder uses unequal-length clause encodings. -/
theorem length_encodeList_absorb_le (enc : Clause α → List Bool) (F : Formula α) :
    (Encoding.encodeList enc (absorb F)).length ≤
      (Encoding.encodeList enc F).length := by
  unfold absorb
  exact (Encoding.length_encodeList_filter_le enc _ _).trans
    (length_encodeList_dedupClauses_le enc F)

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCoreChildProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual encoded construction of the core child

The caller supplies a forward encoded core clause on stack 9, an encoded
selected family on stack 12, and the parent formula on stack 13. All other
stacks are empty. The program builds the core record, removes every clause
equivalent to a selected clause, restores record order, and calls the concrete
absorber. The result is on stack 13; every other stack is empty.

The finite program does not depend on any of its three input values. The
equivalence tests, framing, reversal, and absorption are actual bit programs.
-/

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram


/-- The returned child adds at most the serialized core record to the parent
length. This is independent of list order and duplicate literal encodings. -/
theorem result_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (result F selected H)).length ≤
      (formulaCode F).length + 2 * (clauseCode H).length + 2 := by
  have hfilter := Encoding.length_encodeList_filter_le clauseCode
    (fun C => !(selected.any fun D => ExecCNF.equivalent C D)) F
  have habsorb := ExecCNF.length_encodeList_absorb_le clauseCode
    (H :: ExecCNF.eraseClauses F selected)
  change (formulaCode (ExecCNF.eraseClauses F selected)).length ≤ (formulaCode F).length at hfilter
  change (formulaCode (result F selected H)).length ≤
    (Encoding.encodeList clauseCode (H :: ExecCNF.eraseClauses F selected)).length at habsorb
  rw [Encoding.length_encodeList_cons] at habsorb
  change (formulaCode (result F selected H)).length ≤ 2 * (clauseCode H).length + 2 +
    (formulaCode (ExecCNF.eraseClauses F selected)).length at habsorb
  omega

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecWorklistProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Local encoded worklist updates by a fixed Boolean-stack program

The branch decision and child records are supplied as data. No formula search
or splitting callback is an instruction. Pending work, accumulated leaves, and
both child sources may have arbitrary suffixes; only the current records are
read. The five stack ports are pending, leaves, child A, child B, and scratch.
-/

namespace SubexponentialSAT.ExecWorklistProgram

open BitProgram StructuredCalls

private theorem extend_eq {α β γ : Type*} {f : α → β}
    (hf : Function.Injective f) (inner : α → γ) (frame target : β → γ)
    (hin : ∀ i, target (f i) = inner i)
    (hout : ∀ i, (¬ ∃ j, f j = i) → target i = frame i) :
    Function.extend f inner frame = target := by
  classical
  funext i
  by_cases hi : ∃ j, f j = i
  · obtain ⟨j,rfl⟩ := hi
    rw [hf.extend_apply]
    exact (hin j).symm
  · rw [Function.extend_apply' _ _ _ hi]
    exact (hout i hi).symm

private theorem embed_eq {r s R S : ℕ} (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame target : StructuredProgram.State R S) (inner : StructuredProgram.State r s)
    (hri : ∀ i, target.regs (reg i) = inner.regs i)
    (hro : ∀ i, (¬ ∃ j, reg j = i) → target.regs i = frame.regs i)
    (hsi : ∀ i, target.stacks (stk i) = inner.stacks i)
    (hso : ∀ i, (¬ ∃ j, stk j = i) → target.stacks i = frame.stacks i) :
    embedState reg stk frame inner = target := by
  have he₁ := extend_eq hr inner.regs frame.regs target.regs hri hro
  have he₂ := extend_eq hs inner.stacks frame.stacks target.stacks hsi hso
  cases target
  simp only [embedState, he₁, he₂]

theorem workRegs_injective : Function.Injective workRegs := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [workRegs]

theorem copyPorts_injective (src dst : Fin 5)
    (hsd : src ≠ dst) (hst : src ≠ 4) (hdt : dst ≠ 4) :
    Function.Injective (copyPorts src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copyPorts]

/-- A framed copy reads one record only, including when the source contains
more records. The exact trace is inherited from the actual fixed copy program. -/
theorem copyAt_eval (src dst : Fin 5)
    (hsd : src ≠ dst) (hst : src ≠ 4) (hdt : dst ≠ 4)
    (d : Data) (bits rest : List Bool)
    (hsrc : d.stacks src = record bits ++ rest) (htmp : d.stacks 4 = []) :
    Eval (.call (copyAt src dst)) (13 * bits.length + 18) d (copyAfter src dst bits rest d) := by
  let a : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
      ExecCNFRecords.ports (record bits ++ rest) (d.stacks dst) []⟩
  let b : StructuredProgram.State 2 3 :=
    ⟨ParserProgram.pair false false, ExecCNFRecords.ports rest (record bits ++ d.stacks dst) []⟩
  have hr := workRegs_injective
  have hs := copyPorts_injective src dst hsd hst hdt
  have ha : embedState workRegs (copyPorts src dst) d a = d := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
    · intro i; fin_cases i
      · exact hsrc
      · rfl
      · exact htmp
    · intro i hi; rfl
  have hb : embedState workRegs (copyPorts src dst) d b = copyAfter src dst bits rest d := by
    apply embed_eq _ _ hr hs
    · intro i; fin_cases i <;> simp [copyAfter, workRegs, b, ParserProgram.pair]
    · intro i hi
      have h0 : i ≠ 0 := by intro he; exact hi ⟨0, he.symm⟩
      have h1 : i ≠ 1 := by intro he; exact hi ⟨1, he.symm⟩
      simp [copyAfter, h0, h1]
    · intro i; fin_cases i <;>
        simp [copyAfter, copyPorts, b, hsd, hst.symm, hdt.symm, htmp]
    · intro i hi
      have hsrc' : i ≠ src := by intro he; exact hi ⟨0, he.symm⟩
      have hdst' : i ≠ dst := by intro he; exact hi ⟨1, he.symm⟩
      simp [copyAfter, hsrc', hdst']
  have ht : Trace ExecCNFRecords.copyProgram (13 * bits.length + 18)
      (a.withPC (some ExecCNFRecords.copyProgram.entry)) (b.withPC none) := by
    convert ExecCNFRecords.copy_record_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1) using 1 <;>
      simp [a, b, StructuredProgram.State.withPC, ExecCNFRecords.copyCfg, record,
        List.cons_append ]
  have he := eval_call_lifted ExecCNFRecords.copyProgram workRegs (copyPorts src dst) d hr hs ht
  rw [ha, hb] at he
  exact he

private theorem data_ext (a b : Data) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

@[simp] theorem copyAfter_emit (terminal v p f : Bool)
    (bits rest leaves left right : List Bool) :
    copyAfter 0 1 bits rest (data terminal v p f (record bits ++ rest) leaves left right) =
      data terminal false false f rest (record bits ++ leaves) left right := by
  apply data_ext <;> funext i <;> fin_cases i <;> simp [copyAfter ]

@[simp] theorem copyAfter_right (terminal v p f : Bool)
    (bits rest pending leaves left : List Bool) :
    copyAfter 3 0 bits rest (data terminal v p f pending leaves left (record bits ++ rest)) =
      data terminal false false f (record bits ++ pending) leaves left rest := by
  apply data_ext <;> funext i <;> fin_cases i <;> simp [copyAfter ]

@[simp] theorem copyAfter_left (terminal v p f : Bool)
    (bits rest pending leaves right : List Bool) :
    copyAfter 2 0 bits rest (data terminal v p f pending leaves (record bits ++ rest) right) =
      data terminal false false f (record bits ++ pending) leaves rest right := by
  apply data_ext <;> funext i <;> fin_cases i <;> simp [copyAfter ]

end SubexponentialSAT.ExecWorklistProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseFrontierProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete LIFO storage for normalized formula bodies.

Stack zero is the current body, stack two is the framed pending list, and stack
three is scratch. Stack one is preserved and may hold the declared variable
count. The list's final false bit is retained; emptiness is tested by peeking,
so an empty frontier never causes an unguarded removal of a sentinel.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram

open BitProgram StructuredCalls SubexpPostfixControl

theorem pushPair_eval (left right saved pending : List Bool) (terminal v p flag : Bool) :
    Eval pushPair (13 * right.length + 13 * left.length + 36)
      (ExecWorklistProgram.data terminal v p flag pending saved
        (ExecWorklistProgram.record left) (ExecWorklistProgram.record right))
      (ExecWorklistProgram.data terminal false false flag
        (ExecWorklistProgram.record left ++ (ExecWorklistProgram.record right ++ pending))
        saved [] []) := by
  have hb := ExecWorklistProgram.copyAt_eval 3 0 (by decide) (by decide) (by decide)
    (ExecWorklistProgram.data terminal v p flag pending saved
      (ExecWorklistProgram.record left ++ []) (ExecWorklistProgram.record right ++ []))
    right [] rfl rfl
  have ha := ExecWorklistProgram.copyAt_eval 2 0 (by decide) (by decide) (by decide)
    (ExecWorklistProgram.data terminal false false flag
      (ExecWorklistProgram.record right ++ pending) saved (ExecWorklistProgram.record left ++ []) [])
    left [] rfl rfl
  rw [ExecWorklistProgram.copyAfter_right] at hb
  rw [ExecWorklistProgram.copyAfter_left] at ha
  have h := hb.seq ha
  simp only [List.append_nil] at h
  convert h using 1 <;> first | rfl | omega

theorem pushPair_trace (left right saved pending : List Bool) (terminal v p flag : Bool) :
    Trace pushPairProgram (13 * right.length + 13 * left.length + 37)
      ((ExecWorklistProgram.data terminal v p flag pending saved
        (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
          (some pushPairProgram.entry))
      ((ExecWorklistProgram.data terminal false false flag
        (ExecWorklistProgram.record left ++ (ExecWorklistProgram.record right ++ pending))
        saved [] []).withPC none) := by
  simpa only [pushPairProgram, Nat.add_assoc] using compiled_halt_trace
    (pushPair_eval left right saved pending terminal v p flag) 2 0

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite control for the outer disjoint counting traversal.

The leaf command is an explicit piece of finite code chosen with `k`. Its
layout, reconstruction, input loading and output export are still
separate obligations until the concrete leaf implementation is substituted.
There is no oracle instruction or endpoint theorem in this module.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram

open BitProgram StructuredCalls SubexpPostfixControl

theorem splitter_pair_projection (frame : Data) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ) :
    projectState (registers 4 (by decide)) pairStack
      (embedState (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)) =
      ExecWorklistProgram.data false false false false pending header
        (ExecWorklistProgram.record
          (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)))
        (ExecWorklistProgram.record (ExecCoreChildProgram.formulaCode
          (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H))) := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i
    · exact embedState_register (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)
        (registers 15 (by decide)).injective 0
    · exact embedState_register (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)
        (registers 15 (by decide)).injective 1
    · exact embedState_register (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)
        (registers 15 (by decide)).injective 2
    · exact embedState_register (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H)
        (registers 15 (by decide)).injective 3
  · funext i
    fin_cases i
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 0
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 1
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 2
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 3
    · exact embedState_stack (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 7

theorem branch_execution (frame : Data) (regs : Fin 15 → Bool)
    (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2,
      ∃ e, Eval branch t
        (embedState (registers 15 (by decide)) splitterStack frame
          (DisjointBranchProgram.inputState regs pending header F S H)) e ∧
        e.stacks 257 =
          ExecWorklistProgram.record
            (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)) ++
          (ExecWorklistProgram.record (ExecCoreChildProgram.formulaCode
            (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)) ++ pending) ∧
        e.stacks 258 = header ∧ e.stacks 261 = [] ∧ e.stacks 262 = [] ∧
        e.stacks 265 = [] ∧ e.stacks 259 = frame.stacks 259 ∧
        e.stacks 260 = frame.stacks 260 := by
  let left := ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)
  let right := ExecCoreChildProgram.formulaCode
    (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)
  let middle := embedState (registers 15 (by decide)) splitterStack frame
    (DisjointBranchProgram.outputState pending header F S H)
  obtain ⟨t, ht, hs⟩ := DisjointBranchProgram.program_runsIn regs pending header F S H
  have hsplit : Eval splitCurrent t
      (embedState (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.inputState regs pending header F S H)) middle :=
    eval_call_lifted DisjointBranchProgram.program (registers 15 (by decide))
      splitterStack frame (registers 15 (by decide)).injective splitterStack.injective hs
  have hpair := SparseFrontierProgram.pushPair_trace left right header pending
    false false false false
  rw [← splitter_pair_projection frame pending header F S H] at hpair
  have hp := eval_call_from_state SparseFrontierProgram.pushPairProgram
    (registers 4 (by decide)) pairStack middle (registers 4 (by decide)).injective
    pairStack.injective hpair
  refine ⟨t + (13 * right.length + 13 * left.length + 37), ?_, _, hsplit.seq hp,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl := ExecCoreChildProgram.result_length_le F S H
    have hr := DisjointBranchProgram.resultB_length_le F S H
    have hv : 0 < ExecCoreChildProgram.inputVolume F S H := by
      unfold ExecCoreChildProgram.inputVolume
      omega
    have hla : left.length ≤ ExecCoreChildProgram.inputVolume F S H := by
      dsimp [left]
      unfold ExecCoreChildProgram.inputVolume
      omega
    dsimp [right] at hr ⊢
    nlinarith only [ht, hr, hla, hv]
  · exact embedState_stack (registers 4 (by decide)) pairStack middle _ pairStack.injective 0
  · exact embedState_stack (registers 4 (by decide)) pairStack middle _ pairStack.injective 1
  · exact embedState_stack (registers 4 (by decide)) pairStack middle _ pairStack.injective 2
  · exact embedState_stack (registers 4 (by decide)) pairStack middle _ pairStack.injective 3
  · rw [embedState_stack_frame (registers 4 (by decide)) pairStack middle _ 265 (by decide)]
    exact embedState_stack (registers 15 (by decide)) splitterStack frame
      (DisjointBranchProgram.outputState pending header F S H) splitterStack.injective 4
  · rw [embedState_stack_frame (registers 4 (by decide)) pairStack middle _ 259 (by decide)]
    exact embedState_stack_frame (registers 15 (by decide)) splitterStack frame
      (DisjointBranchProgram.outputState pending header F S H) 259 (by decide)
  · rw [embedState_stack_frame (registers 4 (by decide)) pairStack middle _ 260 (by decide)]
    exact embedState_stack_frame (registers 15 (by decide)) splitterStack frame
      (DisjointBranchProgram.outputState pending header F S H) 260 (by decide)



theorem splitter_input_projection (d : Data) (F S : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
    (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hscratch : ∀ i : Fin 23, 7 ≤ i.val → d.stacks (splitterStack i) = []) :
    projectState (registers 15 (by decide)) splitterStack d =
      DisjointBranchProgram.inputState (d.regs ∘ registers 15 (by decide))
        (d.stacks 257) (d.stacks 258) F S H := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  refine Fin.addCases (m := 7) (n := 16) (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    · rfl
    · rfl
    · exact hleft
    · exact hright
    · exact hF
    · exact hH
    · exact hS
  · simpa [ExecBranchControllerSupport.emptyBank] using
      hscratch (Fin.natAdd 7 j) (by simp)

theorem splitter_input_projection_of_clean (d : Data)
    (F S : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
    (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = []) :
    projectState (registers 15 (by decide)) splitterStack d =
      DisjointBranchProgram.inputState (d.regs ∘ registers 15 (by decide))
        (d.stacks 257) (d.stacks 258) F S H := by
  apply splitter_input_projection d F S H hF hH hS hleft hright
  intro i hi
  have hrange : (splitterStack i).val < 24 ∧ splitterStack i ≠ 9 ∧ splitterStack i ≠ 12 := by
    have h : ∀ j : Fin 23, 7 ≤ j.val →
        (splitterStack j).val < 24 ∧ splitterStack j ≠ 9 ∧ splitterStack j ≠ 12 := by decide
    exact h i hi
  exact hclean _ hrange.1 hrange.2.1 hrange.2.2


/- The typed count identity for the concrete disjoint branch. -/



theorem branch_execution_from_state_oai (d : Data) (F S : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 265 = ExecCoreChildProgram.formulaCode F)
    (hH : d.stacks 9 = ExecCoreChildProgram.clauseCode H)
    (hS : d.stacks 12 = ExecCoreChildProgram.formulaCode S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = []) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2,
      ∃ e, Eval branch t d e ∧
        e.stacks 257 =
          ExecWorklistProgram.record
            (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)) ++
          (ExecWorklistProgram.record (ExecCoreChildProgram.formulaCode
            (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)) ++ d.stacks 257) ∧
        e.stacks 258 = d.stacks 258 ∧ e.stacks 261 = [] ∧ e.stacks 262 = [] ∧
        e.stacks 265 = [] ∧ e.stacks 259 = d.stacks 259 ∧
        e.stacks 260 = d.stacks 260 := by
  have hp := splitter_input_projection_of_clean d F S H hF hH hS hleft hright hclean
  have he := branch_execution d (d.regs ∘ registers 15 (by decide))
    (d.stacks 257) (d.stacks 258) F S H
  rw [← hp, embedState_project _ _ d
    (registers 15 (by decide)).injective splitterStack.injective] at he
  exact he


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state_oai
