-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:07:13.021282+00:00
-- url     : https://prove2.me/submissions/bfe142f1-1b27-474b-af90-a719aa924d02

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DisjointBranchProgram_program_runsIn
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_DisjointBranchProgram_resultB_length_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BitProgramSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Data-size bounds for the concrete Boolean-stack machine. A single
instruction can allocate at most one new bit. These bounds concern the actual
configurations on measured traces, not an auxiliary cost annotation. -/

namespace SubexponentialSAT.BitProgram

open scoped BigOperators

theorem stackBits_update {s : ℕ} (stk : Fin s → List Bool) (k : Fin s)
    (word : List Bool) :
    stackBits (Function.update stk k word) + (stk k).length = stackBits stk + word.length := by
  have lengths : (fun i => (Function.update stk k word i).length) =
      Function.update (fun i => (stk i).length) k word.length := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp only [Function.update_of_ne hi]
  unfold stackBits
  rw [lengths, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun i => (stk i).length) (Finset.mem_univ k)
  omega

theorem execInstr_dataBits {r s l : ℕ} (i : Instr r s l) (c : Cfg r s l) :
    dataBits (execInstr i c) ≤ dataBits c + 1 := by
  cases i <;> try simp [dataBits, execInstr]
  · rename_i stack src next
    have h := stackBits_update c.stacks stack (c.regs src :: c.stacks stack)
    simp only [List.length_cons] at h
    change stackBits (Function.update c.stacks stack (c.regs src :: c.stacks stack)) ≤ _
    omega
  · rename_i stack value present next
    have h := stackBits_update c.stacks stack (c.stacks stack).tail
    have htail : (c.stacks stack).tail.length ≤ (c.stacks stack).length := by
      cases c.stacks stack <;> simp
    change stackBits (Function.update c.stacks stack (c.stacks stack).tail) ≤ _
    omega

theorem step_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l}
    (h : step p a = some b) : dataBits b ≤ dataBits a + 1 := by
  cases hp : a.pc with
  | none => simp [step, hp] at h
  | some label =>
      simp [step, hp] at h
      rw [← h]
      exact execInstr_dataBits _ _

theorem trace_dataBits {r s l : ℕ} (p : Program r s l) {a b : Cfg r s l} {n : ℕ}
    (h : Trace p n a b) : dataBits b ≤ dataBits a + n := by
  induction h with
  | refl a => simp
  | cons hs ht ih =>
      have hstep := step_dataBits p hs
      omega

end SubexponentialSAT.BitProgram

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_VisitedTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Passive absolute-coordinate instrumentation for the primitive machine.
The interval on every tape includes its initial input cells and every visited
head coordinate. The instrumentation never changes a primitive transition. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

theorem trace_suffix {α : Type*} {step : α → Option α}
    {c d intermediate : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps c d)
    (hp : Computation.Trace step prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) :
    Computation.Trace step (steps - prefixSteps) intermediate d := by
  apply Computation.Trace.of_iterate
  have h := tr.iterate
  conv_lhs at h => rw [← Nat.sub_add_cancel hle]
  rw [Function.iterate_add_apply, hp.iterate] at h
  exact h

theorem trace_prefix_bound_trans {α : Type*} {step : α → Option α}
    {a b : α} {firstSteps secondSteps : ℕ} {P : α → Prop}
    (first : Computation.Trace step firstSteps a b)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ secondSteps →
      Computation.Trace step prefixSteps b intermediate → P intermediate) :
    ∀ prefixSteps intermediate, prefixSteps ≤ firstSteps + secondSteps →
      Computation.Trace step prefixSteps a intermediate → P intermediate := by
  intro prefixSteps intermediate hle htrace
  by_cases hprefix : prefixSteps ≤ firstSteps
  · exact hfirst prefixSteps intermediate hprefix htrace
  · exact hsecond (prefixSteps - firstSteps) intermediate (by omega)
      (trace_suffix htrace first (by omega))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

private theorem base_entry_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l) :
    StructuredProgram.entry c (label ∘ embed) (label exit) =
      label (StructuredProgram.entry c embed exit) := by
  induction c generalizing l L with
  | skip => rfl
  | atom => rfl
  | seq first second ihf ihs =>
      change StructuredProgram.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem base_code_map {r s l L : ℕ} (c : StructuredProgram.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (site : StructuredProgram.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredProgram.code c embed exit site) =
      StructuredProgram.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | skip => exact site.elim
  | atom op => cases op <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredProgram.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredProgram.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [base_entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredProgram.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (base_entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (base_entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (base_entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

private theorem entry_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l) :
    StructuredCalls.entry c (label ∘ embed) (label exit) =
      label (StructuredCalls.entry c embed exit) := by
  induction c generalizing l L with
  | base c => exact base_entry_map c label embed exit
  | call => rfl
  | seq first second ihf ihs =>
      change StructuredCalls.entry first (label ∘ (embed ∘ Sum.inl))
        (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) = _
      rw [ihs, ihf]
  | ite => rfl
  | «while» => rfl

private theorem code_map {r s l L : ℕ} (c : StructuredCalls.Cmd r s)
    (label : Fin l → Fin L) (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (site : StructuredCalls.Site c) :
    ProgramLinking.relocateInstr id id label none (StructuredCalls.code c embed exit site) =
      StructuredCalls.code c (label ∘ embed) (label exit) site := by
  induction c generalizing l L with
  | base c => exact base_code_map c label embed exit site
  | call p =>
      simp only [StructuredCalls.code]
      cases p.code site <;> rfl
  | seq first second ihf ihs =>
      cases site with
      | inl q =>
          change _ = StructuredCalls.code first (label ∘ (embed ∘ Sum.inl))
            (StructuredCalls.entry second (label ∘ (embed ∘ Sum.inr)) (label exit)) q
          rw [entry_map]
          exact ihf label (embed ∘ Sum.inl)
            (StructuredCalls.entry second (embed ∘ Sum.inr) exit) q
      | inr q => exact ihs label (embed ∘ Sum.inr) exit q
  | ite test yes no ihy ihn =>
      rcases site with _ | (q | q)
      · exact congrArg₂ (Instr.branch test)
          (entry_map yes label (fun x => embed (some (.inl x))) exit).symm
          (entry_map no label (fun x => embed (some (.inr x))) exit).symm
      · exact ihy label (fun x => embed (some (.inl x))) exit q
      · exact ihn label (fun x => embed (some (.inr x))) exit q
  | «while» test body ih =>
      cases site with
      | none =>
          exact congrArg₂ (Instr.branch test)
            (entry_map body label (embed ∘ some) (embed none)).symm rfl
      | some q => exact ih label (embed ∘ some) (embed none) q

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- Port embedding preserves a uniform local stack bound and the caller's
off-port bound separately. It never charges the caller's frame repeatedly. -/
theorem relocate_trace_stack_bound {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace q prefixSteps
        (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hp i
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix p q register stack label
    returnPc frame hregister hstack hcode tr hle hp
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [ProgramLinking.embedCfg_stack register stack label returnPc frame source hstack]
    exact (hsource prefixSteps source hle hs j).trans (Nat.le_max_left _ _)
  · rw [ProgramLinking.embedCfg_stack_frame register stack label returnPc frame source i hi]
    exact (hframe i).trans (Nat.le_max_right _ _)

theorem liftProgram_stack_bound {r s l R S : ℕ}
    (p : Program r s l) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : Cfg R S l)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p register stack) prefixSteps
        (ProgramLinking.embedCfg register stack id none frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound :=
  relocate_trace_stack_bound p _ register stack id none frame hregister hstack
    (fun _ => rfl) tr hsource hframe

/-- A structured call retains its callee's every-prefix stack bound in the
actual caller table. The table premise is the same one used by eval_trace. -/
theorem call_stack_bound {r s l L : ℕ} (routine : Program r s l)
    (caller : Program r s L) (label : Fin l → Fin L) (exit : Fin L)
    (hcode : ∀ pc, caller.code (label pc) =
      StructuredCalls.code (.call routine) label exit pc)
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (tr : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps (a.withPC (some (label routine.entry))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  have hinitial : ProgramLinking.embedCfg id id label (some exit)
      (a.withPC (some (label routine.entry))) (a.withPC (some routine.entry)) =
      a.withPC (some (label routine.entry)) := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC]
  rw [← hinitial] at hp
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix routine caller id id label
    (some exit) (a.withPC (some (label routine.entry)))
    Function.injective_id Function.injective_id hcode tr hle hp
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

private theorem commandLabel_sites {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L) :
    commandLabel c embed exit ∘ StructuredCalls.siteAddress c = embed := by
  funext site
  exact commandLabel_site c embed exit site

private theorem commandLabel_entry {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s) :
    commandLabel c embed exit (StructuredCalls.compiled c inputStack outputStack).entry =
      StructuredCalls.entry c embed exit := by
  change commandLabel c embed exit
    (StructuredCalls.entry c (StructuredCalls.siteAddress c) (StructuredCalls.exitAddress c)) = _
  rw [← entry_map c (commandLabel c embed exit) (StructuredCalls.siteAddress c)
    (StructuredCalls.exitAddress c), commandLabel_sites, commandLabel_exit]

private theorem commandLabel_code {r s L : ℕ} (c : StructuredCalls.Cmd r s)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (inputStack outputStack : Fin s)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site)
    (pc : Fin (StructuredCalls.size c + 1)) (hpc : pc ≠ StructuredCalls.exitAddress c) :
    caller.code (commandLabel c embed exit pc) =
      ProgramLinking.relocateInstr id id (commandLabel c embed exit) none
        ((StructuredCalls.compiled c inputStack outputStack).code pc) := by
  obtain ⟨site, rfl⟩ : ∃ site, pc = StructuredCalls.siteAddress c site := by
    cases heq : (StructuredCalls.labelEquiv c).symm pc with
    | none =>
        have hp := congrArg (StructuredCalls.labelEquiv c) heq
        exact (hpc (by simpa [StructuredCalls.exitAddress] using hp)).elim
    | some site =>
        exact ⟨site, by simpa [StructuredCalls.siteAddress] using
          (congrArg (StructuredCalls.labelEquiv c) heq)⟩
  rw [commandLabel_site, StructuredCalls.compiled_site, code_map,
    commandLabel_sites, commandLabel_exit]
  exact hcode site

/-- A bound proved for one compiled structured block transfers to every
installation of that same block in a finite caller table. No bound on the
caller's total runtime is used. -/
theorem command_stack_bound {r s L : ℕ} {c : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval c steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled c inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled c inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site c → Fin L) (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) = StructuredCalls.code c embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry c embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  let routine := StructuredCalls.compiled c inputStack outputStack
  let label := commandLabel c embed exit
  let frame := a.withPC (some (StructuredCalls.entry c embed exit))
  have full := StructuredCalls.compiled_trace heval inputStack outputStack
  obtain ⟨source, hs⟩ := trace_prefix_exists full hle
  have hactive : source.pc ≠ none := by
    intro hnone
    have halted := ProgramLinking.trace_from_halted routine (trace_suffix full hs hle) hnone
    change some (StructuredCalls.exitAddress c) = none at halted
    cases halted
  have htable : ∀ pc, routine.code pc ≠ .halt →
      caller.code (label pc) = ProgramLinking.relocateInstr id id label none (routine.code pc) := by
    intro pc hnot
    apply commandLabel_code c caller embed exit inputStack outputStack hcode pc
    intro heq
    subst pc
    exact hnot (StructuredCalls.compiled_exit c inputStack outputStack)
  have hrelocated := ProgramLinking.relocate_trace_before_halt routine caller id id
    label none frame Function.injective_id Function.injective_id htable hs hactive
  have hinitial : ProgramLinking.embedCfg id id label none frame
      (a.withPC (some routine.entry)) = frame := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, routine, label, frame,
      StructuredProgram.State.withPC, commandLabel_entry]
  rw [hinitial] at hrelocated
  have heq := trace_same_length_unique hp hrelocated
  rw [heq]
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

/-- Sequential command blocks share one uniform space bound. -/
theorem sequence_stack_bound {r s L : ℕ} {first second : StructuredCalls.Cmd r s}
    {n m bound : ℕ} {a b c : StructuredCalls.State r s}
    (hf : StructuredCalls.Eval first n a b) (hs : StructuredCalls.Eval second m b c)
    (inputStack outputStack : Fin s)
    (hfirst : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (StructuredCalls.compiled first inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled first inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (hsecond : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (StructuredCalls.compiled second inputStack outputStack) prefixSteps
        (b.withPC (some (StructuredCalls.compiled second inputStack outputStack).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound)
    (caller : Program r s L) (embed : StructuredCalls.Site (.seq first second) → Fin L)
    (exit : Fin L)
    (hcode : ∀ site, caller.code (embed site) =
      StructuredCalls.code (.seq first second) embed exit site) :
    ∀ prefixSteps intermediate, prefixSteps ≤ n + m →
      Trace caller prefixSteps
        (a.withPC (some (StructuredCalls.entry (.seq first second) embed exit))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  exact trace_prefix_bound_trans
    (StructuredCalls.eval_trace hf caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hf inputStack outputStack hfirst caller (embed ∘ Sum.inl)
      (StructuredCalls.entry second (embed ∘ Sum.inr) exit) (fun q => hcode (.inl q)))
    (command_stack_bound hs inputStack outputStack hsecond caller (embed ∘ Sum.inr)
      exit (fun q => hcode (.inr q)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
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

theorem pushPair_prefix_space (left right saved pending : List Bool) (terminal v p flag : Bool)
    (t : ℕ) (c : Cfg 4 5 (size pushPair + 1))
    (ht : t ≤ 13 * right.length + 13 * left.length + 37)
    (hc : Trace pushPairProgram t
      ((ExecWorklistProgram.data terminal v p flag pending saved
        (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
          (some pushPairProgram.entry)) c) :
    dataBits c ≤ pending.length + saved.length + 15 * (left.length + right.length) + 41 := by
  have h := trace_dataBits pushPairProgram hc
  have hstart : dataBits ((ExecWorklistProgram.data terminal v p flag pending saved
        (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
          (some pushPairProgram.entry)) =
      pending.length + saved.length + 2 * left.length + 2 * right.length + 4 := by
    simp [dataBits, stackBits, Fin.sum_univ_succ,
      ExecWorklistProgram.record_length, Nat.add_assoc]
    omega
  rw [hstart] at h
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

open BitProgram StructuredCalls

open ExecBranchControllerSupport

/-- A local prefix bound for every stack in the finite splitter, including
the preserved caller words. Global tape spans require the compiler bridge. -/
theorem prefix_dataBits_le (regs : Regs) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ)
    {t : ℕ} {c : Cfg 15 23 (size command + 1)}
    (ht : t ≤ 620000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2)
    (htrace : Trace program t
      ((inputState regs pending header F S H).withPC (some program.entry)) c) :
    dataBits c ≤ pending.length + header.length +
      620001 * (ExecCoreChildProgram.inputVolume F S H) ^ 2 := by
  have h := trace_dataBits program htrace
  have hbits : dataBits
      ((inputState regs pending header F S H).withPC (some program.entry)) =
      pending.length + header.length + (ExecCoreChildProgram.formulaCode F).length +
        (ExecCoreChildProgram.clauseCode H).length +
        (ExecCoreChildProgram.formulaCode S).length := by
    unfold dataBits stackBits
    rw [Fin.sum_univ_add (a := 7) (b := 16)]
    simp [inputState, idle, state, inputFront, emptyBank,
      Fin.sum_univ_succ, Nat.add_assoc]
  rw [hbits] at h
  let V := ExecCoreChildProgram.inputVolume F S H
  have hv : 1 ≤ V := by dsimp [V, ExecCoreChildProgram.inputVolume]; omega
  have hsq : V ≤ V ^ 2 := by nlinarith [Nat.mul_le_mul_left V hv]
  have hsize : (ExecCoreChildProgram.formulaCode F).length +
      (ExecCoreChildProgram.clauseCode H).length +
      (ExecCoreChildProgram.formulaCode S).length ≤ V := by
    dsimp [V, ExecCoreChildProgram.inputVolume]
    omega
  dsimp only [V] at hsq hsize
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSResource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Resource bounds for the actual outer DFS commands.

Cleanup is structurally nonallocating. The bounds below concern the concrete
finite tables and every source prefix, before applying the guarded primitive
compiler. The selector and leaf contracts still require their own executions.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource

open BitProgram StructuredCalls SparseDFSProgram

private theorem stackBits_single_le {S : ℕ} (words : Fin S → List Bool) (i : Fin S) :
    (words i).length ≤ stackBits words :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((words j).length)) (Finset.mem_univ i)

private theorem lifted_call_space {r s l steps localBound frameBound : ℕ}
    (routine : Program r s l) (register : Fin r ↪ Fin 80) (stack : Fin s ↪ Fin 1220)
    (frame : Data) {a b : State r s}
    (htrace : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hlocal : ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) c →
      ∀ i, (c.stacks i).length ≤ localBound)
    (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        prefixSteps ((embedState register stack frame a).withPC
          (some (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ max localBound frameBound := by
  have hsource := StructuredSpace.liftProgram_stack_bound routine register stack
    (frame.withPC none) register.injective stack.injective htrace hlocal hframe
  have he := eval_call_lifted routine register stack frame register.injective stack.injective htrace
  cases he with
  | call p ht =>
      apply StructuredSpace.call_stack_bound (ProgramLinking.liftProgram routine register stack)
        (compiled (.call (ProgramLinking.liftProgram routine register stack)) 256 256)
        (siteAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (exitAddress (.call (ProgramLinking.liftProgram routine register stack)))
        (compiled_site (.call (ProgramLinking.liftProgram routine register stack)) 256 256) ht
      simpa only [ProgramLinking.embedCfg, ProgramLinking.relocatePc, embedState,
        StructuredProgram.State.withPC, id_eq] using hsource

/-- The concrete disjoint splitter and child insertion share one uniform
bound. Both child records, the pending list and every caller stack are counted;
no number of previously visited branches occurs in this bound. -/
theorem branch_execution_space_oai (frame : Data) (regs : Fin 15 → Bool)
    (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ)
    (frameBound : ℕ) (hframe : ∀ i, (frame.stacks i).length ≤ frameBound) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume F S H) ^ 2, ∃ e,
      Eval branch t (embedState (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.inputState regs pending header F S H)) e ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled branch 256 256) prefixSteps
          ((embedState (registers 15 (by decide)) splitterStack frame
            (DisjointBranchProgram.inputState regs pending header F S H)).withPC
              (some (compiled branch 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max frameBound
          (pending.length + header.length + 620001 * (ExecCoreChildProgram.inputVolume F S H) ^ 2) := by
  let V := ExecCoreChildProgram.inputVolume F S H
  let bound := max frameBound (pending.length + header.length + 620001 * V ^ 2)
  let left := ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H)
  let right := ExecCoreChildProgram.formulaCode
    (DisjointBranchProgram.resultB SubexpFrontend.negateCode F S H)
  let middle := embedState (registers 15 (by decide)) splitterStack frame
    (DisjointBranchProgram.outputState pending header F S H)
  have hv : 0 < V := by dsimp [V, ExecCoreChildProgram.inputVolume]; omega
  have hleft : left.length ≤ V := by
    have h := ExecCoreChildProgram.result_length_le F S H
    dsimp [left, V, ExecCoreChildProgram.inputVolume]
    omega
  have hright : right.length ≤ 5 * V := DisjointBranchProgram.resultB_length_le F S H
  obtain ⟨splitTime, htime, hsplitTrace⟩ := DisjointBranchProgram.program_runsIn regs pending header F S H
  have hsplit : Eval splitCurrent splitTime
      (embedState (registers 15 (by decide)) splitterStack frame
        (DisjointBranchProgram.inputState regs pending header F S H)) middle :=
    eval_call_lifted DisjointBranchProgram.program (registers 15 (by decide)) splitterStack
      frame (registers 15 (by decide)).injective splitterStack.injective hsplitTrace
  have hsplitLocal : ∀ t c, t ≤ splitTime →
      Trace DisjointBranchProgram.program t
        ((DisjointBranchProgram.inputState regs pending header F S H).withPC
          (some DisjointBranchProgram.program.entry)) c → ∀ i, (c.stacks i).length ≤ bound := by
    intro t c ht hc i
    have hb := DisjointBranchProgram.prefix_dataBits_le regs pending header F S H (ht.trans htime) hc
    have hi : (c.stacks i).length ≤ dataBits c :=
      stackBits_single_le c.stacks i
    exact (hi.trans hb).trans (Nat.le_max_right _ _)
  have hsplitSpace := lifted_call_space (frameBound := bound) DisjointBranchProgram.program (registers 15 (by decide))
    splitterStack frame hsplitTrace hsplitLocal
    (fun i => (hframe i).trans (Nat.le_max_left frameBound _))
  simp only [max_self] at hsplitSpace
  have hmiddle : ∀ i, (middle.stacks i).length ≤ bound :=
    hsplitSpace splitTime _ le_rfl (compiled_trace hsplit 256 256)
  have hpairTrace := SparseFrontierProgram.pushPair_trace left right header pending
    false false false false
  have hpairLocal : ∀ t c, t ≤ 13 * right.length + 13 * left.length + 37 →
      Trace SparseFrontierProgram.pushPairProgram t
        ((ExecWorklistProgram.data false false false false pending header
          (ExecWorklistProgram.record left) (ExecWorklistProgram.record right)).withPC
            (some SparseFrontierProgram.pushPairProgram.entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro t c ht hc i
    have hb := SparseFrontierProgram.pushPair_prefix_space left right header pending
      false false false false t c ht hc
    have hi : (c.stacks i).length ≤ dataBits c :=
      stackBits_single_le c.stacks i
    have hsmall : pending.length + header.length + 15 * (left.length + right.length) + 41 ≤
        pending.length + header.length + 620001 * V ^ 2 := by nlinarith
    exact ((hi.trans hb).trans hsmall).trans (Nat.le_max_right _ _)
  have hpairSpace := lifted_call_space SparseFrontierProgram.pushPairProgram
    (registers 4 (by decide)) pairStack middle hpairTrace hpairLocal hmiddle
  have hproject := splitter_pair_projection frame pending header F S H
  change projectState (registers 4 (by decide)) pairStack middle =
    ExecWorklistProgram.data false false false false pending header
      (ExecWorklistProgram.record left) (ExecWorklistProgram.record right) at hproject
  rw [← hproject] at hpairTrace hpairSpace
  simp only [embedState_project _ _ _ (registers 4 (by decide)).injective pairStack.injective,
    max_self] at hpairSpace
  have hpair := eval_call_from_state SparseFrontierProgram.pushPairProgram
    (registers 4 (by decide)) pairStack middle (registers 4 (by decide)).injective
    pairStack.injective hpairTrace
  refine ⟨splitTime + (13 * right.length + 13 * left.length + 37), ?_, _, hsplit.seq hpair, ?_⟩
  · change splitTime ≤ 620000 * V ^ 2 at htime
    change splitTime + (13 * right.length + 13 * left.length + 37) ≤ 621000 * V ^ 2
    nlinarith
  · exact StructuredSpace.sequence_stack_bound hsplit hpair 256 256 hsplitSpace hpairSpace
      (compiled branch 256 256) (siteAddress branch) (exitAddress branch) (compiled_site branch 256 256)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space_oai
