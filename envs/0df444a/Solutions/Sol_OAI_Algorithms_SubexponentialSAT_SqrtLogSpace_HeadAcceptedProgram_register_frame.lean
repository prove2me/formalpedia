-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.register_frame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:41:41.155963+00:00
-- url     : https://prove2.me/submissions/08abbbf5-2977-4586-92ae-c0a4a97a4b08

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLogic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured verification rules for fixed bit programs

Every execution judgment below contains actual transitions of one fixed step
function. Loop iterations may be controlled by unbounded data; neither the
transition function nor its finite control changes with the iteration count.
No judgment assigns a cost to an unimplemented mathematical function.
-/

namespace SubexponentialSAT.ProgramLogic

open SubexponentialSAT.Computation
open scoped BigOperators

section Traces

variable {Cfg : Type} {step : Cfg → Option Cfg}

/-- A frame observation preserved by each actual step is preserved by the run. -/
theorem frame_trace {Frame : Type} (frame : Cfg → Frame)
    (preserve : ∀ a b, step a = some b → frame b = frame a)
    {steps : ℕ} {a b : Cfg} (h : Trace step steps a b) : frame b = frame a := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans (preserve _ _ hs)

end Traces

section BitPrograms

open SubexponentialSAT.BitProgram

variable {r s l : ℕ}

theorem execInstr_register_frame (instr : Instr r s l) (c : Cfg r s l) (k : Fin r)
    (hk : k ∉ registerWrites instr) : (execInstr instr c).regs k = c.regs k := by
  cases instr <;> simp_all [registerWrites, execInstr, readRegs]

theorem step_register_frame (p : Program r s l) {a b : Cfg r s l} (k : Fin r)
    (safe : ∀ label, a.pc = some label → k ∉ registerWrites (p.code label))
    (hs : step p a = some b) : b.regs k = a.regs k := by
  cases hp : a.pc with
  | none => simp [step, hp] at hs
  | some label =>
      have heq : execInstr (p.code label) a = b := by simpa [step, hp] using hs
      subst b
      exact execInstr_register_frame _ _ _ (safe label hp)

end BitPrograms

end SubexponentialSAT.ProgramLogic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandRegisterFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Register frames derived from the actual finite instruction tables and
structured command syntax. These footprints describe code, not an assumed
semantic behavior of a callback. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

open OAI BitProgram ProgramLogic

theorem trace_register_frame {r s l : ℕ} (p : Program r s l)
    {steps : ℕ} {a b : Cfg r s l} (ht : Trace p steps a b)
    (i : Fin r) (hi : i ∉ programWrites p) : b.regs i = a.regs i := by
  apply ProgramLogic.frame_trace (fun c : Cfg r s l => c.regs i) ?_ ht
  intro a b hs
  exact step_register_frame p i (fun label _ => (not_mem_programWrites p i).mp hi label) hs

/-- Relocation changes every destination by precisely the declared register map. -/
theorem relocate_writes {r s l R S L : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (instr : Instr r s l) :
    registerWrites (ProgramLinking.relocateInstr register stack label returnPc instr) =
      (registerWrites instr).image register := by
  cases instr <;> cases returnPc <;> simp [ProgramLinking.relocateInstr, registerWrites]

theorem not_mem_liftProgram {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (i : Fin R)
    (hi : ¬ ∃ j, register j = i) :
    i ∉ programWrites (ProgramLinking.liftProgram p register stack) := by
  rw [not_mem_programWrites]
  intro label
  simp only [relocate_writes, Finset.mem_image, not_exists]
  intro j hj
  exact hi ⟨j, hj.2⟩


theorem base_code_writes {r s : ℕ} (c : StructuredProgram.Cmd r s)
    {l : ℕ} (embed : StructuredProgram.Site c → Fin l) (exit : Fin l)
    (q : StructuredProgram.Site c) :
    registerWrites (StructuredProgram.code c embed exit q) ⊆ baseWrites c := by
  induction c generalizing l with
  | skip => exact q.elim
  | atom atom => cases atom <;> simp [StructuredProgram.code, StructuredProgram.Atom.instr,
      registerWrites, baseWrites]
  | seq first second ihf ihs =>
      cases q with
      | inl q => exact (ihf _ _ q).trans Finset.subset_union_left
      | inr q => exact (ihs _ _ q).trans Finset.subset_union_right
  | ite test yes no ihy ihn =>
      cases q with
      | none => simp [registerWrites]
      | some q =>
          cases q with
          | inl q => exact (ihy _ _ q).trans Finset.subset_union_left
          | inr q => exact (ihn _ _ q).trans Finset.subset_union_right
  | «while» test body ih =>
      cases q with
      | none => simp [registerWrites]
      | some q => exact ih _ _ q

theorem code_writes {r s : ℕ} (c : StructuredCalls.Cmd r s)
    {l : ℕ} (embed : StructuredCalls.Site c → Fin l) (exit : Fin l)
    (q : StructuredCalls.Site c) :
    registerWrites (StructuredCalls.code c embed exit q) ⊆ writes c := by
  induction c generalizing l with
  | base c => exact base_code_writes c embed exit q
  | call p =>
      simp only [StructuredCalls.code, relocate_writes, Finset.image_id, writes]
      intro i hi
      exact (mem_programWrites p i).mpr ⟨q, hi⟩
  | seq first second ihf ihs =>
      cases q with
      | inl q => exact (ihf _ _ q).trans Finset.subset_union_left
      | inr q => exact (ihs _ _ q).trans Finset.subset_union_right
  | ite test yes no ihy ihn =>
      cases q with
      | none => simp [registerWrites]
      | some q =>
          cases q with
          | inl q => exact (ihy _ _ q).trans Finset.subset_union_left
          | inr q => exact (ihn _ _ q).trans Finset.subset_union_right
  | «while» test body ih =>
      cases q with
      | none => simp [registerWrites]
      | some q => exact ih _ _ q

/-- Compiling guards, sequencing and return jumps introduces no register writes. -/
theorem compiled_writes {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) :
    programWrites (StructuredCalls.compiled c input output) ⊆ writes c := by
  intro i hi
  obtain ⟨label, hl⟩ := (mem_programWrites _ i).mp hi
  obtain ⟨q, rfl⟩ := (StructuredCalls.labelEquiv c).surjective label
  cases q with
  | none =>
      change i ∈ registerWrites ((StructuredCalls.compiled c input output).code
        (StructuredCalls.exitAddress c)) at hl
      rw [StructuredCalls.compiled_exit] at hl
      simp [registerWrites] at hl
  | some q =>
      change i ∈ registerWrites ((StructuredCalls.compiled c input output).code
        (StructuredCalls.siteAddress c q)) at hl
      rw [StructuredCalls.compiled_site] at hl
      apply code_writes c _ _ q
      exact hl

theorem not_mem_compiled {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (i : Fin r) (hi : i ∉ writes c) :
    i ∉ programWrites (StructuredCalls.compiled c input output) :=
  fun hm => hi (compiled_writes c input output hm)

theorem compiled_trace_register_frame {r s : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) {steps : ℕ}
    {a b : Cfg r s (StructuredCalls.size c + 1)}
    (ht : Trace (StructuredCalls.compiled c input output) steps a b)
    (i : Fin r) (hi : i ∉ writes c) : b.regs i = a.regs i :=
  trace_register_frame _ ht i (not_mem_compiled c input output i hi)

theorem not_mem_liftCommand {r s R S : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (i : Fin R) (hi : ¬ ∃ j, register j = i) :
    i ∉ writes (StructuredCalls.liftCommand c input output register stack) :=
  not_mem_liftProgram _ register stack i hi

/-- These primitive loops can only write their explicit value/presence registers. -/
theorem not_mem_clearProgram {r s : ℕ} (src : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.clearProgram src value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

theorem not_mem_copyProgram {r s : ℕ} (src dst tmp : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.copyProgram src dst tmp value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]



theorem liftProgram_writes {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) :
    programWrites (ProgramLinking.liftProgram p register stack) =
      (programWrites p).image register := by
  ext i
  simp only [mem_programWrites, ProgramLinking.liftProgram, relocate_writes,
    Finset.mem_image]
  constructor
  · rintro ⟨label, j, hj, hji⟩
    exact ⟨j, ⟨label, hj⟩, hji⟩
  · rintro ⟨j, ⟨label, hj⟩, hji⟩
    exact ⟨label, j, hj, hji⟩

theorem not_mem_liftCommand_of {r s R S : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (i : Fin R) (hi : ∀ j, register j = i → j ∉ writes c) :
    i ∉ writes (StructuredCalls.liftCommand c input output register stack) := by
  change i ∉ programWrites (ProgramLinking.liftProgram _ register stack)
  rw [liftProgram_writes]
  rintro hm
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hm
  exact hi j hji (compiled_writes c input output hj)

theorem not_mem_reverseProgram {r s : ℕ} (src tmp₁ tmp₂ : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.reverseProgram src tmp₁ tmp₂ value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

theorem not_mem_record_reader {r s : ℕ} (p : RecordPrograms.Ports r s) (i : Fin r)
    (ht : i ≠ p.tag) (hp : i ≠ p.present) :
    i ∉ writes (RecordPrograms.reader p) := by
  apply not_mem_liftProgram
  rintro ⟨j, hj⟩
  unfold RecordPrograms.registerMap at hj
  split_ifs at hj
  · exact ht hj.symm
  · exact hp hj.symm

theorem not_mem_record_iterate {r s : ℕ} (p : RecordPrograms.Ports r s)
    (callback : StructuredCalls.Cmd r s) (i : Fin r)
    (hc : i ∉ writes callback)
    (ht : i ≠ p.tag) (hp : i ≠ p.present) (hf : i ≠ p.found) :
    i ∉ writes (RecordPrograms.iterate p callback) := by
  have hr := not_mem_record_reader p i ht hp
  simp only [writes, baseWrites, StructuredProgram.Atom.instr, registerWrites,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hf, ⟨⟨ht, hp⟩, ⟨hr, ⟨hc, ⟨ht, ⟨ht, hp⟩⟩⟩⟩⟩⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorArithmeticFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Register footprints of the original concrete factor arithmetic commands. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorArithmeticFrames
open OAI BitProgram StructuredCalls SqrtLog.LeafProgram
open CommandRegisterFrames

private theorem not_mem_union {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} (hl : i ∉ left) (hr : i ∉ right) :
    i ∉ left ∪ right := by
  simpa only [Finset.mem_union, not_or] using And.intro hl hr

private theorem high_ne (i : Fin 40) (hi : 16 ≤ i.val) (j : Fin 40) (hj : j.val < 16) : i ≠ j := by
  intro he
  subst i
  omega

private theorem outside8 (i : Fin 40) (hi : 16 ≤ i.val) :
    ¬ ∃ j : Fin 8, j.castAdd 32 = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [Fin.val_castAdd] at hv
  omega

theorem clear_not_mem_writes (src : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (Factor.clear src) :=
  not_mem_clearProgram src 0 1 i (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))

theorem move_not_mem_writes (src dst : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (Factor.move src dst) := by
  change i ∉ programWrites (StackRoutines.copyProgram src dst 159 0 1) ∪ writes (Factor.clear src)
  exact not_mem_union (not_mem_copyProgram src dst 159 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide)))
    (clear_not_mem_writes src i hi)

theorem accumulate_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes Factor.accumulate := by
  have hm : i ∉ writes Factor.multiply :=
    not_mem_liftProgram _ _ _ i (outside8 i hi)
  simp only [Factor.accumulate, writes]
  exact not_mem_union (move_not_mem_writes _ _ i hi)
    (not_mem_union (move_not_mem_writes _ _ i hi)
      (not_mem_union hm (move_not_mem_writes _ _ i hi)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorArithmeticFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorCommandFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual accepted-assignment implementation writes only the lower sixteen
Boolean registers. This is a static fact about every concrete called table,
including the original factor dispatcher, parser and native arithmetic. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorCommandFrames

open OAI BitProgram StructuredCalls SqrtLog.LeafProgram
open CommandRegisterFrames

private theorem not_mem_union_iff {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} :
    i ∉ left ∪ right ↔ i ∉ left ∧ i ∉ right := by
  simp only [Finset.mem_union, not_or]

private theorem not_mem_empty {R : Type} [DecidableEq R] (i : R) :
    i ∉ (∅ : Finset R) := by
  simp

private theorem high_ne (i : Fin 40) (hi : 16 ≤ i.val) (j : Fin 40) (hj : j.val < 16) : i ≠ j := by
  intro he
  subst i
  omega

private theorem outside8 (i : Fin 40) (hi : 16 ≤ i.val) :
    ¬ ∃ j : Fin 8, j.castAdd 32 = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [Fin.val_castAdd] at hv
  omega

private theorem outside16 (i : Fin 40) (hi : 16 ≤ i.val) :
    ¬ ∃ j : Fin 16, j.castAdd 24 = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [Fin.val_castAdd] at hv
  omega

private theorem liftLow_safe (c : Cmd 40 768) (input output : Fin 768)
    (i : Fin 40) (hc : i ∉ writes c) :
    i ∉ writes (FactorAssignmentProgram.liftLow c input output) := by
  apply not_mem_liftCommand_of
  intro j hj
  change j = i at hj
  subst j
  exact hc

private theorem hashArithmetic_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorEvaluationSpace.hashArithmetic := by
  have hp : i ∉ programWrites (ProgramLinking.liftProgram
      Indicator.program Factor.nativeRegisters Factor.indicatorStacks) :=
    not_mem_liftProgram _ _ _ i (outside8 i hi)
  have h0 := high_ne i hi 0 (by decide)
  have h1 := high_ne i hi 1 (by decide)
  have h2 := high_ne i hi 2 (by decide)
  have hready : i ∉ writes Factor.indicatorReady := by
    unfold Factor.indicatorReady
    refine not_mem_union_iff.mpr ⟨?_, not_mem_union_iff.mpr ⟨?_, ?_⟩⟩
    · simpa [writes, baseWrites, StructuredProgram.Atom.instr,
        ProgramLogic.registerWrites] using h0
    · simpa [writes, baseWrites, StructuredProgram.Atom.instr,
        ProgramLogic.registerWrites] using h1
    · simpa [writes, baseWrites, StructuredProgram.Atom.instr,
        ProgramLogic.registerWrites] using h2
  have hind : i ∉ writes Factor.indicator := by
    unfold Factor.indicator
    exact not_mem_union_iff.mpr ⟨hready, hp⟩
  unfold FactorEvaluationSpace.hashArithmetic
  exact not_mem_union_iff.mpr ⟨hind, not_mem_union_iff.mpr
    ⟨FactorArithmeticFrames.clear_not_mem_writes _ i hi, not_mem_union_iff.mpr
      ⟨FactorArithmeticFrames.clear_not_mem_writes _ i hi,
        FactorArithmeticFrames.accumulate_not_mem_writes i hi⟩⟩⟩

private theorem markedArithmetic_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorEvaluationSpace.markedArithmetic := by
  have hc : i ∉ writes Clause.caller := not_mem_liftProgram _ _ _ i (outside8 i hi)
  unfold FactorEvaluationSpace.markedArithmetic
  exact not_mem_union_iff.mpr ⟨hc, not_mem_union_iff.mpr
    ⟨FactorArithmeticFrames.clear_not_mem_writes _ i hi,
      FactorArithmeticFrames.accumulate_not_mem_writes i hi⟩⟩

private theorem expansion_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes Expansion.forwardCommand := by
  have hc : i ∉ writes Expansion.command := not_mem_liftProgram _ _ _ i (outside8 i hi)
  have hr : i ∉ writes Expansion.reverseInput := not_mem_reverseProgram 154 358 359 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))
  exact not_mem_union_iff.mpr ⟨hr, hc⟩

private theorem factorID_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorID.command := by
  have h0 := high_ne i hi 0 (by decide)
  have h1 := high_ne i hi 1 (by decide)
  have hc := not_mem_copyProgram (149 : Fin 768) 556 359 0 1 i h0 h1
  unfold FactorID.command
  refine not_mem_union_iff.mpr ⟨hc, ?_⟩
  simpa [writes, baseWrites, StructuredProgram.Atom.instr,
    ProgramLogic.registerWrites] using And.intro h0 h1

private theorem dispatch_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorDispatch.command := by
  have h0 := high_ne i hi 0 (by decide)
  have h1 := high_ne i hi 1 (by decide)
  have h7 := high_ne i hi 7 (by decide)
  have hc := not_mem_copyProgram (149 : Fin 768) 152 359 0 1 i h0 h1
  have hd : i ∉ writes FactorDispatch.dispatch := not_mem_liftProgram _ _ _ i (outside8 i hi)
  unfold FactorDispatch.command
  refine not_mem_union_iff.mpr ⟨not_mem_union_iff.mpr ⟨hc, ?_⟩, hd⟩
  simpa [writes, baseWrites, StructuredProgram.Atom.instr,
    ProgramLogic.registerWrites] using And.intro h7 h0

private theorem prepareIncidence_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorAssignmentProgram.prepareIncidence := by
  have hc : i ∉ writes FactorTableProgram.caller :=
    not_mem_liftProgram _ _ _ i (outside16 i hi)
  exact not_mem_union_iff.mpr ⟨liftLow_safe _ _ _ i (factorID_safe i hi), hc⟩

private theorem choose_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorAssignmentProgram.choose := by
  have hh : i ∉ writes FactorAssignmentProgram.hashFactor := by
    exact not_mem_union_iff.mpr ⟨prepareIncidence_safe i hi,
      liftLow_safe _ _ _ i (not_mem_union_iff.mpr
        ⟨expansion_safe i hi, hashArithmetic_safe i hi⟩)⟩
  have hm : i ∉ writes FactorAssignmentProgram.markedFactor := by
    exact not_mem_union_iff.mpr ⟨prepareIncidence_safe i hi,
      liftLow_safe _ _ _ i (not_mem_union_iff.mpr
        ⟨FactorArithmeticFrames.move_not_mem_writes _ _ i hi, markedArithmetic_safe i hi⟩)⟩
  simp only [FactorAssignmentProgram.choose, writes, baseWrites, not_mem_union_iff,
    not_mem_empty]
  exact ⟨hh, hm, by simp⟩

private theorem assignment_clear (src : Fin 896) (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (FactorAssignmentProgram.clear src) :=
  not_mem_clearProgram src 0 1 i (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))

private theorem assignment_copy (src dst : Fin 896) (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (FactorAssignmentProgram.copy src dst) :=
  not_mem_copyProgram src dst 159 0 1 i (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))

private theorem callback_safe (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorAssignmentProgram.callback := by
  have hclear : i ∉ writes FactorAssignmentProgram.clearCallback :=
    not_mem_liftCommand _ _ _ _ _ i (outside16 i hi)
  have hreturn : i ∉ writes FactorAssignmentProgram.returnToRecords := by
    simp [FactorAssignmentProgram.returnToRecords, writes, baseWrites,
      StructuredProgram.Atom.instr, ProgramLogic.registerWrites,
      high_ne i hi 13 (by decide), high_ne i hi 14 (by decide), high_ne i hi 15 (by decide)]
  simp only [FactorAssignmentProgram.callback, writes, not_mem_union_iff]
  exact ⟨hclear, liftLow_safe _ _ _ i (dispatch_safe i hi), choose_safe i hi,
    assignment_clear _ i hi, hreturn⟩

/-- This fact inspects the actual accepted-assignment syntax and actual called
program maps. There is no semantic frame hypothesis for a callback. -/
theorem assignment_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorAssignmentProgram.assignment := by
  have hinit : i ∉ writes FactorAssignmentProgram.initialize_ :=
    not_mem_liftCommand _ _ _ _ _ i (outside16 i hi)
  have hsetup : i ∉ writes FactorAssignmentProgram.setup :=
    not_mem_liftCommand _ _ _ _ _ i (outside16 i hi)
  have hloop : i ∉ writes FactorAssignmentProgram.loop :=
    not_mem_record_iterate FactorAssignmentProgram.ports _ i (callback_safe i hi)
      (high_ne i hi 13 (by decide)) (high_ne i hi 14 (by decide)) (high_ne i hi 15 (by decide))
  simp only [FactorAssignmentProgram.assignment, FactorAssignmentProgram.product,
    FactorAssignmentProgram.move, writes, not_mem_union_iff]
  exact ⟨hinit, hsetup, assignment_copy _ _ i hi, assignment_copy _ _ i hi,
    hloop, assignment_copy _ _ i hi, assignment_clear _ i hi⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorCommandFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head-sum assembly. The first head gate receives a physically
cleared arithmetic bank; persistent source parameters remain outside that bank.
Accepted assignments continue through dense addition and workspace reclamation,
including empty factor products and zero-valued products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

open OAI BitProgram StructuredCalls StackRoutines
open HeadEvaluationProgram.StagedGate

open CommandRegisterFrames

private theorem outside_castAdd {r k : ℕ} (i : Fin (r + k)) (hi : r ≤ i.val) :
    ¬ ∃ j : Fin r, j.castAdd k = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  have := j.isLt
  simp only [Fin.val_castAdd] at hv
  omega

private theorem not_mem_union {α : Type*} [DecidableEq α] {a : α} {s t : Finset α}
    (hs : a ∉ s) (ht : a ∉ t) : a ∉ s ∪ t := by
  simpa only [Finset.mem_union, not_or] using And.intro hs ht

private theorem bank_clear_writes (tmp : Fin 896) (ports : List (Fin 896)) (i : Fin 40)
    (h0 : i ≠ 0) (h1 : i ≠ 1) :
    i ∉ writes (BankRoutines.clearCmd tmp 0 1 ports) := by
  induction ports with
  | nil => exact not_mem_clearProgram _ _ _ _ h0 h1
  | cons p ps ih =>
      exact not_mem_union (not_mem_clearProgram _ _ _ _ h0 h1) ih

/-- The head controller writes only its explicit low registers. This static
fact applies to every prefix and composes with the concrete factor footprint. -/
theorem head_not_mem_writes (accepted : Code) (i : Fin 40) (hi : 16 ≤ i.val)
    (haccepted : i ∉ writes accepted) : i ∉ writes (head accepted) := by
  have h0 : i ≠ 0 := by intro h; subst i; omega
  have h1 : i ≠ 1 := by intro h; subst i; omega
  have h2 : i ≠ 2 := by intro h; subst i; omega
  have hcopy (src dst : Fin 896) : i ∉ writes (copy src dst) :=
    not_mem_copyProgram _ _ _ _ _ _ h0 h1
  have hclear (src : Fin 896) : i ∉ writes (clear src) :=
    not_mem_clearProgram _ _ _ _ h0 h1
  have hpower : i ∉ writes HeadSumProgram.power :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 3) (k := 37) i (by omega))
  have hseed : i ∉ writes HeadSumProgram.seed := by
    exact not_mem_union (hcopy _ _)
      (not_mem_union (hcopy _ _) (not_mem_union hpower (hclear _)))
  have hstage : i ∉ writes HeadEvaluationProgram.StagedGate.stage := by
    simp only [HeadEvaluationProgram.StagedGate.stage, writes]
    exact not_mem_union (hcopy _ _) (not_mem_union (hcopy _ _)
      (not_mem_union (hcopy _ _) (not_mem_union (hcopy _ _)
        (not_mem_union (hcopy _ _) (hcopy _ _)))))
  have hcleanup : i ∉ writes HeadEvaluationProgram.StagedGate.cleanup := by
    simp only [HeadEvaluationProgram.StagedGate.cleanup, writes]
    exact not_mem_union (hclear _) (not_mem_union (hclear _)
      (not_mem_union (hclear _) (not_mem_union (hclear _)
        (not_mem_union (hclear _) (hclear _)))))
  have hcall : i ∉ writes HeadEvaluationProgram.StagedGate.callGate :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 16) (k := 24) i hi)
  have hgate : i ∉ writes HeadEvaluationProgram.StagedGate.command :=
    not_mem_union hstage (not_mem_union hcall hcleanup)
  have hinc : i ∉ writes (Counters.incrementCmd HeadSumProgram.cursorPorts) :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 3) (k := 37) i (by omega))
  have hbody : i ∉ writes (HeadSumProgram.body accepted) := by
    change i ∉ writes HeadEvaluationProgram.StagedGate.command ∪
      ((writes accepted ∪ ∅) ∪ writes (Counters.incrementCmd HeadSumProgram.cursorPorts))
    simp only [Finset.union_empty]
    exact not_mem_union hgate (not_mem_union haccepted hinc)
  have hzero : i ∉ writes (CounterForPrograms.zeroCmd HeadSumProgram.fuelPorts) :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 3) (k := 37) i (by omega))
  have hdec : i ∉ writes (CounterForPrograms.decrementCmd HeadSumProgram.fuelPorts) :=
    not_mem_liftProgram _ _ _ i (outside_castAdd (r := 3) (k := 37) i (by omega))
  have htest : i ∉ writes (CounterForPrograms.testCmd HeadSumProgram.fuelPorts) := by
    change i ∉ writes (CounterForPrograms.zeroCmd HeadSumProgram.fuelPorts) ∪ {2}
    exact not_mem_union hzero (by simpa only [Finset.mem_singleton] using h2)
  have hloop : i ∉ writes (HeadSumProgram.command accepted) :=
    not_mem_union htest (not_mem_union hbody (not_mem_union hdec htest))
  have hfinal : i ∉ writes HeadSumProgram.finalize :=
    not_mem_liftCommand _ _ _ _ _ i (outside_castAdd (r := 16) (k := 24) i hi)
  have hscan : i ∉ writes (HeadSumProgram.scan accepted) :=
    not_mem_union hseed (not_mem_union hloop hfinal)
  exact not_mem_union (not_mem_union (hclear _) (bank_clear_writes 31 workPorts i h0 h1))
    (not_mem_compiled _ _ _ i hscan)

theorem head_register_frame (accepted : Code) (i : Fin 40) (hi : 16 ≤ i.val)
    (haccepted : i ∉ writes accepted) {steps : ℕ}
    {a b : Cfg 40 896 (StructuredCalls.size (head accepted) + 1)}
    (ht : Trace (headProgram accepted) steps a b) : b.regs i = a.regs i :=
  compiled_trace_register_frame _ _ _ ht i (head_not_mem_writes accepted i hi haccepted)

/-- Immediate dense addition and paid cache reset leave caller flags outside
the actual eight- and sixteen-register arithmetic embeddings untouched. -/
theorem accumulate_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes HeadSumProgram.accumulate :=
  not_mem_union
    (not_mem_liftProgram _ _ _ i (outside_castAdd (r := 8) (k := 32) i (by omega)))
    (not_mem_liftProgram _ _ _ i (outside_castAdd (r := 16) (k := 24) i hi))

theorem overlay_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes HighQueryAdapter.NativeOverlay.prepare := by
  have h0 : i ≠ 0 := by intro h; subst i; omega
  have h1 : i ≠ 1 := by intro h; subst i; omega
  exact not_mem_union
    (not_mem_union (not_mem_clearProgram _ _ _ _ h0 h1)
      (bank_clear_writes _ _ _ h0 h1))
    (not_mem_liftProgram _ _ _ i (outside_castAdd (r := 8) (k := 32) i (by omega)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadAcceptedFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram
open OAI BitProgram StructuredCalls CommandRegisterFrames

private theorem not_mem_union_iff {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} :
    i ∉ left ∪ right ↔ i ∉ left ∧ i ∉ right := by
  simp only [Finset.mem_union, not_or]

/-- The actual accepted path preserves every outer Boolean control register. -/
theorem accepted_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes HeadSumAssembly.accepted :=
  not_mem_union_iff.mpr ⟨HeadSumAssembly.overlay_not_mem_writes i hi,
    not_mem_union_iff.mpr ⟨FactorCommandFrames.assignment_not_mem_writes i hi,
      HeadSumAssembly.accumulate_not_mem_writes i hi⟩⟩

/-- The same static frame holds through every source prefix of the fixed full
head rescan, so tuple controller flags36–39 need no assumed restoration. -/
theorem register_frame_oai {steps : ℕ}
    {a b : Cfg 40 896 (size (HeadSumAssembly.head HeadSumAssembly.accepted) + 1)}
    (ht : Trace program steps a b) (i : Fin 40) (hi : 16 ≤ i.val) :
    b.regs i = a.regs i :=
  HeadSumAssembly.head_register_frame _ i hi (accepted_not_mem_writes i hi) ht

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.register_frame_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.register_frame_oai
