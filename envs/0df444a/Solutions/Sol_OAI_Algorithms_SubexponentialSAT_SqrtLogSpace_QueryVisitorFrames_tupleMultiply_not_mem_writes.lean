-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames.tupleMultiply_not_mem_writes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:54:41.957762+00:00
-- url     : https://prove2.me/submissions/04d7120e-43ca-439e-b2ab-719ff5423b75

import Mathlib
import Definitions.Def_OAIQ081S152

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Static register frames for the concrete tuple visitor. The frame follows
from the actual instructions and embeddings, including the ambient overlay.
The retained tuple-controller flags require no save stack. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames

open OAI BitProgram StructuredCalls
open CommandRegisterFrames QueryTupleVisitor

private theorem not_mem_union_iff {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} :
    i ∉ left ∪ right ↔ i ∉ left ∧ i ∉ right := by
  simp only [Finset.mem_union, not_or]

private theorem not_mem_empty {R : Type} [DecidableEq R] (i : R) :
    i ∉ (∅ : Finset R) := by
  simp

private theorem high_ne (i : Fin 40) (hi : 16 ≤ i.val)
    (j : Fin 40) (hj : j.val < 16) : i ≠ j := by
  intro h
  subst i
  omega

private theorem outside16 (i : Fin 40) (hi : 16 ≤ i.val) :
    ¬ ∃ j : Fin 16, j.castAdd 24 = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  simp only [Fin.val_castAdd] at hv
  omega

theorem clearMany_not_mem_writes (ports : List (Fin 896))
    (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (NodeReadoutSpace.clearMany ports) := by
  induction ports with
  | nil => exact not_mem_empty i
  | cons p ps ih =>
      exact not_mem_union_iff.mpr ⟨not_mem_clearProgram p 0 1 i
        (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide)), ih⟩

theorem clearPair_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes QueryAssembler.clearPair :=
  not_mem_liftCommand _ _ _ _ _ i (outside16 i hi)

theorem bootstrap_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes FactorEnvironment.bootstrap :=
  not_mem_liftProgram _ _ _ i (outside16 i hi)

theorem prepareMultiply_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes QueryAssembler.TupleMultiply.prepare :=
  not_mem_union_iff.mpr ⟨clearMany_not_mem_writes [61,70] i hi,
    not_mem_union_iff.mpr ⟨clearPair_not_mem_writes i hi,
      bootstrap_not_mem_writes i hi⟩⟩

/-- The original multiplication runs inside its actual low-register map. -/
theorem tupleMultiply_not_mem_writes_oai (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes QueryAssembler.TupleMultiply.command := by
  have hm : i ∉ writes QueryAssembler.TupleMultiply.multiply := by
    apply not_mem_liftCommand_of
    intro j hj
    change j = i at hj
    subst j
    exact FactorArithmeticFrames.accumulate_not_mem_writes i hi
  exact not_mem_union_iff.mpr ⟨prepareMultiply_not_mem_writes i hi,
    not_mem_union_iff.mpr ⟨hm, clearPair_not_mem_writes i hi⟩⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames.tupleMultiply_not_mem_writes_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames.tupleMultiply_not_mem_writes_oai
