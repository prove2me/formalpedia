-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:24:54.101498+00:00
-- url     : https://prove2.me/submissions/29fcaa6b-d354-4025-93ad-ae603358a891

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QuerySelectorFrames_five_word_command_avoids

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reclamation after one marked or accepted query. The port list is part
of the fixed program syntax. Only the collector, immutable formula/row inputs,
and the outer caller's high ports survive. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

theorem cleanupPorts_eq :
    cleanupPorts =
      (List.finRange 768).filter (fun i => !decide (Protected i) && decide (i ≠ 699)) :=
  cleanupPortsWrapped.2

@[simp] theorem mem_cleanupPorts (i : Fin 768) :
    i∈cleanupPorts ↔ ¬Protected i ∧ i≠699 := by
  rw [cleanupPorts_eq]
  simp

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedReturn
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete return from a completed marked high-assignment count. All fresh
query workspace is reclaimed, the complete count is moved to323, and the
collector parser registers are reset after cleanup. The compact boundary cap
is distinct from the transient query cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn

open BitProgram StructuredCalls RecordPrograms SqrtLog
open HashMarkedQueryAdapter
open HashGreedyProgram.NativeRound

theorem upperPorts_eq :
    upperPorts =
      (List.finRange 896).filter (fun i => decide (832 ≤ i.val ∧ i.val < 895)) :=
  upperPortsWrapped.2

@[simp] theorem mem_upperPorts (i : Fin 896) :
    i ∈ upperPorts ↔ 832 ≤ i.val ∧ i.val < 895 := by
  rw [upperPorts_eq]
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExportsTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem fields_good : ∀ f∈fields, f.Good := by
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  fin_cases i <;> simp [Field.Good,field,localSource,destination]

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem clearPorts_mem (j : Fin 768) : j∈clearPorts ↔ 386 ≤ j.val ∧ j.val < 404 := by
  simp only [clearPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,rfl⟩; dsimp [bank]; have := i.isLt; omega
  · intro hj
    refine ⟨⟨j.val-386,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [bank]
    omega

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayFootprint
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compositional certificates for the tape footprint of compiled finite programs. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s l R S L : ℕ}

theorem avoids_transferProgram (H : Fin s → Prop) (src dst : Fin s) (value present : Fin r)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsProgram H (StackRoutines.transferProgram src dst value present) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs,hd]

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayMacros
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Footprints of the fixed storage and scan controllers used by the leaf. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s : ℕ}

theorem avoids_liftCommand_of_range {R S : ℕ} (H : Fin S → Prop)
    (c : Cmd r s) (input output : Fin s) (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (h : ∀ i, ¬ H (stack i)) :
    AvoidsCmd H (liftCommand c input output register stack) :=
  avoids_call_lift_of_range H _ register stack h

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramOuterCarriedMono
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s l : ℕ} {H K : Fin s → Prop}

theorem avoidsInstr_mono (sub : ∀ i, H i → K i) {c : Instr r s l}
    (h : AvoidsInstr K c) : AvoidsInstr H c := by
  cases c <;> simp only [AvoidsInstr] at * <;>
    first | trivial | exact fun hi => h (sub _ hi)

theorem avoidsProgram_mono (sub : ∀ i, H i → K i) {p : Program r s l}
    (h : AvoidsProgram K p) : AvoidsProgram H p :=
  fun q => avoidsInstr_mono sub (h q)

theorem avoidsAtom_mono (sub : ∀ i, H i → K i) {c : StructuredProgram.Atom r s}
    (h : AvoidsAtom K c) : AvoidsAtom H c := by
  cases c <;> simp only [AvoidsAtom] at * <;>
    first | trivial | exact fun hi => h (sub _ hi)

theorem avoidsBase_mono (sub : ∀ i, H i → K i) {c : StructuredProgram.Cmd r s}
    (h : AvoidsBase K c) : AvoidsBase H c := by
  induction c with
  | skip => trivial
  | atom a => exact avoidsAtom_mono sub h
  | seq a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | ite i a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | «while» i a ha => exact ha h

theorem avoidsCmd_mono (sub : ∀ i, H i → K i) {c : StructuredCalls.Cmd r s}
    (h : AvoidsCmd K c) : AvoidsCmd H c := by
  induction c with
  | base a => exact avoidsBase_mono sub h
  | call p => exact avoidsProgram_mono sub h
  | seq a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | ite i a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | «while» i a ha => exact ha h

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual frontend neither reads nor writes outer carried tapes. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Replay
open LeafProgram.OuterCarried

private theorem visible (i : Fin 768) (hi : i.val < 320 ∨ 332 < i.val) : ¬ LeafProgram.OuterCarried.hidden i := by
  simp only [LeafProgram.OuterCarried.hidden,List.mem_cons,List.mem_nil_iff,or_false]
  rintro (rfl|rfl|rfl) <;> norm_num at hi

private theorem block_visible (b n : ℕ) (h : b+n ≤ 768) (hb : 332 < b) (i : Fin n) :
    ¬ LeafProgram.OuterCarried.hidden (block b n h i) := by
  apply visible
  right
  dsimp [block]
  omega

private theorem copy_avoids (s d : Fin 768) (hs : ¬ LeafProgram.OuterCarried.hidden s) (hd : ¬ LeafProgram.OuterCarried.hidden d) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (copy s d) :=
  avoids_copyProgram LeafProgram.OuterCarried.hidden s d 679 0 1 hs hd (by decide)

private theorem copies_avoids (xs : List (Fin 768 × Fin 768))
    (h : ∀ p∈xs, ¬ LeafProgram.OuterCarried.hidden p.1 ∧ ¬ LeafProgram.OuterCarried.hidden p.2) : AvoidsCmd LeafProgram.OuterCarried.hidden (copies xs) := by
  induction xs with
  | nil => trivial
  | cons p ps ih => exact ⟨copy_avoids p.1 p.2 (h p (by simp)).1 (h p (by simp)).2,
      ih (fun q hq => h q (by simp [hq]))⟩

private theorem sequence_avoids (cs : List Code)
    (h : ∀ c∈cs, AvoidsCmd LeafProgram.OuterCarried.hidden c) : AvoidsCmd LeafProgram.OuterCarried.hidden (sequence cs) := by
  induction cs with
  | nil => trivial
  | cons c cs ih => exact ⟨h c (by simp),ih (fun d hd => h d (by simp [hd]))⟩

private theorem load_avoids (dst : Fin 768) (bits : List Bool) (hd : ¬ LeafProgram.OuterCarried.hidden dst) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (loadBits dst bits) := by
  apply avoids_liftProgram
  apply avoids_compiled
  change AvoidsCmd LeafProgram.OuterCarried.hidden (ArithmeticExpressionSupport.pushWord dst bits)
  induction bits with
  | nil => trivial
  | cons b bs ih => exact ⟨ih,trivial,hd⟩

private theorem clear_avoids (ps : List (Fin 768)) (hp : ∀ p∈ps, ¬ LeafProgram.OuterCarried.hidden p) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (BankRoutines.clearCmd 679 (0 : Fin 40) 1 ps) := by
  induction ps with
  | nil => exact avoids_clearProgram LeafProgram.OuterCarried.hidden 679 0 1 (by decide)
  | cons p ps ih => exact ⟨avoids_clearProgram LeafProgram.OuterCarried.hidden p 0 1 (hp p (by simp)),
      ih (fun q hq => hp q (by simp [hq]))⟩

private theorem export_field_avoids (f : Exports.Field) (hf : f.Good) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Exports.fieldCommand f) := by
  have hs : ¬ LeafProgram.OuterCarried.hidden f.src := visible _ (Or.inr (by have := hf.1; omega))
  have hd : ¬ LeafProgram.OuterCarried.hidden f.dst := visible _ (by rcases hf.2.2 with h|h; left; omega; right; omega)
  unfold Exports.fieldCommand
  split
  · apply avoids_liftCommand_of_range
    intro i
    unfold Exports.ports
    split
    · exact hs
    · split
      · exact hd
      · apply visible; right; dsimp; omega
  · exact avoids_copyProgram LeafProgram.OuterCarried.hidden f.src f.dst 679 0 1 hs hd (by decide)

private theorem export_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Exports.prepareCommand := by
  refine ⟨?_,?_,clear_avoids _ ?_⟩
  · apply avoids_liftCommand_of_range
    intro i
    apply visible
    right
    dsimp [Exports.bank]
    omega
  · change AvoidsCmd LeafProgram.OuterCarried.hidden (Exports.command Exports.fields)
    have h (fs : List Exports.Field) (hf : ∀ f∈fs, f.Good) :
        AvoidsCmd LeafProgram.OuterCarried.hidden (Exports.command fs) := by
      induction fs with
      | nil => trivial
      | cons f fs ih => exact ⟨export_field_avoids f (hf f (by simp)),
          ih (fun g hg => hf g (by simp [hg]))⟩
    exact h _ Exports.fields_good
  · intro p hp
    apply visible
    right
    have := (Exports.clearPorts_mem p).mp hp
    omega

private theorem binary_avoids (s d : Fin 768) (hs : ¬ LeafProgram.OuterCarried.hidden s) (hd : ¬ LeafProgram.OuterCarried.hidden d) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (binary s d) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> simp [binaryPorts,hs,hd]
  decide

/-- Syntactic avoidance includes peeks, so arbitrary carried words cannot affect time. -/
theorem frontend_avoids (k : ℕ) : AvoidsCmd LeafProgram.OuterCarried.hidden (frontend k) := by
  have hcount : AvoidsCmd LeafProgram.OuterCarried.hidden countHashes := by
    refine sequence_avoids _ ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro c (rfl|rfl)
    · exact copy_avoids _ _ (by decide) (by decide)
    · apply avoids_call_lift_of_range
      intro i; fin_cases i <;> decide
  have hraw : AvoidsCmd LeafProgram.OuterCarried.hidden rawCommand := by
    refine ⟨sequence_avoids _ ?_,?_,copy_avoids _ _ (by decide) (by decide)⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false]
      rintro c (rfl|rfl|rfl)
      · apply copies_avoids
        simp [scopeCopies,LeafProgram.OuterCarried.hidden]
      · exact load_avoids _ _ (by decide)
      · simp [resetScopeRegs,setRegs,SubexpParameterProgram.atoms,AvoidsBase,AvoidsAtom]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 500 80 _ (by decide))
  have hhigh : AvoidsCmd LeafProgram.OuterCarried.hidden highCommand := by
    refine sequence_avoids _ ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro c (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact copy_avoids _ _ (by decide) (by decide)
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 417 77 _ (by decide))
    · apply copies_avoids
      simp [highCopies,LeafProgram.OuterCarried.hidden]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 580 32 _ (by decide))
    · exact copy_avoids _ _ (by decide) (by decide)
    · apply avoids_call_lift_of_range
      intro i; fin_cases i <;> decide
  have hmeasure : AvoidsCmd LeafProgram.OuterCarried.hidden measureCommand := by
    refine sequence_avoids _ ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rintro c (rfl|rfl|rfl|rfl|rfl|rfl)
    · apply copies_avoids
      simp [statsCopies,LeafProgram.OuterCarried.hidden]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 612 21 _ (by decide))
    · apply copies_avoids
      simp [arityCopies,LeafProgram.OuterCarried.hidden]
    · simp [arityRegisters,setRegs,SubexpParameterProgram.atoms,AvoidsBase,AvoidsAtom]
    · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 633 12 _ (by decide))
    · apply avoids_call_lift_of_range
      intro i; fin_cases i <;> decide
  have hnumeric : AvoidsCmd LeafProgram.OuterCarried.hidden (numericStage k) := by
    refine ⟨copies_avoids _ ?_,load_avoids _ _ (by decide),sequence_avoids _ ?_⟩
    · simp [LeafProgram.OuterCarried.hidden]
    · simp only [List.mem_cons,List.not_mem_nil,or_false]
      rintro c (rfl|rfl|rfl|rfl|rfl) <;> exact binary_avoids _ _ (by decide) (by decide)
  refine ⟨hcount,⟨hraw,hhigh,hmeasure,hnumeric,?_⟩,export_avoids,?_,?_,?_⟩
  · exact avoids_call_lift_of_range LeafProgram.OuterCarried.hidden _ _ _ (block_visible 340 77 _ (by decide))
  · apply avoids_call_lift_of_range
    intro i; fin_cases i <;> decide
  · refine ⟨copy_avoids _ _ (by decide) (by decide),?_⟩
    apply avoids_call_lift_of_range
    intro i; fin_cases i <;> decide
  · apply clear_avoids
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    exact block_visible 417 262 _ (by decide) i

end Replay

/-- The concrete frontend does not read or write tapes 320, 322, or 332. -/
theorem frontend_avoids_outerCarried (k : ℕ) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (frontend k) := Replay.frontend_avoids k

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite syntax for both marked and final accepted queries. The only
program parameter is the fixed clause width. Every mark regenerates its own
physical high mask and zero counter. The semantic proof must establish that
the actual frontend guard holds on every reachable input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI BitProgram StructuredCalls HighQueryAdapter
noncomputable section

open HashGreedyProgram.NativeRound

namespace Carried

open SqrtLog.ProgramTapeReplay

local notation "H" => (fun i : Fin 896 => i ∈ words)

private theorem SafeAvoids.call {l : Nat} {p : Program 40 896 l}
    (hp : AvoidsProgram H p) :
    SafeAvoids (.call p) :=
  ⟨hp⟩

private theorem LowerSafeAvoids.intro {c : Cmd 40 768}
    (hc : AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) c) : LowerSafeAvoids c :=
  ⟨hc⟩

private theorem LowerSafeAvoids.ofMono {K : Fin 768 → Prop} {c : Cmd 40 768}
    (sub : ∀ i, (H ∘ HighMarkedFrontend.stackMap) i → K i)
    (hc : AvoidsCmd K c) : LowerSafeAvoids c :=
  ⟨avoidsCmd_mono sub hc⟩

private theorem LowerSafeAvoids.seq {first second : Cmd 40 768}
    (hfirst : LowerSafeAvoids first) (hsecond : LowerSafeAvoids second) :
    LowerSafeAvoids (.seq first second) :=
  ⟨⟨hfirst.proof, hsecond.proof⟩⟩

private theorem LowerSafeAvoids.liftCall {c : Cmd 40 768}
    (hc : LowerSafeAvoids c) (input output : Fin 768) :
    SafeAvoids (.call (ProgramLinking.liftProgram (compiled c input output)
      id HighMarkedFrontend.stackMap)) :=
  SafeAvoids.call (avoids_liftProgram H _ id HighMarkedFrontend.stackMap
    (avoids_compiled _ c hc.proof input output))

private theorem clear_bank {r s : ℕ} (K : Fin s → Prop)
    (tmp : Fin s) (value present : Fin r) (ports : List (Fin s))
    (ht : ¬K tmp) (hp : ∀ i∈ports, ¬K i) :
    AvoidsCmd K (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram K tmp value present ht
  | cons i is ih => exact ⟨avoids_clearProgram K i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

private theorem lower_subset (i : Fin 768) (hi : H (HighMarkedFrontend.stackMap i)) :
    SqrtLog.LeafProgram.OuterCarried.hidden i := by
  simp only [words,Finset.mem_insert,Finset.mem_singleton,HighMarkedFrontend.stackMap,
    Fin.ext_iff,Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at hi
  simp only [SqrtLog.LeafProgram.OuterCarried.hidden,List.mem_cons,
    Fin.ext_iff,Fin.coe_ofNat_eq_mod]
  have hv := i.isLt
  omega

private theorem mark_input :
    AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) SqrtLog.LeafProgram.Query.markInput := by
  refine ⟨avoids_copyProgram _ 321 699 698 0 1 (by decide) (by decide) (by decide),
    avoids_transferProgram _ 699 705 0 1 (by decide) (by decide), ?_⟩
  exact ⟨True.intro,⟨by change ¬(H ∘ HighMarkedFrontend.stackMap) 706; decide,True.intro⟩⟩

theorem frontend (k : ℕ) : AvoidsCmd H (HighMarkedFrontend.command k) := by
  have hfront := LowerSafeAvoids.ofMono lower_subset
    (SqrtLog.LeafQueryFrontend.frontend_avoids_outerCarried k)
  have hmark := LowerSafeAvoids.intro mark_input
  let hs := (hmark.seq hfront).liftCall 321 338
  have hpack : ∃ c, c = HighMarkedFrontend.command k ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [HighMarkedFrontend.command, HighMarkedFrontend.localProgram,
      SqrtLog.LeafProgram.Query.markedFrontend]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

private theorem seed_generator : AvoidsCmd H HighCountSeed.command := by
  refine ⟨⟨avoids_clearProgram H 791 0 1 (by decide),
    clear_bank H 791 0 1 _ (by decide) ?_⟩,
    avoids_copyProgram H 338 792 791 0 1 (by decide) (by decide) (by decide), ?_⟩
  · simp only [HighCountSeed.changed,List.mem_cons,List.not_mem_nil,or_false]
    rintro i (rfl|rfl|rfl) <;> decide
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

private theorem seed_install : AvoidsCmd H HighCountInit.command := by
  refine ⟨⟨avoids_clearProgram H 792 0 1 (by decide),
    clear_bank H 792 0 1 _ (by decide) ?_⟩,
    avoids_copyProgram H 330 789 792 0 1 (by decide) (by decide) (by decide), True.intro⟩
  simp only [HighCountInit.changed,List.mem_cons,List.not_mem_nil,or_false]
  rintro i (rfl|rfl|rfl|rfl|rfl|rfl) <;> decide

private theorem seed_program : AvoidsProgram H HighCountSeed.initializeProgram := by
  apply avoids_compiled
  exact ⟨avoids_compiled H _ seed_generator 338 330,
    avoids_compiled H _ seed_install 330 788⟩

private theorem copy_high : AvoidsCmd H copyHighCounter :=
  ⟨avoids_clearProgram H 330 0 1 (by decide),
    avoids_clearProgram H 792 0 1 (by decide),
    avoids_copyProgram H 789 330 792 0 1 (by decide) (by decide) (by decide)⟩

private theorem canonical : AvoidsCmd H HighQueryExecution.canonicalize := by
  apply avoids_compiled
  refine ⟨⟨avoids_clearProgram H 793 0 1 (by decide),
    avoids_clearProgram H 794 0 1 (by decide)⟩,?_⟩
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

private theorem route (src dst : Fin 896) (hs : ¬H src) (hd : ¬H dst) :
    AvoidsCmd H (SqrtLog.LeafOuterProgram.route (src,dst)) :=
  ⟨avoids_clearProgram H dst 0 1 hd,
    avoids_copyProgram H src dst 767 0 1 hs hd (by decide)⟩

private theorem finish : AvoidsCmd H HashMarkedQueryAdapter.finish := by
  refine ⟨route 788 323 (by decide) (by decide),
    clear_bank H 767 0 1 _ (by decide) ?_,?_⟩
  · simp only [HashMarkedQueryAdapter.cleanupPorts,List.mem_cons,List.not_mem_nil,or_false]
    rintro i (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> decide
  · exact ⟨True.intro,True.intro,True.intro,True.intro⟩

private theorem cleanup : AvoidsCmd H HighMarkedFrontend.cleanupCommand := by
  have hp : ∀ i∈SqrtLog.LeafProgram.Query.cleanupPorts,
      ¬(H ∘ HighMarkedFrontend.stackMap) i := by
    intro i hi hh
    have hprotect : SqrtLog.LeafProgram.Query.Protected i := by
      simp only [Function.comp_apply,words,Finset.mem_insert,Finset.mem_singleton,
        HighMarkedFrontend.stackMap,Fin.ext_iff,Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at hh
      simp only [SqrtLog.LeafProgram.Query.Protected,Fin.ext_iff,Fin.coe_ofNat_eq_mod]
      have hv := i.isLt
      omega
    exact ((SqrtLog.LeafProgram.Query.mem_cleanupPorts i).mp hi).1 hprotect
  have hc : AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) SqrtLog.LeafProgram.Query.cleanup := by
    unfold SqrtLog.LeafProgram.Query.cleanup
    generalize he : SqrtLog.LeafProgram.Query.cleanupPorts = ports
    have hv : ∀ i∈ports, ¬(H ∘ HighMarkedFrontend.stackMap) i := by
      rw [←he]
      exact hp
    exact ⟨avoids_clearProgram _ 699 0 1 (by decide),
      clear_bank (r:=40) (H ∘ HighMarkedFrontend.stackMap) 699 0 1 ports (by decide) hv⟩
  exact avoids_liftProgram H HighMarkedFrontend.cleanupLocalProgram id
    HighMarkedFrontend.stackMap
      (avoids_compiled _ SqrtLog.LeafProgram.Query.cleanup hc 699 323)

private theorem upper_cleanup : AvoidsCmd H HashMarkedReturn.upperClear := by
  have hp : ∀ i∈HashMarkedReturn.upperPorts, ¬H i := by
    intro i hi hh
    have hu := HashMarkedReturn.mem_upperPorts i |>.mp hi
    simp only [words,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,
      Fin.coe_ofNat_eq_mod] at hh
    omega
  unfold HashMarkedReturn.upperClear
  generalize he : HashMarkedReturn.upperPorts = ports
  have hv : ∀ i∈ports, ¬H i := by rw [←he]; exact hp
  exact clear_bank (r:=40) H 767 0 1 ports (by decide) hv

attribute [local irreducible] HashMarkedReturn.upperClear

theorem marked_return : AvoidsCmd H HighQueryExecution.markedReturn := by
  have hupper : AvoidsCmd H HashMarkedReturn.upperClear := upper_cleanup
  have hlower : AvoidsCmd H HighMarkedFrontend.cleanupCommand := cleanup
  have hfinish : AvoidsCmd H HashMarkedQueryAdapter.finish := finish
  have hcanonical : AvoidsCmd H HighQueryExecution.canonicalize := canonical
  have hr : AvoidsCmd H HashMarkedQueryAdapter.resetParser :=
    ⟨True.intro,True.intro,True.intro,True.intro⟩
  unfold HighQueryExecution.markedReturn HashMarkedReturn.command
  generalize hu : HashMarkedReturn.upperClear = upper at hupper ⊢
  generalize hl : HighMarkedFrontend.cleanupCommand = lower at hlower ⊢
  generalize hf : HashMarkedQueryAdapter.finish = finishCommand at hfinish ⊢
  generalize hc : HighQueryExecution.canonicalize = canonicalCommand at hcanonical ⊢
  exact ⟨hcanonical,hfinish,hlower,hupper,hr⟩

/-- The actual lower preparation excludes the collector tapes by its
instruction certificate; the selector words lie outside its lifted bank. -/
theorem preparation : AvoidsCmd H prepare := by
  have hcommand := LowerSafeAvoids.ofMono lower_subset
    NativeQueryPreparation.command_avoids
  let hs := hcommand.liftCall 700 728
  have hpack : ∃ c, c = prepare ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [prepare, preparationProgram]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

private theorem stream : AvoidsCmd H QueryStreamProgram.command := by
  apply avoidsCmd_mono (K:=fun i : Fin 896 => i.val=320 ∨ i.val=322 ∨
    i.val=770 ∨ i.val=771 ∨ i.val=781) _ QuerySelectorFrames.five_word_command_avoids
  intro i hi
  simpa only [words,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,
    Fin.coe_ofNat_eq_mod] using hi

theorem conditioned_avoids : AvoidsCmd H conditioned :=
  ⟨copy_high,stream,True.intro⟩

private theorem mass : AvoidsCmd H (SqrtLog.LeafProgram.Mass.invoke highPorts.mass) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem branch_avoids : AvoidsCmd H branch := ⟨conditioned_avoids,mass⟩

private theorem increment :
    AvoidsCmd H (ExecCNFTupleEnumeration.incrementCmd highPorts.counter) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem high_loop : AvoidsCmd H highLoop :=
  ⟨True.intro,branch_avoids,increment,True.intro⟩

theorem prepared_count : AvoidsCmd H preparedCount :=
  ⟨preparation,seed_program,high_loop⟩

theorem guarded_count : AvoidsCmd H guardedCount :=
  ⟨prepared_count,avoids_clearProgram H 788 0 1 (by decide)⟩

/-- Both fixed complete query programs exclude all five caller words from
reads and writes, including every called table, presence test and cleanup. -/
theorem marked_avoids (k : ℕ) : AvoidsCmd H (marked k) :=
  ⟨frontend k,guarded_count,marked_return⟩

/-- Erasing the five carried words is proof-side only. The actual command
runs for exactly the same number of steps while retaining their full bytes. -/
theorem marked_shadow_eval (k : ℕ) {steps : ℕ} {a b : Data}
    (he : Eval (marked k) steps (rebaseState H (fun _ => []) a) b) :
    Eval (marked k) steps a (rebaseState H a.stacks b) :=
  CommandStackTransport.eval_shadow H (marked_avoids k) he

end Carried

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryEntryShadow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The proof shadow erases exactly the five suspended caller words. Actual
query sources, reusable workspace, reference and temporary bytes are retained.
No length premise is imposed on any erased word; this module constructs no
execution and changes no instruction table. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay

/-- Visible words retain their complete bit strings. -/
theorem visible (a : Data) (i : Fin 896) (hi : i ∉ HighQueryProgram.Carried.words) :
    (erase a).stacks i = a.stacks i :=
  rebaseStacks_of_not_mem (fun j => j ∈ HighQueryProgram.Carried.words)
    (fun _ => []) a.stacks i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryReturnReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The complete fixed query has an actual same-step replay after erasing its
five suspended caller words. These lemmas transport the exact output contracts
and every prefix of that execution. They do not construct a query evaluator;
the actual marked or accepted execution is supplied by the count proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HashGreedyProgram.NativeRound HighQueryEntryShadow

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

theorem restore_visible (input output : Data) (i : Fin 896) (hi : ¬H i) :
    (restore input output).stacks i = output.stacks i :=
  rebaseStacks_of_not_mem H input.stacks output.stacks i hi

theorem restore_carried (input output : Data) (i : Fin 896) (hi : H i) :
    (restore input output).stacks i = input.stacks i :=
  rebaseStacks_of_mem H input.stacks output.stacks i hi

/-- Equality on all891 query workspace words survives restoration, including
the selector words which were erased for the source-only time proof. -/
theorem restore_workspace (input output : Data)
    (hw : HashMassAdapter.workspace output = HashMassAdapter.workspace (erase input)) :
    HashMassAdapter.workspace (restore input output) = HashMassAdapter.workspace input := by
  funext j
  let i := HashMassAdapter.workPort j
  change (restore input output).stacks i = input.stacks i
  by_cases hi : H i
  · exact restore_carried input output i hi
  · rw [restore_visible input output i hi]
    exact (congrFun hw j).trans (visible input i hi)

/-- The parser reset survives replay, while320 is the original unread tail.
No size or content restriction is placed on that tail or accumulated mass322. -/
theorem restore_record (input output : Data)
    (hp : output.regs 16 = false ∧ output.regs 17 = true ∧ output.regs 18 = false)
    (hb : output.stacks 321 = []) :
    RecordPrograms.state HashMassAdapter.recordPorts (restore input output)
      false true false (input.stacks 320) [] = restore input output := by
  apply RecordPrograms.state_eq_self
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2
  · exact restore_carried input output 320 (by decide)
  · exact (restore_visible input output 321 (by decide)).trans hb

/-- All actual marked prefixes, including the final halt, have the maximum
of the local workspace cap and the unchanged suspended caller-word cap. -/
theorem marked_space {k steps localBound frameBound : ℕ} {input output : Data}
    (he : Eval (HighQueryProgram.marked k) steps (erase input) output)
    (hs : StageSpace (HighQueryProgram.marked k) (steps+1) (erase input) localBound)
    (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
    StageSpace (HighQueryProgram.marked k) (steps+1) input (max localBound frameBound) := by
  exact ⟨CommandStackTransport.eval_shadow_prefix_bound H
    (HighQueryProgram.Carried.marked_avoids k) 778 777 he
    (fun t z ht hz i _ => hs.bound t z ht hz i) hf⟩

/-- The same fixed marked execution returns the canonical whole count, all
891 workspace words, both collector sources and the reset parser. Its step
count is exactly the step count of the actual shadow execution. -/
theorem marked_oai {k steps count localBound frameBound : ℕ} {input output : Data}
    (he : Eval (HighQueryProgram.marked k) steps (erase input) output)
    (hw : HashMassAdapter.workspace output = HashMassAdapter.workspace (erase input))
    (hp : output.regs 16 = false ∧ output.regs 17 = true ∧ output.regs 18 = false)
    (h321 : output.stacks 321 = []) (h324 : output.stacks 324 = [])
    (hcount : output.stacks 323 = countWord count)
    (hs : StageSpace (HighQueryProgram.marked k) (steps+1) (erase input) localBound)
    (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
    Eval (HighQueryProgram.marked k) steps input (restore input output) ∧
    HashMassAdapter.workspace (restore input output) = HashMassAdapter.workspace input ∧
    HashMassAdapter.read (restore input output) = HashMassAdapter.read input ∧
    RecordPrograms.state HashMassAdapter.recordPorts (restore input output)
      false true false (input.stacks 320) [] = restore input output ∧
    (restore input output).stacks 323 = countWord count ∧
    (restore input output).stacks 324 = [] ∧
    StageSpace (HighQueryProgram.marked k) (steps+1) input (max localBound frameBound) := by
  exact ⟨HighQueryProgram.Carried.marked_shadow_eval k he,
    restore_workspace input output hw,restore_carried input output 322 (by decide),
    restore_record input output hp h321,
    (restore_visible input output 323 (by decide)).trans hcount,
    (restore_visible input output 324 (by decide)).trans h324,marked_space he hs hf⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked_oai
