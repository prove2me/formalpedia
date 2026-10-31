-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.accepted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:23:45.043369+00:00
-- url     : https://prove2.me/submissions/77f019b8-54b9-4cea-b54f-a2c4d859a81a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighQueryProgram_Carried_accepted_frontend
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

private theorem LowerSafeAvoids.ofMono {K : Fin 768 → Prop} {c : Cmd 40 768}
    (sub : ∀ i, (H ∘ HighMarkedFrontend.stackMap) i → K i)
    (hc : AvoidsCmd K c) : LowerSafeAvoids c :=
  ⟨avoidsCmd_mono sub hc⟩

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

private theorem sequence (first second : Code)
    (hf : AvoidsCmd H first) (hs : AvoidsCmd H second) :
    AvoidsCmd H (.seq first second) := ⟨hf,hs⟩

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

theorem accepted_return : AvoidsCmd H HighQueryExecution.acceptedReturn := by
  have hi := sequence (SqrtLog.LeafOuterProgram.route (323,788))
    (.call (StackRoutines.clearProgram 323 0 1)) (route 323 788 (by decide) (by decide))
      (avoids_clearProgram H 323 0 1 (by decide))
  exact sequence HighQueryExecution.markedReturn HighQueryExecution.installAccepted marked_return hi

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

theorem accepted_avoids (k : ℕ) : AvoidsCmd H (accepted k) :=
  ⟨accepted_frontend k,guarded_count,accepted_return⟩

theorem accepted_shadow_eval (k : ℕ) {steps : ℕ} {a b : Data}
    (he : Eval (accepted k) steps (rebaseState H (fun _ => []) a) b) :
    Eval (accepted k) steps a (rebaseState H a.stacks b) :=
  CommandStackTransport.eval_shadow H (accepted_avoids k) he

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

/-- The accepted output changes only788 in the original whole store. The
complete binary word and every opaque caller byte are retained exactly. -/
theorem restore_accepted_stacks (input output : Data) (word : List Bool)
    (hw : output.stacks = Function.update (erase input).stacks 788 word) :
    (restore input output).stacks = Function.update input.stacks 788 word := by
  funext i
  by_cases hi : H i
  · have hn : i ≠ 788 := by intro he; subst i; exact (by decide : ¬H 788) hi
    rw [restore_carried input output i hi,Function.update_of_ne hn]
  · rw [restore_visible input output i hi,hw]
    by_cases hc : i = 788
    · subst i; simp only [Function.update_self]
    · rw [Function.update_of_ne hc,Function.update_of_ne hc,visible input i hi]

theorem accepted_space {k steps localBound frameBound : ℕ} {input output : Data}
    (he : Eval (HighQueryProgram.accepted k) steps (erase input) output)
    (hs : StageSpace (HighQueryProgram.accepted k) (steps+1) (erase input) localBound)
    (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
    StageSpace (HighQueryProgram.accepted k) (steps+1) input (max localBound frameBound) := by
  exact ⟨CommandStackTransport.eval_shadow_prefix_bound H
    (HighQueryProgram.Carried.accepted_avoids k) 778 777 he
    (fun t z ht hz i _ => hs.bound t z ht hz i) hf⟩

/-- The same fixed accepted execution changes precisely the whole count788.
The time bound needs no lengths of the five suspended caller words; their
lengths occur only in the independent maximum-prefix bound. -/
theorem accepted_oai {k steps count localBound frameBound : ℕ} {input output : Data}
    (he : Eval (HighQueryProgram.accepted k) steps (erase input) output)
    (hw : output.stacks = Function.update (erase input).stacks 788 (countWord count))
    (hs : StageSpace (HighQueryProgram.accepted k) (steps+1) (erase input) localBound)
    (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
    Eval (HighQueryProgram.accepted k) steps input (restore input output) ∧
    (restore input output).stacks = Function.update input.stacks 788 (countWord count) ∧
    StageSpace (HighQueryProgram.accepted k) (steps+1) input (max localBound frameBound) := by
  exact ⟨HighQueryProgram.Carried.accepted_shadow_eval k he,
    restore_accepted_stacks input output _ hw,accepted_space he hs hf⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.accepted_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.accepted_oai
