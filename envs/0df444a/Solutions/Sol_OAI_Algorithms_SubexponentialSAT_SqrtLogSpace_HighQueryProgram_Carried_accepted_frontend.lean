-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.accepted_frontend
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:17:28.681627+00:00
-- url     : https://prove2.me/submissions/0c6e8abe-58f7-425f-81ba-7fbbe43f0534

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S183

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

private theorem lower_subset (i : Fin 768) (hi : H (HighMarkedFrontend.stackMap i)) :
    SqrtLog.LeafProgram.OuterCarried.hidden i := by
  simp only [words,Finset.mem_insert,Finset.mem_singleton,HighMarkedFrontend.stackMap,
    Fin.ext_iff,Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at hi
  simp only [SqrtLog.LeafProgram.OuterCarried.hidden,List.mem_cons,
    Fin.ext_iff,Fin.coe_ofNat_eq_mod]
  have hv := i.isLt
  omega

private theorem no_mark_input :
    AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) SqrtLog.LeafProgram.Query.noMarkInput :=
  ⟨True.intro,⟨by change ¬(H ∘ HighMarkedFrontend.stackMap) 705; decide,
    ⟨by change ¬(H ∘ HighMarkedFrontend.stackMap) 706; decide,True.intro⟩⟩⟩

theorem accepted_frontend_oai (k : ℕ) : AvoidsCmd H (HighMarkedFrontend.acceptedCommand k) := by
  have hfront := LowerSafeAvoids.ofMono lower_subset
    (SqrtLog.LeafQueryFrontend.frontend_avoids_outerCarried k)
  have hmark := LowerSafeAvoids.intro no_mark_input
  let hs := (hmark.seq hfront).liftCall 700 338
  have hpack : ∃ c, c = HighMarkedFrontend.acceptedCommand k ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [HighMarkedFrontend.acceptedCommand, HighMarkedFrontend.acceptedLocalProgram,
      HighMarkedFrontend.acceptedLocalCommand]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

attribute [local irreducible] HashMarkedReturn.upperClear

end Carried

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.accepted_frontend_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.accepted_frontend_oai
