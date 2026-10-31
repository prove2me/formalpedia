-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:01:05.684566+00:00
-- url     : https://prove2.me/submissions/aa82c769-9b28-47f9-94be-1e72c280372c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Exports_prepare_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Exports_prepared_binary
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Exports_prepared_binary_length
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_lowMask_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_offset_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearBankStacks_frame {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∉ ports) :
    clearBankStacks ports stk j = stk j := by
  simp [clearBankStacks, hj]

theorem clearStacks_eq_self_of_empty {S : Type u} [DecidableEq S]
    (tmp : S) (stk : Stacks S) (htmp : stk tmp = []) :
    clearStacks tmp stk = stk := by
  funext j
  by_cases hj : j = tmp
  · subst j
    simp [htmp]
  · exact clearStacks_frame _ _ _ hj

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

/-- Exact clearing cost in terms of the original word lengths.  The temporary
may also occur in the bank: its initial emptiness makes the final clear cost
exactly three instructions in either case. -/
theorem clear_eval {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports)
      (2 * (ports.map (fun j => (stk j).length)).sum + 3 * ports.length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  induction ports generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [clearCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hports
      have htemp : clearStacks dst stk tmp = [] := by
        by_cases h : tmp = dst
        · subst tmp
          simp
        · rw [clearStacks_frame dst tmp stk h, htmpEmpty]
      have hmap : ports.map (fun j => (clearStacks dst stk j).length) =
          ports.map (fun j => (stk j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [clearStacks_frame dst j stk hjd]
      have first := clear_call_eval dst value present regs stk
      have rest := ih hn.2 (readRegs regs value present none)
        (clearStacks dst stk) htemp
      have run := Eval.seq first rest
      simpa only [clearCmd, List.map_cons, List.sum_cons, List.length_cons,
        hmap, readRegs_reset, clearBankStacks_cons, Nat.mul_add,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- One stack update in the local result becomes the same update at its
assigned caller port. This is an equality of state descriptions. -/
theorem embedState_update_stack {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (frame : State R S) (d : State r s) (hs : Function.Injective stack)
    (k : Fin s) (word : List Bool) :
    embedState register stack frame { d with «stacks» := Function.update d.stacks k word } =
      { embedState register stack frame d with
        «stacks» := Function.update (embedState register stack frame d).stacks (stack k) word } := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · exact ProgramLinking.extend_update hs d.stacks frame.stacks k word

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

/-- Explicit polynomial in the numerical R and the physical source widths. -/
theorem budget_eq (B Q R : List Bool) :
    budget B Q R=5000*(2*BinaryArithmetic.toNat R+1)^2*(B.length+Q.length+R.length+11)^2 := by
  unfold budget width sourceWidth
  ring

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExportsOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid metadata exports. These commands touch only their destination and
three working registers; binary sources and all scratch words are restored. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem ports_injective (f : Field) (hf : f.Good) : Function.Injective (ports f) := by
  intro i j h
  dsimp [Field.Good] at hf
  fin_cases i <;> fin_cases j <;> simp_all [ports,Fin.ext_iff]
  all_goals omega

theorem field_stacks (f : Field) (hf : f.Good) (a : Data) (hd : a.stacks f.dst=[]) :
    (fieldState f a).stacks=Function.update a.stacks f.dst (payload f a) := by
  by_cases hu : f.unary=true
  · let d := projectState regs (ports f) a
    have hb : (embedState regs (ports f) a
        (⟨SubexpClauseMastersProgram.zeroRegs,d.stacks⟩ : Serialization.Data)).stacks=a.stacks := by
      change (embedState regs (ports f) a d).stacks=a.stacks
      exact congrArg (fun z => z.stacks)
        (embedState_project regs (ports f) a (Fin.castAdd_injective _ _) (ports_injective f hf))
    simp only [fieldState,hu,ite_true, if_true]
    dsimp only [SubexpClauseMastersProgram.write]
    rw [show (⟨SubexpClauseMastersProgram.zeroRegs,
      Function.update (projectState regs (ports f) a).stacks 1 (payload f a)⟩ : Serialization.Data)=
      { (⟨SubexpClauseMastersProgram.zeroRegs,d.stacks⟩ : Serialization.Data) with
        «stacks» := Function.update d.stacks 1 (payload f a) } by rfl]
    rw [embedState_update_stack regs (ports f) a _ (ports_injective f hf) 1 (payload f a)]
    simpa [ports] using congrArg (fun w => Function.update w f.dst (payload f a)) hb
  · simp [fieldState,hu,payload,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,hd]

theorem final_stack_frame (fs : List Field) (a : Data) (h : Ready fs a)
    (i : Fin 768) (hi : ∀ f∈fs, f.dst≠i) : (finalState fs a).stacks i=a.stacks i := by
  induction fs generalizing a with
  | nil => rfl
  | cons f fs ih =>
    rw [finalState,ih _ h.2.2.2 (fun g hg => hi g (List.mem_cons_of_mem _ hg)),
      field_stacks f h.1 a h.2.1]
    exact Function.update_of_ne (Ne.symm (hi f List.mem_cons_self)) _ _

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
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

theorem destination_ne_scratch (f : Field) (hf : f.Good) :
    f.dst≠659 ∧ f.dst≠660 ∧ f.dst≠661 ∧ f.dst≠679 := by
  dsimp [Field.Good] at hf
  constructor
  · intro h; have := congrArg Fin.val h; norm_num at this; omega
  constructor
  · intro h; have := congrArg Fin.val h; norm_num at this; omega
  constructor
  · intro h; have := congrArg Fin.val h; norm_num at this; omega
  · intro h; have := congrArg Fin.val h; norm_num at this; omega

theorem ready_of_empty (fs : List Field) (a : Data)
    (hg : ∀ f∈fs, f.Good) (hn : (fs.map Field.dst).Nodup)
    (he : ∀ f∈fs, a.stacks f.dst=[]) (ht : Scratch a) : Ready fs a := by
  induction fs generalizing a with
  | nil => trivial
  | cons f fs ih =>
    have hf := hg f List.mem_cons_self
    have hfd := he f List.mem_cons_self
    have hn' := List.nodup_cons.mp (show (f.dst :: fs.map Field.dst).Nodup from hn)
    have hdiff : ∀ g∈fs, g.dst≠f.dst := by
      intro g hgm h
      apply hn'.1
      exact List.mem_map.mpr ⟨g,hgm,h⟩
    have hst := field_stacks f hf a hfd
    refine ⟨hf,hfd,ht,ih _ (fun g hgm => hg g (List.mem_cons_of_mem _ hgm)) hn'.2 ?_ ?_⟩
    · intro g hgm
      rw [hst,Function.update_of_ne (hdiff g hgm)]
      exact he g (List.mem_cons_of_mem _ hgm)
    · obtain ⟨h1,h2,h3,h4⟩ := destination_ne_scratch f hf
      simpa only [Scratch,hst,Function.update_of_ne h1.symm,
        Function.update_of_ne h2.symm,Function.update_of_ne h3.symm,
        Function.update_of_ne h4.symm] using ht

theorem fields_good : ∀ f∈fields, f.Good := by
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  fin_cases i <;> simp [Field.Good,field,localSource,destination]
theorem fields_nodup : (fields.map Field.dst).Nodup := by decide

theorem fields_ready (a : Data) (ho : OutputEmpty a) (ht : Scratch a) : Ready fields a := by
  apply ready_of_empty fields a fields_good fields_nodup _ ht
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  exact ho i

theorem export_stack_frame (a : Data) (ho : OutputEmpty a) (ht : Scratch a)
    (j : Fin 768) (hj : ∀ i, destination i≠j) : (exportState a).stacks j=a.stacks j := by
  apply final_stack_frame fields a (fields_ready a ho ht) j
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  exact hj i

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

theorem cached_frame (a : Data) (r : Regs) (w : Words) (j : Fin 768)
    (hj : j.val < 340 ∨ 417 ≤ j.val) : (cached a r w).stacks j=a.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i,hi⟩
  have := congrArg Fin.val hi
  dsimp [bank] at this
  have := i.isLt
  omega

theorem destination_outside (i : Fin 16) :
    (destination i).val < 340 ∨ 417 ≤ (destination i).val := by fin_cases i <;> decide

theorem cached_empty (a : Data) (r : Regs) (w : Words) (ho : OutputEmpty a) :
    OutputEmpty (cached a r w) := by
  intro i
  rw [cached_frame a r w _ (destination_outside i)]
  exact ho i

theorem cached_scratch (a : Data) (r : Regs) (w : Words) (ht : Scratch a) :
    Scratch (cached a r w) := by
  simpa only [Scratch,cached_frame a r w 659 (by decide),
    cached_frame a r w 660 (by decide),cached_frame a r w 661 (by decide),
    cached_frame a r w 679 (by decide)] using ht

theorem clearPorts_mem (j : Fin 768) : j∈clearPorts ↔ 386 ≤ j.val ∧ j.val < 404 := by
  simp only [clearPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,rfl⟩; dsimp [bank]; have := i.isLt; omega
  · intro hj
    refine ⟨⟨j.val-386,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [bank]
    omega

theorem prepared_stack_frame (a : Data) (r : Regs) (w : Words)
    (ho : OutputEmpty a) (ht : Scratch a) (j : Fin 768)
    (hb : j.val < 340 ∨ 417 ≤ j.val) (hj : ∀ i, destination i≠j) :
    (cleared (exportState (cached a r w))).stacks j=a.stacks j := by
  change BankRoutines.clearBankStacks clearPorts _ j=_
  rw [BankRoutines.clearBankStacks_frame]
  · rw [export_stack_frame _ (cached_empty a r w ho) (cached_scratch a r w ht) j hj]
    exact cached_frame a r w j hb
  · rw [clearPorts_mem]; omega

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed disjoint work areas for the per-query native frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
theorem block_injective (base n : ℕ) (hn : base+n ≤ 768) : Function.Injective (block base n hn) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [block] at this; omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem cleanup_eval (a : Data) (ht : a.stacks 679=[]) :
    Eval clearPrivate (cleanupCost a) a (cleaned a) := by
  have h := BankRoutines.clear_eval (679 : Fin 768) (0 : Fin 40) 1 cleanupPorts
    (List.nodup_finRange 262 |>.map (block_injective ..)) a.regs a.stacks ht
  simpa [clearPrivate,cleanupPorts,cleanupCost,cleaned] using h

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendGrowth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem eval_length_le {c : Code} {n : ℕ} {a b : Data} (he : Eval c n a b)
    (i : Fin 768) : (b.stacks i).length ≤ (a.stacks i).length+n := by
  exact Subexp.SequentialProgram.trace_stack_length_le (compiled_trace he i i) i

theorem cleanupCost_le (a : Data) (A : ℕ)
    (ha : ∀ i ∈ cleanupPorts,(a.stacks i).length ≤ A) : cleanupCost a ≤ 524*A+789 := by
  have hsum : (cleanupPorts.map (fun i => (a.stacks i).length)).sum ≤
      (cleanupPorts.map (fun _ => A)).sum := by
    apply List.sum_le_sum
    exact ha
  have hlen : cleanupPorts.length=262 := by simp [cleanupPorts]
  have hc : (cleanupPorts.map (fun _ => A)).sum=262*A := by
    rw [List.map_const',List.sum_replicate,hlen]
    simp []
  rw [hc] at hsum
  unfold cleanupCost
  omega

theorem cleanupCost_le_after_eval {c : Code} {n A : ℕ} {a b : Data}
    (he : Eval c n a b) (ha : ∀ i ∈ cleanupPorts,(a.stacks i).length ≤ A) :
    cleanupCost b ≤ 524*(A+n)+789 := by
  apply cleanupCost_le
  intro i hi
  exact (eval_length_le he i).trans (Nat.add_le_add_right (ha i hi) n)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid persistent metadata export, offset construction, mask conversion, and
scratch cleanup after the guarded numeric bank has been computed. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram


theorem export_destination_not_private (i : Fin 16) :
    (Exports.destination i).val < 340 ∨ 680 ≤ (Exports.destination i).val := by
  fin_cases i <;> decide

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPostBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Input-only bound for the export/offset/mask/cleanup suffix. The live-word
bound A is propagated from the preceding actual evaluation. -/
theorem postCommand_eval_uniform_oai (a : Data) (m : Circuit.Model) (w : Bank.Words)
    (hs : Circuit.Shape m w)
    (hp : projectState Exports.bankRegs Exports.bank a=Bank.state (a.regs ∘ Exports.bankRegs) w)
    (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
    (ho : Exports.OutputEmpty a) (ht : emptyRange a 648 680)
    (h134 : a.stacks 134=[]) (h141 : a.stacks 141=[])
    (descending : List Bool) (h338 : a.stacks 338=descending)
    (A : ℕ) (ha : ∀ i∈cleanupPorts, (a.stacks i).length ≤ A) :
    ∃ n b, Eval postCommand n a b ∧ n ≤ postUniformBudget m descending.length A := by
  have hscratch : Exports.Scratch a := ⟨ht _ (by decide) (by decide),ht _ (by decide) (by decide),
    ht _ (by decide) (by decide),ht _ (by decide) (by decide)⟩
  obtain ⟨ne,hne,rf,wb,hee,hsb,hsr⟩ := Exports.prepare_eval a m w hs hp hr hz ho hscratch
  let e := Exports.cleared (Exports.exportState (Exports.cached a rf wb))
  have ef (i : Fin 768) (hi : i.val < 340 ∨ 417 ≤ i.val) (hd : ∀ j,Exports.destination j≠i) :
      e.stacks i=a.stacks i := Exports.prepared_stack_frame a rf wb ho hscratch i hi hd
  have ez : emptyRange e 648 680 := by
    intro i hi hj
    apply (ef i (Or.inr (by omega)) ?_).trans (ht i hi hj)
    intro j heq
    have hv := congrArg Fin.val heq
    have hd := export_destination_not_private j
    omega
  have e141 : e.stacks 141=[] := (ef _ (Or.inl (by decide)) (by intro j; fin_cases j <;> decide)).trans h141
  obtain ⟨no,hno,o,heo,hov,hol,ofr,ogr⟩ := offset_eval e
    (fun i hi hj => ez i (by omega) (by omega)) e141
  have hbB := Exports.prepared_binary_length a rf m wb hsb ho hscratch 5
  have hbQ := Exports.prepared_binary_length a rf m wb hsb ho hscratch 0
  have hbR := Exports.prepared_binary_length a rf m wb hsb ho hscratch 7
  have hvR := Exports.prepared_binary a rf m wb hsb ho hscratch 7
  change (e.stacks 725).length ≤ m.len 3 at hbB
  change (e.stacks 720).length ≤ m.len 21 at hbQ
  change (e.stacks 727).length ≤ m.len 29 at hbR
  change BinaryArithmetic.toNat (e.stacks 727)=m.val 29 at hvR
  have hbo : LayoutOffsetProgram.budget (e.stacks 725) (e.stacks 720) (e.stacks 727) ≤ offsetModelBudget m := by
    rw [LayoutOffsetProgram.budget_eq,hvR]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega
  have oz : emptyRange o 648 680 := by
    intro i hi hj
    exact (ofr i (by intro heq; subst i; norm_num at hi)).trans (ez i hi hj)
  have o134 : o.stacks 134=[] := (ofr _ (by decide)).trans
    ((ef _ (Or.inl (by decide)) (by intro j; fin_cases j <;> decide)).trans h134)
  have o338 : o.stacks 338=descending := (ofr _ (by decide)).trans
    ((ef _ (Or.inl (by decide)) (by intro j; fin_cases j <;> decide)).trans h338)
  obtain ⟨c,hec,hc134,hc668,cfr,cgr⟩ := lowMask_eval o descending o338 o134
    (oz _ (by decide) (by decide)) (oz _ (by decide) (by decide))
  have c679 : c.stacks 679=[] := (cfr _ (by decide) (by decide)).trans (oz _ (by decide) (by decide))
  have heclear := cleanup_eval c c679
  have hclean := cleanupCost_le_after_eval (hee.seq (heo.seq hec)) ha
  refine ⟨ne+(no+(12*descending.length+8+cleanupCost c)),cleaned c,
    hee.seq (heo.seq (hec.seq heclear)),?_⟩
  unfold postUniformBudget postPrefixBudget
  omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval_uniform_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.postCommand_eval_uniform_oai
