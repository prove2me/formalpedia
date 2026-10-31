-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepare_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:48:52.312228+00:00
-- url     : https://prove2.me/submissions/16a17b49-3692-42f2-88a5-502a0ca34b90

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Exports_cacheCall_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramInterval
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem prepare_frame (m : Model) (a : Fin 64) (ha : a.val < 46) :
    (result prepare m).val a=m.val a ∧ (result prepare m).len a=m.len a := by
  have hne (k : Fin 64) (hk : 46 ≤ k.val) : a≠k := by
    intro he; subst k; omega
  simp [prepare,result,next,output,lengthBound,hne _ (by decide : 46 ≤ (46 : Fin 64).val),
    hne _ (by decide : 46 ≤ (47 : Fin 64).val),hne _ (by decide : 46 ≤ (48 : Fin 64).val),
    hne _ (by decide : 46 ≤ (49 : Fin 64).val),hne _ (by decide : 46 ≤ (50 : Fin 64).val),
    hne _ (by decide : 46 ≤ (51 : Fin 64).val),hne _ (by decide : 46 ≤ (52 : Fin 64).val),
    hne _ (by decide : 46 ≤ (53 : Fin 64).val),hne _ (by decide : 46 ≤ (54 : Fin 64).val),
    hne _ (by decide : 46 ≤ (55 : Fin 64).val),hne _ (by decide : 46 ≤ (56 : Fin 64).val),
    hne _ (by decide : 46 ≤ (57 : Fin 64).val),hne _ (by decide : 46 ≤ (58 : Fin 64).val),
    hne _ (by decide : 46 ≤ (59 : Fin 64).val),hne _ (by decide : 46 ≤ (60 : Fin 64).val),
    hne _ (by decide : 46 ≤ (61 : Fin 64).val),hne _ (by decide : 46 ≤ (62 : Fin 64).val),
    hne _ (by decide : 46 ≤ (63 : Fin 64).val)]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem unaryCopyBound_le (bits : List Bool) (v l : ℕ)
    (hv : BinaryArithmetic.toNat bits=v) (hl : bits.length ≤ l) :
    Serialization.unaryCopyBound bits+1 ≤ unaryBound v l := by
  rw [Serialization.unaryCopyBound_eq,hv]
  calc
    _ = 7*bits.length+6+32*(v+1)*(bits.length+1) := by omega
    _ ≤ unaryBound v l := by
      dsimp [unaryBound]
      gcongr

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache

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

theorem field_eval (f : Field) (hf : f.Good) (a : Data)
    (hd : a.stacks f.dst=[]) (ht : Scratch a) :
    ∃ n  ≤  fieldCost f a, Eval (fieldCommand f) n a (fieldState f a) := by
  by_cases hu : f.unary=true
  · let d := projectState regs (ports f) a
    obtain ⟨n,hn,he⟩ := Serialization.unaryCopy_eval 0 1 d
      (by decide) (by decide) (by decide) (by decide)
      (by simpa [d,projectState,ports] using hd)
      (by simpa [d,projectState,ports] using ht.1)
      (by simpa [d,projectState,ports] using ht.2.1)
      (by simpa [d,projectState,ports] using ht.2.2.1)
    refine ⟨n+1,?_,?_⟩
    · simpa [fieldCost,hu,d,projectState,ports] using Nat.add_le_add_right hn 1
    · simpa [fieldCommand,fieldState,payload,hu,d,projectState,ports] using
        eval_liftCommand_from_state (Serialization.unaryCopy 0 1) 0 1 regs (ports f) a
          (Fin.castAdd_injective _ _) (ports_injective f hf) he
  · have hf' := hf
    dsimp [Field.Good] at hf'
    have hsd : f.src≠f.dst := by intro h; have := congrArg Fin.val h; omega
    have hst : f.src≠679 := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    have htd : (679 : Fin 768)≠f.dst := by intro h; have := congrArg Fin.val h; norm_num at this; omega
    refine ⟨7*(a.stacks f.src).length+5,by simp [fieldCost,hu],?_⟩
    simpa [fieldCommand,fieldState,hu] using
      SubexpScanPrimitives.copy_eval a f.src f.dst 679 0 1 hsd hst htd (by decide) ht.2.2.2

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

theorem command_eval (fs : List Field) (a : Data) (h : Ready fs a) :
    ∃ n  ≤  budget fs a, Eval (command fs) n a (finalState fs a) := by
  induction fs generalizing a with
  | nil => exact ⟨0,le_rfl,.base (.skip a)⟩
  | cons f fs ih =>
    obtain ⟨n,hn,he⟩ := field_eval f h.1 a h.2.1 h.2.2.1
    obtain ⟨k,hk,hke⟩ := ih _ h.2.2.2
    exact ⟨n+k,Nat.add_le_add hn hk,he.seq hke⟩

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

theorem source_ne_destination (f g : Field) (hf : f.Good) (hg : g.Good) : f.src≠g.dst := by
  intro h
  have := congrArg Fin.val h
  dsimp [Field.Good] at hf hg
  omega

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

theorem cost_frame (f g : Field) (hf : f.Good) (hg : g.Good) (a : Data)
    (hd : a.stacks f.dst=[]) : fieldCost g (fieldState f a)=fieldCost g a := by
  simp only [fieldCost,field_stacks f hf a hd,
    Function.update_of_ne (source_ne_destination g f hg hf)]

theorem ready_good (fs : List Field) (a : Data) (h : Ready fs a) : ∀ f∈fs, f.Good := by
  induction fs generalizing a with
  | nil => simp
  | cons f fs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · exact h.1
    · exact ih _ h.2.2.2 g hg

theorem budget_eq_sum (fs : List Field) (a : Data) (h : Ready fs a) :
    budget fs a=(fs.map (fun f => fieldCost f a)).sum := by
  induction fs generalizing a with
  | nil => rfl
  | cons f fs ih =>
    simp only [budget,List.map_cons,List.sum_cons]
    rw [ih _ h.2.2.2]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro g hg
    exact cost_frame f g h.1 (ready_good fs _ h.2.2.2 g hg) a h.2.1

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

theorem export_eval (a : Data) (ho : OutputEmpty a) (ht : Scratch a) :
    ∃ n  ≤  exportBudget a, Eval exportCommand n a (exportState a) := by
  have hr := fields_ready a ho ht
  simpa only [exportCommand,exportState,exportBudget,budget_eq_sum fields a hr] using
    command_eval fields a hr

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem bank_injective : Function.Injective bank := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [bank] at this; omega

theorem cached_stack (a : Data) (r : Regs) (w : Words) (i : Fin 64) :
    (cached a r w).stacks (bank (Bank.port i))=Cache.unaryWords w i := by
  exact (embedState_stack bankRegs bank a _ bank_injective (Bank.port i)).trans (Bank.state_port _ _ _)

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

theorem cacheLength_le (m : Model) (w : Words) (hs : Shape m w) (j : Fin 64) :
    (Cache.unaryWords w j).length ≤ cacheLength m j := by
  by_cases h53 : j=53
  · subst j; simp [Cache.unaryWords,cacheLength,hs.1 50]
  by_cases h52 : j=52
  · subst j; simp [Cache.unaryWords,cacheLength,hs.1 46]
  by_cases h51 : j=51
  · subst j; simp [Cache.unaryWords,cacheLength,hs.1 29]
  simpa [Cache.unaryWords,cacheLength,h53,h52,h51] using hs.2 j

theorem first_sources (i : Fin 16) (hi : i.val < 5) :
    localSource i≠51 ∧ localSource i≠52 ∧ localSource i≠53 := by
  fin_cases i <;> simp_all [localSource]

theorem exportField_le (m : Model) (w : Words) (hs : Shape m w)
    (a : Data) (r : Regs) (i : Fin 16) :
    fieldCost (field i) (cached a r w) ≤ exportFieldBound m i := by
  have hword : (cached a r w).stacks (field i).src=Cache.unaryWords w (localSource i) :=
    cached_stack a r w (localSource i)
  simp only [fieldCost,hword,exportFieldBound]
  by_cases hi : i.val < 5
  · obtain ⟨h51,h52,h53⟩ := first_sources i hi
    simpa [field,hi,Cache.unaryWords,h51,h52,h53] using
      Cache.unaryCopyBound_le (w (localSource i)) (m.val (localSource i))
        (m.len (localSource i)) (hs.1 _) (hs.2 _)
  · simp only [field,hi,decide_false,Bool.false_eq_true,ite_false]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 7 (cacheLength_le m w hs _)) 5

theorem exportBudget_le (m : Model) (w : Words) (hs : Shape m w) (a : Data) (r : Regs) :
    exportBudget (cached a r w) ≤ exportModelBudget m := by
  simp only [exportBudget,fields,List.map_map,Function.comp_def,exportModelBudget]
  apply List.sum_le_sum
  intro i hi
  exact exportField_le m w hs a r i

theorem clearPorts_nodup : clearPorts.Nodup := by decide

theorem clearCommand_eval (a : Data) (ht : a.stacks 679=[]) :
    Eval clearCommand (clearCost a) a (cleared a) := by
  have he := BankRoutines.clear_eval 679 (0 : Fin 40) 1 clearPorts clearPorts_nodup a.regs a.stacks ht
  simpa only [clearCommand,clearCost,cleared,clearPorts,List.length_map,List.length_finRange,
    show 3*18+3=57 by decide] using he

theorem clearCost_le (m : Model) (w : Words) (hs : Shape m w) (a : Data) (r : Regs)
    (ho : OutputEmpty (cached a r w)) (ht : Scratch (cached a r w)) :
    clearCost (exportState (cached a r w)) ≤ clearModelBudget m := by
  simp only [clearCost,clearPorts,List.map_map,Function.comp_def,clearModelBudget]
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  apply List.sum_le_sum
  intro i hi
  have hn : ∀ j, destination j≠bank ⟨46+i.val,by omega⟩ := by
    intro j heq
    have hj := destination_outside j
    have hv := congrArg Fin.val heq
    dsimp [bank] at hv
    have := i.isLt
    omega
  rw [export_stack_frame _ ho ht _ hn]
  have hbank : (⟨46+i.val,by omega⟩ : Fin 77)=Bank.port ⟨46+i.val,by omega⟩ := rfl
  rw [hbank,cached_stack]
  exact cacheLength_le m w hs _

theorem intervalModel_frame (m : Model) (j : Fin 64) (hj : j.val < 46) :
    (Interval.finalModel m).val j=m.val j ∧ (Interval.finalModel m).len j=m.len j := by
  have h46 : j≠46 := by intro h; subst j; norm_num at hj
  have h47 : j≠47 := by intro h; subst j; norm_num at hj
  have h48 : j≠48 := by intro h; subst j; norm_num at hj
  have h49 : j≠49 := by intro h; subst j; norm_num at hj
  have h50 : j≠50 := by intro h; subst j; norm_num at hj
  simpa [Interval.finalModel,CacheWidth.code,Interval.intervalModel,result,next,output,
    lengthBound,h46,h47,h48,h49,h50] using Interval.prepare_frame m j hj

theorem restored_shape (m : Model) (w : Words) (hs : Shape (Interval.finalModel m) w)
    (hz : ∀ j,46 ≤ j.val → m.val j=0) : Shape m (restoredWords w) := by
  constructor
  · intro j
    by_cases hj : 46 ≤ j.val
    · simp [restoredWords,hj,hz j hj]
    · simpa [restoredWords,hj,(intervalModel_frame m j (by omega)).1] using hs.1 j
  · intro j
    by_cases hj : 46 ≤ j.val
    · simp [restoredWords,hj]
    · simpa [restoredWords,hj,(intervalModel_frame m j (by omega)).2] using hs.2 j

theorem prepare_eval_oai (a : Data) (m : Model) (w : Words) (hs : Shape m w)
    (hp : projectState bankRegs bank a=Bank.state (a.regs ∘ bankRegs) w)
    (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
    (ho : OutputEmpty a) (ht : Scratch a) :
    ∃ n ≤ prepareBudget m, ∃ rf wb,
      Eval prepareCommand n a (cleared (exportState (cached a rf wb))) ∧
      Shape (Interval.finalModel m) wb ∧ Shape m (restoredWords wb) := by
  obtain ⟨nc,hnc,rf,wb,hec,hsb⟩ := cacheCall_eval a m w hs hp hr
  have ho' := cached_empty a rf wb ho
  have ht' := cached_scratch a rf wb ht
  obtain ⟨ne,hne,hee⟩ := export_eval (cached a rf wb) ho' ht'
  have htmp : (exportState (cached a rf wb)).stacks 679=[] := by
    rw [export_stack_frame _ ho' ht' _ (by intro i; fin_cases i <;> decide)]
    exact ht'.2.2.2
  have heclear := clearCommand_eval (exportState (cached a rf wb)) htmp
  refine ⟨nc+(ne+clearCost (exportState (cached a rf wb))),?_,rf,wb,hec.seq (hee.seq heclear),
    hsb,restored_shape m wb hsb hz⟩
  have heB := exportBudget_le (Interval.finalModel m) wb hsb a rf
  have hcB := clearCost_le (Interval.finalModel m) wb hsb a rf ho' ht'
  dsimp [prepareBudget]
  omega


end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepare_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepare_eval_oai
