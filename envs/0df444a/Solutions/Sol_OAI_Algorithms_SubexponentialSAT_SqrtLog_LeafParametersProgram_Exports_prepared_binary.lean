-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:54:21.333529+00:00
-- url     : https://prove2.me/submissions/dabca89f-3177-4332-946b-d63bdfc8fe8a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S169

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

theorem payload_frame (f g : Field) (hf : f.Good) (hg : g.Good) (a : Data)
    (hd : a.stacks f.dst=[]) : payload g (fieldState f a)=payload g a := by
  simp only [payload,field_stacks f hf a hd,
    Function.update_of_ne (source_ne_destination g f hg hf)]

theorem ready_good (fs : List Field) (a : Data) (h : Ready fs a) : ∀ f∈fs, f.Good := by
  induction fs generalizing a with
  | nil => simp
  | cons f fs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · exact h.1
    · exact ih _ h.2.2.2 g hg

theorem final_output (fs : List Field) (a : Data) (h : Ready fs a)
    (hn : (fs.map Field.dst).Nodup) (g : Field) (hg : g∈fs) :
    (finalState fs a).stacks g.dst=payload g a := by
  induction fs generalizing a with
  | nil => simp at hg
  | cons f fs ih =>
    have hn' := List.nodup_cons.mp (show (f.dst :: fs.map Field.dst).Nodup from hn)
    rcases List.mem_cons.mp hg with rfl|hg
    · rw [finalState,final_stack_frame fs _ h.2.2.2 g.dst]
      · rw [field_stacks g h.1 a h.2.1,Function.update_self]
      · intro k hk heq
        exact hn'.1 (List.mem_map.mpr ⟨k,hk,heq⟩)
    · exact (ih _ h.2.2.2 hn'.2 hg).trans
        (payload_frame f g h.1 (ready_good fs _ h.2.2.2 g hg) a h.2.1)

theorem fields_good : ∀ f∈fields, f.Good := by
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  fin_cases i <;> simp [Field.Good,field,localSource,destination]
theorem fields_nodup : (fields.map Field.dst).Nodup := by decide
theorem field_mem (i : Fin 16) : field i∈fields := List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩

theorem fields_ready (a : Data) (ho : OutputEmpty a) (ht : Scratch a) : Ready fields a := by
  apply ready_of_empty fields a fields_good fields_nodup _ ht
  intro f hf
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
  exact ho i

theorem export_output (a : Data) (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 16) :
    (exportState a).stacks (destination i)=payload (field i) a :=
  final_output fields a (fields_ready a ho ht) fields_nodup (field i) (field_mem i)

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

theorem clearPorts_mem (j : Fin 768) : j∈clearPorts ↔ 386 ≤ j.val ∧ j.val < 404 := by
  simp only [clearPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,rfl⟩; dsimp [bank]; have := i.isLt; omega
  · intro hj
    refine ⟨⟨j.val-386,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [bank]
    omega

theorem intervalModel_frame (m : Model) (j : Fin 64) (hj : j.val < 46) :
    (Interval.finalModel m).val j=m.val j ∧ (Interval.finalModel m).len j=m.len j := by
  have h46 : j≠46 := by intro h; subst j; norm_num at hj
  have h47 : j≠47 := by intro h; subst j; norm_num at hj
  have h48 : j≠48 := by intro h; subst j; norm_num at hj
  have h49 : j≠49 := by intro h; subst j; norm_num at hj
  have h50 : j≠50 := by intro h; subst j; norm_num at hj
  simpa [Interval.finalModel,CacheWidth.code,Interval.intervalModel,result,next,output,
    lengthBound,h46,h47,h48,h49,h50] using Interval.prepare_frame m j hj


theorem clear_output_frame (a : Data) (i : Fin 16) :
    (cleared a).stacks (destination i)=a.stacks (destination i) := by
  change BankRoutines.clearBankStacks clearPorts a.stacks (destination i)=_
  apply BankRoutines.clearBankStacks_frame
  rw [clearPorts_mem]
  have hi := destination_outside i
  omega

theorem prepared_output (a : Data) (r : Regs) (w : Words)
    (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 16) :
    (cleared (exportState (cached a r w))).stacks (destination i)=
      if i.val < 5 then List.replicate (BinaryArithmetic.toNat (Cache.unaryWords w (localSource i))) true
      else Cache.unaryWords w (localSource i) := by
  rw [clear_output_frame,export_output _ (cached_empty a r w ho) (cached_scratch a r w ht)]
  have hc := cached_stack a r w (localSource i)
  have hsrc : (field i).src = bank (Bank.port (localSource i)) := by
    apply Fin.ext
    rfl
  simp only [payload, hsrc]
  by_cases hi : i.val < 5
  · simpa [payload,field,hi] using congrArg (fun bits => List.replicate (BinaryArithmetic.toNat bits) true) hc
  · simpa [payload,field,hi] using hc

theorem cached_small_value (m : Model) (w : Words) (hs : Shape (Interval.finalModel m) w)
    (j : Fin 64) (hj : j.val < 46) : BinaryArithmetic.toNat (Cache.unaryWords w j)=m.val j := by
  have h51 : j≠51 := by intro h; subst j; norm_num at hj
  have h52 : j≠52 := by intro h; subst j; norm_num at hj
  have h53 : j≠53 := by intro h; subst j; norm_num at hj
  simpa [Cache.unaryWords,h51,h52,h53,(intervalModel_frame m j hj).1] using hs.1 j

theorem prepared_binary_oai (a : Data) (r : Regs) (m : Model) (w : Words)
    (hs : Shape (Interval.finalModel m) w) (ho : OutputEmpty a) (ht : Scratch a) (i : Fin 8) :
    BinaryArithmetic.toNat ((cleared (exportState (cached a r w))).stacks (destination (i.natAdd 8)))=
      m.val (binarySources i) := by
  rw [prepared_output a r w ho ht]
  have hi : 8+i.val ≥ 5 := by omega
  have hj : (binarySources i).val < 46 := by fin_cases i <;> decide
  have hv := cached_small_value m w hs (binarySources i) hj
  fin_cases i <;> simpa [localSource,binarySources] using hv


end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary_oai
