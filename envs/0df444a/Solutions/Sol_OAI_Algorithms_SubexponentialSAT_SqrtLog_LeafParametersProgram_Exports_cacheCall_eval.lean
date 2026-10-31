-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cacheCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:53:06.719121+00:00
-- url     : https://prove2.me/submissions/107f63d2-ab31-4a67-b61b-0cac1aa346dc

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S169
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_Interval_at_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnaryCopy
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem unaryPorts_injective (a o : Fin 64) (hao : a≠o) :
    Function.Injective (unaryPorts a o) := by
  have hv : a.val≠o.val := fun h => hao (Fin.ext h)
  have ha := a.isLt
  have ho := o.isLt
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [unaryPorts,port,Fin.ext_iff]
  all_goals omega

/-- Preserving binary-to-unary conversion in the parameter bank. The unary
output's numeric length is explicitly charged, including the lifted return. -/
theorem unaryCopy_eval (r : Regs) (w : Words) (a o : Fin 64)
    (hao : a≠o) (ho : w o=[]) :
    ∃ t rf, Eval (unaryCopyCmd a o) t (state r w)
        (state rf (Function.update w o (List.replicate (BinaryArithmetic.toNat (w a)) true))) ∧
      t ≤ Serialization.unaryCopyBound (w a)+1 := by
  let frame := state r w
  let d := projectState unaryRegs (unaryPorts a o) frame
  have hr : Function.Injective unaryRegs := Fin.castAdd_injective _ _
  have hp := unaryPorts_injective a o hao
  have hd : d.stacks 1=[] := by simpa [d,frame,projectState,unaryPorts] using ho
  have h11 : d.stacks 11=[] := by simp [d,frame,projectState,unaryPorts,state]
  have h12 : d.stacks 12=[] := by simp [d,frame,projectState,unaryPorts,state]
  have h13 : d.stacks 13=[] := by simp [d,frame,projectState,unaryPorts,state]
  obtain ⟨t,ht,he⟩ := Serialization.unaryCopy_eval 0 1 d
    (by decide) (by decide) (by decide) (by decide) hd h11 h12 h13
  have hsrc : d.stacks 0=w a := by simp [d,frame,projectState,unaryPorts]
  let u := List.replicate (BinaryArithmetic.toNat (w a)) true
  let b := embedState unaryRegs (unaryPorts a o) frame
    (SubexpClauseMastersProgram.write d 1 u)
  have he' : Eval (unaryCopyCmd a o) (t+1) frame b := by
    apply eval_liftCommand_from_state (Serialization.unaryCopy 0 1) 0 1
      unaryRegs (unaryPorts a o) frame hr hp
    simpa only [hsrc] using he
  have hbase :
      (embedState unaryRegs (unaryPorts a o) frame
        (⟨SubexpClauseMastersProgram.zeroRegs,d.stacks⟩ : Serialization.Data)).stacks=frame.stacks := by
    change (embedState unaryRegs (unaryPorts a o) frame d).stacks=frame.stacks
    exact congrArg (fun z => z.stacks) (embedState_project unaryRegs (unaryPorts a o) frame hr hp)
  have hb : b.stacks=Function.update frame.stacks (port o) u := by
    dsimp only [b,SubexpClauseMastersProgram.write]
    rw [show (⟨SubexpClauseMastersProgram.zeroRegs,Function.update d.stacks 1 u⟩ : Serialization.Data)=
      { (⟨SubexpClauseMastersProgram.zeroRegs,d.stacks⟩ : Serialization.Data) with
        «stacks» := Function.update d.stacks 1 u } by rfl]
    rw [embedState_update_stack unaryRegs (unaryPorts a o) frame _ hp 1 u]
    exact congrArg (fun ws : Fin 77 → List Bool => Function.update ws (port o) u) hbase
  have heq : b=state b.regs (Function.update w o u) := by
    rw [← state_update r b.regs w o u]
    exact CounterForPrograms.data_ext rfl hb
  refine ⟨t+1,b.regs,?_,?_⟩
  · rw [heq] at he'
    exact he'
  · rw [hsrc] at ht
    exact Nat.add_le_add_right ht 1

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCacheWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid binary metadata for the integer entry cache. The centered interval
start on port46 is produced by `SubexpIntervalStartProgram.program`; its
semantic identification is `SubexpIntervalStart.value_eq_intervalStart`.
This stage preserves that word and the parameter table while forming Qr and
the sufficient scalar width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem admissible (m : Model) : AdmissibleCode code m := by
  simp [code,AdmissibleCode,Admissible,next,output,lengthBound]

theorem command_eval (m : Model) (w : Words) (r : Regs) (hs : Shape m w) :
    ∃ t rf w', Eval command t (Bank.state r w) (Bank.state rf w') ∧
      Shape (result code m) w' ∧ t ≤ budget code m :=
  Circuit.program_eval code m w r hs (admissible m)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth

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

theorem prepare_admissible (m : Model) : AdmissibleCode prepare m := by
  simp [prepare,AdmissibleCode,Admissible]

theorem prepare_empty (m : Model) (w : Words) (hs : Shape (result prepare m) w)
    (a : Fin 64) (ha : 46 ≤ a.val) : w a=[] := by
  have hl := hs.2 a
  fin_cases a <;> simp_all [prepare,result,next,output,lengthBound]

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

theorem command_eval (m : Model) (r : Regs) (w : Words) (hs : Shape m w)
    (hr : 0 < m.val 18) :
    ∃ t rf w', Eval command t (Bank.state r w) (Bank.state rf w') ∧
      Shape (finalModel m) w' ∧ t ≤ runtimeBound m := by
  obtain ⟨t1,r1,w1,he1,hs1,ht1⟩ := Circuit.program_eval prepare m w r hs (prepare_admissible m)
  have hval (a : Fin 64) (ha : a.val < 46) : BinaryArithmetic.toNat (w1 a)=m.val a :=
    (hs1.1 a).trans (prepare_frame m a ha).1
  have hlen (a : Fin 64) (ha : a.val < 46) : (w1 a).length ≤ m.len a :=
    (hs1.2 a).trans_eq (prepare_frame m a ha).2
  obtain ⟨t2,r2,v,he2,hv,hl,ht2⟩ := at_eval r1 w1
    (prepare_empty m w1 hs1) (by rw [hval 18 (by decide)]; exact hr)
  let w2 := Function.update w1 46 v
  have hs2 : Shape (intervalModel m) w2 := by
    constructor
    · intro a
      by_cases ha : a=46
      · subst a
        simpa [intervalModel,w2,hval 18 (by decide),hval 21 (by decide),
          hval 29 (by decide)] using hv
      · simpa [intervalModel,w2,ha] using hs1.1 a
    · intro a
      by_cases ha : a=46
      · subst a
        simp only [intervalModel,w2,Function.update_self]
        calc
          v.length ≤ 4*((w1 18).length+(w1 21).length+(w1 29).length+1) := hl
          _ ≤ 4*(m.len 18+m.len 21+m.len 29+1) := by
            gcongr <;> exact hlen _ (by decide)
      · simpa [intervalModel,w2,ha] using hs1.2 a
  obtain ⟨t3,r3,w3,he3,hs3,ht3⟩ := CacheWidth.command_eval (intervalModel m) w2 r2 hs2
  have htime : t2 ≤ 10000*(m.len 18+m.len 21+m.len 29+1)^2+1 := by
    apply ht2.trans
    gcongr <;> exact hlen _ (by decide)
  exact ⟨t1+(t2+t3),r3,w3,he1.seq (he2.seq he3),hs3,by dsimp [runtimeBound]; omega⟩

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

theorem unary_eval (m : Model) (r : Regs) (w : Words) (hs : Shape m w)
    (h51 : w 51=[]) (h52 : w 52=[]) (h53 : w 53=[]) :
    ∃ t rf, Eval unaryCommand t (Bank.state r w) (Bank.state rf (unaryWords w)) ∧
      t ≤ unaryRuntime m := by
  obtain ⟨t1,r1,he1,ht1⟩ := Bank.unaryCopy_eval r w 29 51 (by decide) h51
  let w1 := Function.update w 51 (List.replicate (BinaryArithmetic.toNat (w 29)) true)
  obtain ⟨t2,r2,he2,ht2⟩ := Bank.unaryCopy_eval r1 w1 46 52 (by decide)
    (by simpa [w1] using h52)
  let w2 := Function.update w1 52 (List.replicate (BinaryArithmetic.toNat (w 46)) true)
  have he2' : Eval (Bank.unaryCopyCmd 46 52) t2 (Bank.state r1 w1) (Bank.state r2 w2) := by
    simpa [w1,w2] using he2
  obtain ⟨t3,r3,he3,ht3⟩ := Bank.unaryCopy_eval r2 w2 50 53 (by decide)
    (by simpa [w2,w1] using h53)
  have he3' : Eval (Bank.unaryCopyCmd 50 53) t3
      (Bank.state r2 w2) (Bank.state r3 (unaryWords w)) := by
    simpa [unaryWords,w2,w1] using he3
  have hb1 := unaryCopyBound_le (w 29) (m.val 29) (m.len 29) (hs.1 29) (hs.2 29)
  have hb2 := unaryCopyBound_le (w 46) (m.val 46) (m.len 46) (hs.1 46) (hs.2 46)
  have hb3 := unaryCopyBound_le (w 50) (m.val 50) (m.len 50) (hs.1 50) (hs.2 50)
  simp only [w1,w2,Function.update_of_ne (by decide : (46 : Fin 64)≠51),
    Function.update_of_ne (by decide : (50 : Fin 64)≠51),
    Function.update_of_ne (by decide : (50 : Fin 64)≠52)] at ht2 ht3
  exact ⟨t1+(t2+t3),r3,he1.seq (he2'.seq he3'),by dsimp [unaryRuntime]; omega⟩

theorem finalModel_empty (m : Model) :
    (Interval.finalModel m).len 51=0 ∧
    (Interval.finalModel m).len 52=0 ∧
    (Interval.finalModel m).len 53=0 := by
  simp [Interval.finalModel,Interval.intervalModel,Interval.prepare,
    CacheWidth.code,result,next,output,lengthBound]

/-- Concrete binary and unary cache preparation. The binary intermediate
table is retained in every port except the three declared unary outputs. -/
theorem command_eval (m : Model) (r : Regs) (w : Words) (hs : Shape m w)
    (hr : 0 < m.val 18) :
    ∃ t rf wb, Eval command t (Bank.state r w) (Bank.state rf (unaryWords wb)) ∧
      Shape (Interval.finalModel m) wb ∧ t ≤ runtimeBound m := by
  obtain ⟨t1,r1,wb,he1,hs1,ht1⟩ := Interval.command_eval m r w hs hr
  have hz := finalModel_empty m
  have h51 : wb 51=[] := by have h := hs1.2 51; rw [hz.1] at h; simpa using h
  have h52 : wb 52=[] := by have h := hs1.2 52; rw [hz.2.1] at h; simpa using h
  have h53 : wb 53=[] := by have h := hs1.2 53; rw [hz.2.2] at h; simpa using h
  obtain ⟨t2,r2,he2,ht2⟩ := unary_eval (Interval.finalModel m) r1 wb hs1 h51 h52 h53
  exact ⟨t1+t2,r2,wb,he1.seq he2,hs1,by dsimp [runtimeBound]; omega⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache

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

theorem cacheCall_eval_oai (a : Data) (m : Model) (w : Words) (hs : Shape m w)
    (hp : projectState bankRegs bank a=Bank.state (a.regs ∘ bankRegs) w)
    (hr : 0 < m.val 18) :
    ∃ n ≤ Cache.runtimeBound m+1, ∃ rf wb,
      Eval cacheCall n a (cached a rf wb) ∧ Shape (Interval.finalModel m) wb := by
  obtain ⟨n,rf,wb,he,hshape,hn⟩ := Cache.command_eval m (a.regs ∘ bankRegs) w hs hr
  refine ⟨n+1,Nat.add_le_add_right hn 1,rf,wb,?_,hshape⟩
  exact eval_liftCommand_from_state Cache.command (Bank.port 18) (Bank.port 53) bankRegs bank a
    (Fin.castAdd_injective _ _) bank_injective (hp.symm ▸ he)

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cacheCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cacheCall_eval_oai
