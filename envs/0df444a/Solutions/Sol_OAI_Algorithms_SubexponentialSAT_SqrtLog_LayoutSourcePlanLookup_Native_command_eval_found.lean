-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:30:55.59811+00:00
-- url     : https://prove2.me/submissions/0fe53c33-1c00-4928-aa96-adeb4e40b5b7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S106
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourcePlanLookup_Scan_command_eval_found

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and framing adapters for direct construction of all incidence
rows. The adapters expose native instruction counts and exact stack effects. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem regs8_injective : Function.Injective regs8 := Fin.castAdd_injective _ _

theorem lift8_eval {s : ℕ} (c : Cmd 8 s) (input output : Fin s) (d : Data s)
    (t : ℕ) (e : State 8 s)
    (he : Eval c t (projectState regs8 id d) e) :
    ∃ rf, Eval (lift8 c input output) (t+1) d ⟨rf,e.stacks⟩ := by
  let z := embedState regs8 id d e
  have hs := embedState_project regs8 (id : Fin s → Fin s) d
    regs8_injective Function.injective_id
  have hz : z = ⟨z.regs,e.stacks⟩ := by
    apply congrArg (StructuredProgram.State.mk z.regs)
    funext i
    exact embedState_stack regs8 id d e Function.injective_id i
  have h := eval_call_lifted (compiled c input output) regs8 id d
    regs8_injective Function.injective_id (compiled_halt_trace he input output)
  rw [hs] at h
  change Eval (lift8 c input output) (t+1) d z at h
  rw [hz] at h
  exact ⟨z.regs,h⟩

theorem frame_eval {s : ℕ} (src dst tmp : Fin s) (hsd : src ≠ dst)
    (hst : src ≠ tmp) (htd : tmp ≠ dst) (d : Data s) (ht : d.stacks tmp=[]) :
    ∃ e, Eval (frame src dst tmp htd) (8*(d.stacks src).length+9) d e ∧
      e.stacks=Function.update (Function.update d.stacks src []) dst
        (Encoding.frame (d.stacks src)++d.stacks dst) := by
  obtain ⟨e,he,hs⟩ := Subexp.MatrixProgramSupport.emitFrame_eval src dst tmp hsd hst htd
    (projectState regs8 id d) ht
  obtain ⟨rf,hf⟩ := lift8_eval _ src dst d _ e he
  refine ⟨⟨rf,e.stacks⟩,?_,hs⟩
  convert hf using 1 ; simp [projectState]

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed twelve-stack workspace for a full pair-key lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem push_eval (dst : Fin 12) (bit : Bool) (d : Data) :
    Eval (push dst bit) 2 d
      ⟨Function.update d.regs 0 bit,Function.update d.stacks dst (bit::d.stacks dst)⟩ := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 16) bit) d)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.push dst 0)
    ((StructuredProgram.Atom.set 0 bit).eval d))
  simpa [push,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h1.seq h2

theorem clear_eval (src : Fin 12) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d
      ⟨readRegs d.regs 0 1 none,Function.update d.stacks src []⟩ := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 16) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [clear,StackRoutines.clearResult,StackRoutines.clearStacks,
    StructuredProgram.State.withPC,StackRoutines.clearProgram,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

/-- Copy and frame both runtime fields; the second is their unary concatenation. -/
theorem buildQuery_eval (regs : Fin 16 → Bool)
    (literal ambient factor master : List Bool) :
    ∃ rf, Eval buildQuery (31*(literal.length+ambient.length+factor.length)+88)
      (data regs literal ambient factor master [] [] [] [] [] [] [] [])
      (data rf literal ambient factor master [] []
        (pairKey literal (ambient++factor)) [] [] [] [] []) := by
  let r1 := readRegs regs 0 1 none
  have h1 := copy_eval (data regs literal ambient factor master [] [] [] [] [] [] [] []) 2 6 11 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have e1 : afterCopy (data regs literal ambient factor master [] [] [] [] [] [] [] []) 2 6 0 1 =
      data r1 literal ambient factor master [] [] factor [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data,afterCopy,StackRoutines.copyStacks]
  rw [e1] at h1
  let r2 := readRegs r1 0 1 none
  have h2 := copy_eval (data r1 literal ambient factor master [] [] factor [] [] [] [] []) 1 6 11 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have e2 : afterCopy (data r1 literal ambient factor master [] [] factor [] [] [] [] []) 1 6 0 1 =
      data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data,afterCopy,StackRoutines.copyStacks]
  rw [e2] at h2
  let r3 := Function.update r2 0 false
  have h3 := push_eval 5 false (data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] [])
  have e3 : (⟨Function.update (data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] []).regs 0 false,Function.update (data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] []).stacks 5
      (false::(data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] []).stacks 5)⟩ : Data) =
      data r3 literal ambient factor master [] (false::([])) (ambient++factor) [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data]
  rw [e3] at h3
  obtain ⟨out4,h4,hs4⟩ := LayoutMatrixProgram.frame_eval 6 5 7
    (by decide) (by decide) (by decide) (data r3 literal ambient factor master [] (false::([])) (ambient++factor) [] [] [] [] []) rfl
  let r4 := out4.regs
  have e4 : out4 = data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · rw [hs4]
      funext i; fin_cases i <;>
        simp [data]
  rw [e4] at h4
  let r5 := Function.update r4 0 true
  have h5 := push_eval 5 true (data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] [])
  have e5 : (⟨Function.update (data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] []).regs 0 true,Function.update (data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] []).stacks 5
      (true::(data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] []).stacks 5)⟩ : Data) =
      data r5 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data]
  rw [e5] at h5
  let r6 := readRegs r5 0 1 none
  have h6 := copy_eval (data r5 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) [] [] [] [] [] []) 0 6 11 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have e6 : afterCopy (data r5 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) [] [] [] [] [] []) 0 6 0 1 =
      data r6 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) literal [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data,afterCopy,StackRoutines.copyStacks]
  rw [e6] at h6
  obtain ⟨out7,h7,hs7⟩ := LayoutMatrixProgram.frame_eval 6 5 7
    (by decide) (by decide) (by decide) (data r6 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) literal [] [] [] [] []) rfl
  let r7 := out7.regs
  have e7 : out7 = data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · rw [hs7]
      funext i; fin_cases i <;>
        simp [data]
  rw [e7] at h7
  let r8 := Function.update r7 0 true
  have h8 := push_eval 5 true (data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] [])
  have e8 : (⟨Function.update (data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] []).regs 0 true,Function.update (data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] []).stacks 5
      (true::(data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] []).stacks 5)⟩ : Data) =
      data r8 literal ambient factor master [] (true::(Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([])))))) [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data]
  rw [e8] at h8
  obtain ⟨out9,h9,hs9⟩ := LayoutMatrixProgram.frame_eval 5 6 7
    (by decide) (by decide) (by decide) (data r8 literal ambient factor master [] (true::(Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([])))))) [] [] [] [] [] []) rfl
  let r9 := out9.regs
  have e9 : out9 = data r9 literal ambient factor master [] [] (pairKey literal (ambient++factor)) [] [] [] [] [] := by
    apply state_ext
    · rfl
    · rw [hs9]
      funext i; fin_cases i <;>
        simp [data,pairKey,ProgramEncoding.encodeRecords,Encoding.encodeList]
  rw [e9] at h9
  refine ⟨r9,?_⟩
  have hh := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))
  convert hh using 1 <;>
    simp [buildQuery,copy,data,Encoding.length_frame] ; omega

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem stack_injective : Function.Injective stack := by decide

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupFound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The same frozen pair-lookup program exposes its native found bit in register4.
No extra scan, metadata value, or runtime instruction is introduced. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Local
theorem command_eval_found (regs : Fin 16 → Bool) (literal ambient factor : List Bool)
    (nodes : List (List Bool)) :
    ∃ n ≤ budget literal ambient factor nodes, ∃ rf,
      Eval command n
        (data regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
          [] [] [] [] [] [] [] [])
        (data rf literal ambient factor (ProgramEncoding.encodeRecords nodes)
          (List.replicate (nodes.idxOf (pairKey literal (ambient++factor))) true)
          [] [] [] [] [] [] []) ∧
      rf 4=decide (pairKey literal (ambient++factor) ∈ nodes) := by
  obtain ⟨r1,h1⟩ := buildQuery_eval regs literal ambient factor (ProgramEncoding.encodeRecords nodes)
  obtain ⟨n,hn,r2,h2,hflag⟩ := Scan.command_eval_found r1 literal ambient factor
    (pairKey literal (ambient++factor)) nodes
  let q := pairKey literal (ambient++factor)
  let count := List.replicate (nodes.idxOf q) true
  let d := data r2 literal ambient factor (ProgramEncoding.encodeRecords nodes)
    count [] q [] [] [] [] []
  have h3 := clear_eval 6 d
  have he : (⟨readRegs d.regs 0 1 none,Function.update d.stacks 6 []⟩ : Data)=
      data (readRegs r2 0 1 none) literal ambient factor (ProgramEncoding.encodeRecords nodes)
        count [] [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [d,data]
  rw [he] at h3
  refine ⟨31*(literal.length+ambient.length+factor.length)+88+
    (n+(2*q.length+3)),?_,readRegs r2 0 1 none,?_,?_⟩
  · simp only [budget,q,pairKey_length,List.length_append] at *
    omega
  · exact h1.seq (h2.seq h3)

  · first | (simpa [readRegs, -OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.status_read] using hflag) | (simpa [readRegs] using hflag)

end Local

namespace Native
theorem command_eval_found_oai (d : Data) (nodes : List (List Bool))
    (hmaster : d.stacks 337=ProgramEncoding.encodeRecords nodes) (hclean : Clean d) :
    ∃ n ≤ budget d nodes, ∃ e : Data,
      Eval command n d e ∧
      e.stacks=Function.update d.stacks 304
        (List.replicate (nodes.idxOf
          (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216))) true) ∧
      e.regs 4=decide (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216) ∈ nodes) := by
  have h304 := hclean 304 (by simp)
  have h315 := hclean 315 (by simp)
  have h316 := hclean 316 (by simp)
  have h317 := hclean 317 (by simp)
  have h318 := hclean 318 (by simp)
  have h319 := hclean 319 (by simp)
  have h338 := hclean 338 (by simp)
  have h339 := hclean 339 (by simp)
  obtain ⟨n,hn,rs,he,hflag⟩ := Local.command_eval_found d.regs
    (d.stacks 233) (d.stacks 212) (d.stacks 216) nodes
  have ha : projectState id stack d =
      data d.regs (d.stacks 233) (d.stacks 212) (d.stacks 216)
        (ProgramEncoding.encodeRecords nodes) [] [] [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;>
        simp [projectState,stack,data,hmaster,h304,h315,h316,h317,h318,h319,h338,h339]
  rw [←ha] at he
  have hh := eval_liftCommand_from_state Local.command 0 4 id stack d
    Function.injective_id stack_injective he
  let count := List.replicate (nodes.idxOf
    (pairKey (d.stacks 233) (d.stacks 212++d.stacks 216))) true
  let e := embedState id stack d
    (data rs (d.stacks 233) (d.stacks 212) (d.stacks 216)
      (ProgramEncoding.encodeRecords nodes) count [] [] [] [] [] [] [])
  refine ⟨n+1,Nat.add_le_add_right hn 1,e,hh,?_,?_⟩
  · funext j
    by_cases hj : ∃ i, stack i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [show e.stacks (stack i)=_ from embedState_stack id stack d _ stack_injective i]
      fin_cases i <;>
        simp [stack,data,count,hmaster,h315,h316,h317,h318,h319,h338,h339]
    · have hj304 : j≠304 := fun h => hj ⟨4,by simpa [stack] using h.symm⟩
      rw [Function.update_of_ne hj304]
      exact embedState_stack_frame id stack d _ j hj
  · have hg : e.regs ((id : Fin 16 → Fin 16) 4)=rs 4 :=
      embedState_register id stack d _ Function.injective_id 4
    exact hg.trans hflag

end Native

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.command_eval_found_oai
