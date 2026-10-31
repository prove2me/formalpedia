-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.raw_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:17:57.241483+00:00
-- url     : https://prove2.me/submissions/c55e03de-7880-47fe-9a2e-bb103b1d13ac

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S187
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutMatrixProgram_rowLoop_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_stageCost_linear

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocatable finite-bank contract for integer incidence entries, and the
fixed physical storage layout used by the direct all-row matrix builder. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem update_reversedIDs (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 282 word =
      (state base regs {q with reversedIDs:=word}).stacks := by
  funext i
  by_cases h : i=282
  · subst i; simp [state]
  · simp [state,h]

theorem update_todo (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (q : Store) (word : List Bool) :
    Function.update (state base regs q).stacks 283 word =
      (state base regs {q with todo:=word}).stacks := by
  funext i
  by_cases h : i=283
  · subst i; simp [state]
  · simp [state,h]

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid preparation of reversed original head-ID records. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem reverseRegs_injective : Function.Injective reverseRegs := Fin.castAdd_injective _ _
theorem reversePorts_injective : Function.Injective reversePorts := by decide

theorem reverseIDs_eval (base : Fin 288 → List Bool) (hb : base 285=[])
    (hb' : base 286=[]) (regs : Fin 16 → Bool) (q : Store) (js : List ℕ)
    (ht : q.todo=ids js) (hr : q.reversedIDs=[false]) :
    ∃ t ≤ 10*(ids js).length, ∃ rf, Eval reverseIDs t (state base regs q)
      (state base rf {q with todo:=[],reversedIDs:=ids js.reverse}) := by
  let records := js.map fun j => List.replicate j true
  have hproj : projectState reverseRegs reversePorts (state base regs q)=
      SubexpNormalizeProgram.filterState (regs 0) (regs 1) (regs 2)
        (Encoding.encodeList id records++[]) [] (Encoding.encodeList id []) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;>
        simp [reversePorts,state,
          SubexpPostfixControl.quadruple,records,ids,ht,hr,hb,hb',ProgramEncoding.encodeRecords,Encoding.encodeList]
  obtain ⟨t,htime,he⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] []
    (regs 0) (regs 1) (regs 2)
  rw [←hproj] at he
  have hcall := eval_call_from_state SubexpNormalizeProgram.reverseRecordsProgram reverseRegs
    reversePorts (state base regs q) reverseRegs_injective reversePorts_injective he
  let localEnd := SubexpNormalizeProgram.filterState false true false [] []
    (Encoding.encodeList id (records.reverse++[])) []
  let e := embedState reverseRegs reversePorts (state base regs q) localEnd
  have heq : e=state base e.regs {q with todo:=[],reversedIDs:=ids js.reverse} := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    by_cases hi : i ∈ Set.range reversePorts
    · obtain ⟨k,rfl⟩ := hi
      calc
        _ = localEnd.stacks k :=
          embedState_stack reverseRegs reversePorts (state base regs q) localEnd reversePorts_injective k
        _ = _ := by
          fin_cases k <;> simp [localEnd,reversePorts,SubexpNormalizeProgram.filterState,
            SubexpPostfixControl.quadruple,records,ids,hb,hb',ProgramEncoding.encodeRecords,List.map_reverse]
    · have h282 : i≠282 := fun h => hi ⟨2,by simpa [reversePorts] using h.symm⟩
      have h283 : i≠283 := fun h => hi ⟨0,by simpa [reversePorts] using h.symm⟩
      calc
        _ = (state base regs q).stacks i :=
          embedState_stack_frame reverseRegs reversePorts (state base regs q) localEnd i hi
        _ = _ := by simp [state,h282,h283]
  change Eval reverseIDs t (state base regs q) e at hcall
  rw [heq] at hcall
  exact ⟨t,htime,e.regs,hcall⟩

theorem initializeIDs_eval (base : Fin 288 → List Bool) (hb : base 285=[])
    (hb' : base 286=[]) (regs : Fin 16 → Bool) (q : Store) (js : List ℕ)
    (hi : base 17=ids js) (ht : q.todo=[]) (hr : q.reversedIDs=[]) :
    ∃ t ≤ 17*(ids js).length+7, ∃ rf, Eval initializeIDs t (state base regs q)
      (state base rf {q with todo:=[],reversedIDs:=ids js.reverse}) := by
  have hc := Subexp.TupleProgram.copy_eval (17 : Fin 288) 283 285 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  let r₁ := readRegs regs 0 1 none
  let q₁ : Store := {q with todo:=ids js}
  have hceq : (⟨r₁,StackRoutines.copyStacks 17 283 (state base regs q).stacks⟩ : Data 288)=
      state base r₁ q₁ := by
    apply congrArg (StructuredProgram.State.mk r₁)
    change Function.update (state base regs q).stacks 283
      ((state base regs q).stacks 17++(state base regs q).stacks 283)=_
    simp only [state,show (17:Fin 288)≠277 by decide,show (17:Fin 288)≠278 by decide]
    change Function.update (state base regs q).stacks 283 (base 17++q.todo)=_
    rw [hi,ht,List.append_nil,update_todo]
    rfl
  change Eval copyInputIDs _ (state base regs q)
    (⟨r₁,StackRoutines.copyStacks 17 283 (state base regs q).stacks⟩ : Data 288) at hc
  rw [hceq] at hc
  have hp := Subexp.TupleProgram.pushConst_eval (282 : Fin 288) (0 : Fin 16) false (state base r₁ q₁)
  let r₂ := Function.update r₁ 0 false
  let q₂ : Store := {q₁ with reversedIDs:=[false]}
  have hpeq : Subexp.TupleProgram.pushedState 282 0 false (state base r₁ q₁)=state base r₂ q₂ := by
    apply congrArg (StructuredProgram.State.mk r₂)
    change Function.update (state base r₁ q₁).stacks 282 (false::q.reversedIDs)=_
    rw [hr,update_reversedIDs]
    rfl
  rw [hpeq] at hp
  obtain ⟨tr,htr,rf,her⟩ := reverseIDs_eval base hb hb' r₂ q₂ js rfl rfl
  refine ⟨(7*(ids js).length+5)+(2+tr),by omega,rf,?_⟩
  simpa [initializeIDs,copyInputIDs,state,hi,q₁,q₂,r₁,r₂] using hc.seq (hp.seq her)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct all-incidence-row signed matrix construction by one fixed program.
The entry dependency is an explicit native finite-bank command contract. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem clearIDs_eval (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) :
    Eval clearIDs (2*q.reversedIDs.length+3) (state base regs q)
      (state base (readRegs regs 0 1 none) {q with reversedIDs:=[]}) := by
  have h := Subexp.TupleProgram.clear_eval (282 : Fin 288) (0 : Fin 16) 1 (state base regs q)
  convert h using 1 <;> first
    | rfl
    | exact congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
        (update_reversedIDs base regs q []).symm

theorem command_eval (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hi : base 17=ids js) (hvalid : ∀ j < D, ∀ v ∈ js, Valid j v)
    (hbound : ∀ v ∈ js, v ≤ n) (regs : Fin 16 → Bool) :
    ∃ t ≤ commandCost T B D n js, ∃ rf rows,
      Eval (command entry) t (initialState base regs D) (finalState base rf rows) ∧
      MatrixRel Rel B D js rows := by
  let q₀ : Store := {remaining:=List.replicate D true}
  obtain ⟨ti,hti,ri,hei⟩ := initializeIDs_eval base hb hb' regs q₀ js hi rfl rfl
  let q₁ : Store := {q₀ with todo:=[],reversedIDs:=ids js.reverse}
  obtain ⟨tl,htl,rl,rows,hel,hrel⟩ := rowLoop_eval entry base hb hb' Valid Rel T B hc D n js
    hvalid hbound ri q₁ rfl rfl rfl rfl rfl rfl rfl rfl
  let q₂ : Store := {q₁ with remaining:=[],matrix:=rowsWords rows++q₁.matrix}
  have hec := clearIDs_eval base rl q₂
  refine ⟨ti+(tl+(2*(ids js.reverse).length+3)),?_,readRegs rl 0 1 none,rows,?_,hrel⟩
  · simp only [ids_reverse_length] at *
    unfold commandCost
    omega
  · simpa [command,initialState,finalState,q₀,q₁,q₂] using hei.seq (hel.seq hec)

theorem program_runsIn (entry : Code 256) (base : Fin 288 → List Bool)
    (hb : base 285=[]) (hb' : base 286=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → Pair → Prop) (T B : ℕ)
    (hc : EntryContract entry base Valid Rel T B) (D n : ℕ) (js : List ℕ)
    (hi : base 17=ids js) (hvalid : ∀ j < D, ∀ v ∈ js, Valid j v)
    (hbound : ∀ v ∈ js, v ≤ n) (regs : Fin 16 → Bool) :
    ∃ rf rows,
      RunsIn (program entry) (commandCost T B D n js+1)
        ((initialState base regs D).withPC (some (program entry).entry))
        ((finalState base rf rows).withPC none) ∧ MatrixRel Rel B D js rows := by
  obtain ⟨t,ht,rf,rows,he,hr⟩ := command_eval entry base hb hb' Valid Rel T B hc D n js
    hi hvalid hbound regs
  exact ⟨rf,rows,⟨t+1,by omega,compiled_halt_trace he 281 24⟩,hr⟩

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem finish_value {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hdup : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ outputs) (hport : p.2 ∉ ports) :
    (finishState ports outputs a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ outputs, (clearManyState (outputs.map Prod.snd) a).stacks q.2 = [] := by
    intro q hq
    rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
  have hs : p.1 ∉ outputs.map Prod.snd := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    exact hsep p hp q hq he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hport,
    copyMany_value _ _ hdup hc hsep p hp, clearMany_stacks, ite_eq_right hs]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorageCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem resetMany_wordBound {S : ℕ} (rs : List (Fin 16)) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : WordBound B (resetManyState rs a) := by
  intro i
  simpa only [resetMany_stacks] using ha i

theorem beforeCopies_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (a : Data S) (B : ℕ) (ha : WordBound B a) :
    WordBound B (beforeCopies tmp ports a) :=
  resetMany_wordBound _ _ B
    (clearMany_wordBound ports _ B (clearMany_wordBound [tmp] a B ha))

theorem prepare_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (inputs.map Prod.snd).Nodup)
    (hp : ∀ p ∈ inputs, p.2 ∈ ports)
    (hsep : ∀ p ∈ inputs, ∀ q ∈ inputs, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (prepareState tmp ports inputs a) := by
  apply copyMany_wordBound inputs _ B hd _ hsep (beforeCopies_wordBound tmp ports a B ha)
  intro p hm
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_left (hp p hm)]

theorem finishCopies_wordBound {S : ℕ} (outputs : List (Fin S × Fin S))
    (a : Data S) (B : ℕ) (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) :
    WordBound B (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)) := by
  apply copyMany_wordBound outputs _ B hd _ hsep
    (clearMany_wordBound (outputs.map Prod.snd) a B ha)
  intro p hp
  rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨p, hp, rfl⟩)]

theorem finish_wordBound {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (finishState ports outputs a) :=
  resetMany_wordBound _ _ B
    (clearMany_wordBound ports _ B (finishCopies_wordBound outputs a B hd hsep ha))

theorem embedState_wordBound {r s S : ℕ} (register : Fin r → Fin 16)
    (stack : Fin s → Fin S) (frame : Data S) (out : State r s) (B : ℕ)
    (hs : Function.Injective stack) (hf : WordBound B frame) (ho : WordBound B out) :
    WordBound B (embedState register stack frame out) := by
  intro i
  by_cases hm : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hm
    rw [embedState_stack register stack frame out hs j]
    exact ho j
  · rw [embedState_stack_frame register stack frame out i hm]
    exact hf i

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem workPort_injective {s : ℕ} (hs : s ≤ 288) : Function.Injective (workPort hs) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [workPort] at this
  omega

theorem protected_ne_work {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) (j : Fin s) : i ≠ workPort hs j := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [workPort] at *
  rcases hi.1 with h | h <;> omega

theorem work_ne_temporary {s : ℕ} (hs : s ≤ 288) (i : Fin s) :
    workPort hs i ≠ temporary := by
  intro h
  have := congrArg Fin.val h
  have := i.isLt
  simp only [workPort,temporary] at *
  omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem work_mem_workPorts {s : ℕ} (hs : s ≤ 288) (j : Fin s) :
    workPort hs j ∈ workPorts hs := by
  simp only [workPorts,List.mem_ofFn]
  exact ⟨j,rfl⟩

theorem inputCopies_good {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (hi : ∀ p ∈ ins, Protected p.1) :
    ∀ p ∈ inputCopies hs ins, p.1 ≠ p.2 ∧ p.1 ≠ temporary ∧ temporary ≠ p.2 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨protected_ne_work hs (hi q hq) q.2,(hi q hq).2,(work_ne_temporary hs q.2).symm⟩

theorem outputCopies_good {s : ℕ} (hs : s ≤ 288) (outs : List (Fin s × Fin 768))
    (ho : ∀ p ∈ outs, Protected p.2) :
    ∀ p ∈ outputCopies hs outs, p.1 ≠ p.2 ∧ p.1 ≠ temporary ∧ temporary ≠ p.2 := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨(protected_ne_work hs (ho q hq) q.1).symm,work_ne_temporary hs q.1,(ho q hq).2.symm⟩

theorem prepared_word {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (hi : ∀ p ∈ ins, Protected p.1) (hd : (ins.map Prod.snd).Nodup)
    (p : Fin 768 × Fin s) (hp : p ∈ ins) :
    (prepared hs ins a).stacks (workPort hs p.2) = a.stacks p.1 := by
  have hd' : ((inputCopies hs ins).map Prod.snd).Nodup := by
    simpa only [inputCopies,List.map_map,Function.comp_def] using
      hd.map (workPort_injective hs)
  have hc : ∀ q ∈ inputCopies hs ins,
      (beforeCopies temporary (workPorts hs) a).stacks q.2 = [] := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
    simp only [beforeCopies,resetMany_stacks,clearMany_stacks,
      ite_eq_left (work_mem_workPorts hs z.2)]
  have hsep : ∀ q ∈ inputCopies hs ins, ∀ z ∈ inputCopies hs ins, q.1 ≠ z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact protected_ne_work hs (hi q' hq') z'.2
  have hv := copyMany_value (inputCopies hs ins) (beforeCopies temporary (workPorts hs) a)
    hd' hc hsep (p.1,workPort hs p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
  change (prepared hs ins a).stacks (workPort hs p.2) = _ at hv
  rw [hv]
  simp only [beforeCopies,resetMany_stacks,clearMany_stacks,
    ite_eq_right (protected_not_workPorts hs (hi p hp))]
  simp [(hi p hp).2]

theorem prepared_empty {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (j : Fin s) (hj : ∀ p ∈ ins,j ≠ p.2) :
    (prepared hs ins a).stacks (workPort hs j) = [] := by
  have hn : ∀ p ∈ inputCopies hs ins,workPort hs j ≠ p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact fun h => hj q hq (workPort_injective hs h)
  unfold prepared prepareState
  rw [copyMany_frame _ _ _ hn]
  simp only [beforeCopies,resetMany_stacks,clearMany_stacks,ite_eq_left (work_mem_workPorts hs j)]

theorem prepared_eq {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (a : Data) (b : State r s)
    (hi : ∀ p ∈ ins,Protected p.1) (hd : (ins.map Prod.snd).Nodup)
    (hr : ∀ j,(prepared hs ins a).regs (reg j)=b.regs j)
    (hw : ∀ p ∈ ins,b.stacks p.2=a.stacks p.1)
    (hz : ∀ j,(∀ p ∈ ins,j≠p.2)→b.stacks j=[]) :
    projectState reg (workPort hs) (prepared hs ins a)=b := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j; exact hr j
  · funext j
    by_cases hm : ∃ p ∈ ins,p.2=j
    · obtain ⟨p,hp,rfl⟩ := hm
      exact (prepared_word hs ins a hi hd p hp).trans (hw p hp).symm
    · have hj : ∀ p ∈ ins,j≠p.2 := by
        intro p hp h; exact hm ⟨p,hp,h.symm⟩
      exact (prepared_empty hs ins a j hj).trans (hz j hj).symm

theorem stage_eval {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 16)
    (hr : Function.Injective reg) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b c : State r s) {t : ℕ}
    (hi : ∀ q ∈ ins,Protected q.1) (ho : ∀ q ∈ outs,Protected q.2)
    (hl : projectState reg (workPort hs) (prepared hs ins a)=b)
    (ht : Trace p t (b.withPC (some p.entry)) (c.withPC none)) :
    Eval (stage p reg hs ins outs) (stageCost reg hs ins outs a c t) a
      (returned reg hs ins outs a c) := by
  apply isolated_eval p reg (workPort hs) hr (workPort_injective hs)
    temporary (workPorts hs) (inputCopies hs ins) (outputCopies hs outs) a c
    (inputCopies_good hs ins hi) (outputCopies_good hs outs ho)
  · rintro ⟨j,hj⟩; exact work_ne_temporary hs j hj
  · change Trace p t ((projectState reg (workPort hs) (prepared hs ins a)).withPC _) _
    rw [hl]
    exact ht

theorem returned_word {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (ho : ∀ q ∈ outs,Protected q.2)
    (hd : (outs.map Prod.snd).Nodup) (p : Fin s × Fin 768) (hp : p ∈ outs) :
    (returned reg hs ins outs a b).stacks p.2=b.stacks p.1 := by
  have hd' : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hd
  have hsep : ∀ q ∈ outputCopies hs outs,∀ z ∈ outputCopies hs outs,q.1≠z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact (protected_ne_work hs (ho z' hz') q'.1).symm
  exact (finish_value (workPorts hs) (outputCopies hs outs) _ hd' hsep
    (workPort hs p.1,p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
    (protected_not_workPorts hs (ho p hp))).trans
      (embedState_stack reg (workPort hs) _ b (workPort_injective hs) p.1)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorageBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Linear paid staging overhead. This bound counts the copied words and
cleared cells, including produced output streams. It adds no unit-cost data
movement to any of the native service bounds. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem inputCopies_separated {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (hi : ∀ p∈ins,Protected p.1) :
    ∀ p∈inputCopies hs ins,∀ q∈inputCopies hs ins,p.1≠q.2 := by
  intro p hp q hq
  obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
  obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
  exact protected_ne_work hs (hi p' hp') q'.2

theorem outputCopies_separated {s : ℕ} (hs : s ≤ 288) (outs : List (Fin s × Fin 768))
    (ho : ∀ p∈outs,Protected p.2) :
    ∀ p∈outputCopies hs outs,∀ q∈outputCopies hs outs,p.1≠q.2 := by
  intro p hp q hq
  obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
  obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
  exact (protected_ne_work hs (ho q' hq') p'.1).symm

theorem prepared_wordBound {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (B : ℕ) (hi : ∀ p∈ins,Protected p.1) (hd : (ins.map Prod.snd).Nodup)
    (ha : WordBound B a) : WordBound B (prepared hs ins a) := by
  apply prepare_wordBound _ _ _ _ B _ _ (inputCopies_separated hs ins hi) ha
  · simpa only [inputCopies,List.map_map,Function.comp_def] using hd.map (workPort_injective hs)
  · intro p hp
    obtain ⟨p',hp',rfl⟩ := List.mem_map.mp hp
    exact work_mem_workPorts hs p'.2

theorem returned_wordBound {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (B : ℕ)
    (hi : ∀ p∈ins,Protected p.1) (ho : ∀ p∈outs,Protected p.2)
    (hdi : (ins.map Prod.snd).Nodup) (hdo : (outs.map Prod.snd).Nodup)
    (ha : WordBound B a) (hb : WordBound B b) :
    WordBound B (returned reg hs ins outs a b) := by
  have hd : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hdo
  exact finish_wordBound _ _ _ B hd (outputCopies_separated hs outs ho)
    (embedState_wordBound reg (workPort hs) (prepared hs ins a) b B
      (workPort_injective hs) (prepared_wordBound hs ins a B hi hdi ha) hb)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem matrixInputs_protected : ∀ p∈matrixInputs,Protected p.1 := by
  simp [matrixInputs,Protected,temporary]

theorem matrix_prepared (a : Data) (D : ℕ) (hD : a.stacks 647=List.replicate D true) :
    projectState id (workPort (by decide)) (prepared (by decide) matrixInputs a)=
      LayoutMatrixProgram.initialState (matrixBase a) (prepared (by decide) matrixInputs a).regs D := by
  apply prepared_eq id (by decide) matrixInputs a _ matrixInputs_protected (by decide)
  · intro j; rfl
  · intro p hp
    simp only [matrixInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [LayoutMatrixProgram.initialState,LayoutMatrixProgram.state,matrixBase,hD]
  · intro j hj
    simp only [matrixInputs,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at hj
    rcases hj with ⟨h0,h17,h18,h23,h225,h226,h227,h228,h229,h230,h231,h232,h233,h234,h235,h236,h281⟩
    simp [LayoutMatrixProgram.initialState,LayoutMatrixProgram.state,matrixBase, *]



theorem rawOutputs_protected : ∀ p∈rawOutputs,Protected p.2 := by
  simp [rawOutputs,Protected,temporary]

/-- A local polynomial run gives a polynomial bound for every paid stage,
including input copies, dirty work-bank clearing, and output copies. -/
theorem stage_trace_bound {r q l t T A : ℕ} (p : Program r q l)
    (reg : Fin r → Fin 16) (hs : q ≤ 288)
    (ins : List (Fin 768 × Fin q)) (outs : List (Fin q × Fin 768))
    (a : Data) (b : State r q)
    (hi : ∀ v∈ins,Protected v.1) (ho : ∀ v∈outs,Protected v.2)
    (hdi : (ins.map Prod.snd).Nodup) (hdo : (outs.map Prod.snd).Nodup)
    (ha : WordBound A a) (ht : t ≤ T)
    (tr : Trace p t
      ((projectState reg (workPort hs) (prepared hs ins a)).withPC (some p.entry))
      (b.withPC none)) :
    stageCost reg hs ins outs a b t ≤ T+(6*q+7*ins.length+10*outs.length+21)*(A+T+1) ∧
    WordBound (A+T) (returned reg hs ins outs a b) := by
  have hp := prepared_wordBound hs ins a A hi hdi ha
  have hb : WordBound (A+T) b := by
    intro i
    have h := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le tr i
    change (b.stacks i).length ≤ ((prepared hs ins a).stacks (workPort hs i)).length + t at h
    exact h.trans (Nat.add_le_add (hp _) ht)
  have ha' : WordBound (A+T) a := fun i => (ha i).trans (Nat.le_add_right _ _)
  refine ⟨?_,returned_wordBound reg hs ins outs a b (A+T) hi ho hdi hdo ha' hb⟩
  exact (stageCost_linear reg hs ins outs a b t (A+T) hi ho hdi hdo ha' hb).trans
    (Nat.add_le_add_right ht _)

/-- Paid raw-matrix staging, with its exact physical output and caller frame.
The native specialization below discharges the entry contract. -/
theorem raw_eval_oai (a : Data) (D n : ℕ) (js : List ℕ)
    (hD : a.stacks 647=List.replicate D true)
    (hi : a.stacks 650=LayoutMatrixProgram.ids js)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (T B : ℕ)
    (hc : LayoutMatrixProgram.EntryContract entry (matrixBase a) Valid Rel T B)
    (hv : ∀ j<D,∀ v∈js,Valid j v) (hjs : ∀ v∈js,v ≤ n) :
    ∃ rf rows t,
      LayoutMatrixProgram.MatrixRel Rel B D js rows ∧
      t ≤ stageCost id (by decide) matrixInputs rawOutputs a
        (LayoutMatrixProgram.finalState (matrixBase a) rf rows)
        (LayoutMatrixProgram.commandCost T B D n js+1) ∧
      Eval rawCommand t a (returned id (by decide) matrixInputs rawOutputs a
        (LayoutMatrixProgram.finalState (matrixBase a) rf rows)) ∧
      (returned id (by decide) matrixInputs rawOutputs a
        (LayoutMatrixProgram.finalState (matrixBase a) rf rows)).stacks 669=
          LayoutMatrixProgram.rowsWords rows ∧
      ∀ A,WordBound A a →
        t ≤ (LayoutMatrixProgram.commandCost T B D n js+1)+
          1878*(A+(LayoutMatrixProgram.commandCost T B D n js+1)+1) ∧
        WordBound (A+(LayoutMatrixProgram.commandCost T B D n js+1))
          (returned id (by decide) matrixInputs rawOutputs a
            (LayoutMatrixProgram.finalState (matrixBase a) rf rows)) := by
  obtain ⟨rf,rows,⟨t,ht,he⟩,hr⟩ := LayoutMatrixProgram.program_runsIn entry
    (matrixBase a) (by simp [matrixBase]) (by simp [matrixBase]) Valid Rel T B hc
    D n js (by simpa [matrixBase] using hi) hv hjs
    (prepared (by decide) matrixInputs a).regs
  have hs := stage_eval (LayoutMatrixProgram.program entry) id Function.injective_id
    (by decide) matrixInputs rawOutputs a _ _ matrixInputs_protected rawOutputs_protected
    (matrix_prepared a D hD) he
  refine ⟨rf,rows,_,hr,?_,hs,?_,?_⟩
  · unfold stageCost
    omega
  · exact returned_word id (by decide) matrixInputs rawOutputs a _
      rawOutputs_protected (by decide) (24,669) (by simp [rawOutputs])
  · intro A ha
    have hex := he
    rw [←matrix_prepared a D hD] at hex
    have hb := stage_trace_bound (LayoutMatrixProgram.program entry) id
      (by decide) matrixInputs rawOutputs a _ matrixInputs_protected rawOutputs_protected
      (by decide) (by decide) ha ht hex
    simpa only [matrixInputs,rawOutputs,List.length_cons,List.length_nil] using hb

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.raw_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.raw_eval_oai
