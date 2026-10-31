-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:51:49.61117+00:00
-- url     : https://prove2.me/submissions/6201a2b2-dce1-47c5-89e9-c16c071b3011

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S162
import Definitions.Def_OAIQ081S168
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_IntegerCache_program_runsIn

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The node index and palette size are runtime inputs. This fixed program
initializes the head countdown and computes the first physical color address
by real unary multiplication. Subsequent heads increment that address. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BasisTransposePlanProgram

theorem command_eval (regs : Fin 3 → Bool) (r t : ℕ) :
    ∃ n ≤ budget r t-1, ∃ rf, Eval command n (input regs r t) (result rf r t) := by
  let a := input regs r t
  let b := copied 2 5 a
  have h1 := copy_eval 2 5 a (by decide) (by decide) (by decide) rfl
  obtain ⟨n,c,h2,hn,hs⟩ := multiply_eval r t b
    (by simp [b,a,input])
    (by simp [b,a,input])
    (by simp [b,a,input])
  have hc0 : c.stacks 0=_root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary r := by simp [hs,b,a,input]
  have hc6 : c.stacks 6=[] := by simp [hs,b,a,input]
  let e := copied 0 3 c
  have h3 := copy_eval 0 3 c (by decide) (by decide) (by decide) hc6
  have he : e=result e.regs r t := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    fin_cases i <;> simp [hs,b,a,input,StackRoutines.copyStacks]
  change Eval _ _ c e at h3
  rw [he] at h3
  refine ⟨_,?_,e.regs,h1.seq (h2.seq h3)⟩
  simp [a,input,_root_.OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary,hc0]
  have hb : budget r t-1=t*(7*r+14)+7*r+12 := by unfold budget; omega
  rw [hb]
  nlinarith

theorem program_runsIn (regs : Fin 3 → Bool) (r t : ℕ) :
    ∃ rf, RunsIn program (budget r t) ((input regs r t).withPC (some program.entry))
      ((result rf r t).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval regs r t
  exact ⟨rf,n+1,by unfold budget at *; omega,compiled_halt_trace he 2 4⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Address

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

theorem prepare_frame {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (ht : i ≠ tmp) (hp : i ∉ ports) (hi : ∀ p ∈ inputs, i ≠ p.2) :
    (prepareState tmp ports inputs a).stacks i = a.stacks i := by
  unfold prepareState beforeCopies
  rw [copyMany_frame _ _ _ hi, resetMany_stacks, clearMany_stacks,
    ite_eq_right hp, clearMany_stacks]
  simp [ht]

theorem finish_frame {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hp : i ∉ ports) (ho : ∀ p ∈ outputs, i ≠ p.2) :
    (finishState ports outputs a).stacks i = a.stacks i := by
  have hmem : i ∉ outputs.map Prod.snd := by
    intro hi
    obtain ⟨p, hm, he⟩ := List.mem_map.mp hi
    exact ho p hm he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hp,
    copyMany_frame _ _ _ ho, clearMany_stacks, ite_eq_right hmem]

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

theorem prepared_frame {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (i : Fin 768) (hi : Protected i) : (prepared hs ins a).stacks i = a.stacks i := by
  apply prepare_frame _ _ _ _ _ hi.2 (protected_not_workPorts hs hi)
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact protected_ne_work hs hi q.2

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

theorem returned_frame {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hi : Protected i)
    (hn : ∀ p ∈ outs,i≠p.2) : (returned reg hs ins outs a b).stacks i=a.stacks i := by
  have hno : ∀ p ∈ outputCopies hs outs,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hn q hq
  exact (finish_frame _ _ _ _ (protected_not_workPorts hs hi) hno).trans
    ((embedState_stack_frame _ _ _ _ _ (by
      rintro ⟨j,hj⟩; exact protected_ne_work hs hi j hj.symm)).trans
      (prepared_frame hs ins a i hi))

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

open BitProgram StructuredCalls

theorem counterReg_injective : Function.Injective counterReg := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h)

theorem counterStack_injective : Function.Injective counterStack := by decide

theorem countCall_eval (records : List (List Bool)) (d : Data)
    (hi : d.stacks 14 = Encoding.encodeList id records) (ho : d.stacks 2 = []) :
    ∃ e : Data, Eval countCall (SubexpSunflowerProgram.CountRecords.loopSteps records) d e ∧
      e.stacks = Function.update (Function.update d.stacks 14 []) 2 (List.replicate records.length true) := by
  let a := counterState (d.regs 0) (d.regs 1) (Encoding.encodeList id records) []
  let b := counterState false false [] (List.replicate records.length true)
  have ha : a = projectState counterReg counterStack d := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [ counterStack, ParserProgram.pair, hi, ho]
  have ht := counter_trace records (d.regs 0) (d.regs 1)
  change Trace counterProgram _ (a.withPC _) (b.withPC _) at ht
  rw [ha] at ht
  have he := eval_call_from_state counterProgram counterReg counterStack d
    counterReg_injective counterStack_injective ht
  let e := embedState counterReg counterStack d b
  have hs (i : Fin 2) : e.stacks (counterStack i) = b.stacks i :=
    embedState_stack _ _ _ _ counterStack_injective i
  refine ⟨e, he, ?_⟩
  funext i
  by_cases h14 : i = 14
  · subst i
    simpa [b, counterState, counterStack, ParserProgram.pair] using hs 0
  by_cases h2 : i = 2
  · subst i
    simpa [b, counterState, counterStack, ParserProgram.pair] using hs 1
  · rw [embedState_stack_frame counterReg counterStack d b i (by
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [counterStack] at hj <;> simp_all)]
    simp [h14, h2]

theorem count_eval (records : List (List Bool)) (d : Data)
    (hs : d.stacks 1 = Encoding.encodeList id records)
    (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = []) (h14 : d.stacks 14 = []) :
    ∃ rf : Fin 8 → Bool,
      Eval countCommand (countBudget records) d
        ⟨rf, Function.update d.stacks 2 (List.replicate records.length true)⟩ := by
  let a := ArithmeticCalls.afterCopy 1 14 d
  have ha14 : a.stacks 14 = Encoding.encodeList id records := by
    simp [a, ArithmeticCalls.afterCopy, hs]
  have ha2 : a.stacks 2 = [] := by simpa [a, ArithmeticCalls.afterCopy] using h2
  obtain ⟨e, he, hstacks⟩ := countCall_eval records a ha14 ha2
  have heq : e.stacks = Function.update d.stacks 2 (List.replicate records.length true) := by
    rw [hstacks]
    funext i
    by_cases hi2 : i = 2
    · subst i; simp
    by_cases hi14 : i = 14
    · subst i; simp [h14]
    · simp [a, ArithmeticCalls.afterCopy, hi2, hi14]
  have heq' : e = (⟨e.regs, Function.update d.stacks 2 (List.replicate records.length true)⟩ : Data) :=
    congrArg (fun stk => (⟨e.regs, stk⟩ : Data)) heq
  have hcopy := ArithmeticCalls.copyAt_eval (1 : Fin 15) 14 5 d
    (by decide) (by decide) (by decide) h14 h5
  have hrun := hcopy.seq he
  rw [heq'] at hrun
  refine ⟨e.regs, ?_⟩
  simpa only [countCommand, countBudget, hs] using hrun

end SubexponentialSAT.SubexpScopeCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem addressInputs_protected : ∀ p∈addressInputs,Protected p.1 := by simp [addressInputs,Protected,temporary]
theorem addressOutputs_protected : ∀ p∈addressOutputs,Protected p.2 := by simp [addressOutputs,Protected,temporary]

theorem initializeAddress_eval (a : Data) (r t : ℕ)
    (hr : a.stacks 130=List.replicate r true) (ht : a.stacks 307=List.replicate t true) :
    ∃ rf n,n ≤ stageCost addressRegs (by decide) addressInputs addressOutputs a
        (Address.result rf r t) (Address.budget r t) ∧
      Eval initializeAddress n a
        (returned addressRegs (by decide) addressInputs addressOutputs a (Address.result rf r t)) := by
  let regs := (prepared (by decide) addressInputs a).regs ∘ addressRegs
  have hp : projectState addressRegs (workPort (by decide)) (prepared (by decide) addressInputs a)=
      Address.input regs r t := by
    apply prepared_eq addressRegs (by decide) addressInputs a _ addressInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [addressInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> simp [Address.input,SubexponentialSAT.Subexp.BasisTransposePlanProgram.unary,hr,ht]
    · intro j hj
      have h0 : j≠0 := hj (130,0) (by simp [addressInputs])
      have h2 : j≠2 := hj (307,2) (by simp [addressInputs])
      fin_cases j <;> simp_all [Address.input]
  obtain ⟨rf,n,hn,he⟩ := Address.program_runsIn regs r t
  have h := stage_eval Address.program addressRegs (Fin.castAdd_injective _ _) (by decide)
    addressInputs addressOutputs a _ _ addressInputs_protected addressOutputs_protected hp he
  exact ⟨rf,_,by unfold stageCost; omega,h⟩

theorem rowCountInputs_protected : ∀ p∈rowCountInputs,Protected p.1 := by simp [rowCountInputs,Protected,temporary]
theorem rowCountOutputs_protected : ∀ p∈rowCountOutputs,Protected p.2 := by simp [rowCountOutputs,Protected,temporary]

theorem countRows_eval (a : Data) (records : List (List Bool))
    (hs : a.stacks 136=SubexponentialSAT.Encoding.encodeList id records) :
    ∃ rf, Eval countRows
      (stageCost rowCountRegs (by decide) rowCountInputs rowCountOutputs a
        (rowCountState rf records (List.replicate records.length true))
        (SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1)) a
      (returned rowCountRegs (by decide) rowCountInputs rowCountOutputs a
        (rowCountState rf records (List.replicate records.length true))) := by
  let regs := (prepared (by decide) rowCountInputs a).regs ∘ rowCountRegs
  have hp : projectState rowCountRegs (workPort (by decide)) (prepared (by decide) rowCountInputs a)=
      rowCountState regs records [] := by
    apply prepared_eq rowCountRegs (by decide) rowCountInputs a _ rowCountInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [rowCountInputs,List.mem_singleton] at hp
      subst p
      simp [rowCountState,hs]
    · intro j hj
      have h1 : j≠1 := hj (136,1) (by simp [rowCountInputs])
      simp [rowCountState,h1]
  obtain ⟨rf,he⟩ := SubexponentialSAT.SubexpScopeCountSetup.count_eval records (rowCountState regs records [])
    (by simp [rowCountState]) (by simp [rowCountState]) (by simp [rowCountState])
    (by simp [rowCountState])
  have hend : (⟨rf,Function.update (rowCountState regs records []).stacks 2
      (List.replicate records.length true)⟩ : State 8 15)=
      rowCountState rf records (List.replicate records.length true) := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i
    by_cases h2 : i=2
    · subst i
      simp [rowCountState]
    · simp [rowCountState,h2]
  rw [hend] at he
  exact ⟨rf,stage_eval rowCountProgram rowCountRegs (Fin.castAdd_injective _ _) (by decide)
    rowCountInputs rowCountOutputs a _ _ rowCountInputs_protected rowCountOutputs_protected hp
      (compiled_halt_trace he 1 2)⟩

theorem cacheInputs_protected : ∀ p∈cacheInputs,Protected p.1 := by simp [cacheInputs,Protected,temporary]
theorem cacheOutputs_protected : ∀ p∈cacheOutputs,Protected p.2 := by simp [cacheOutputs,Protected,temporary]

theorem initializeCache_eval (d : Data) (a r width : List Bool)
    (ha : d.stacks 139=a) (hr : d.stacks 138=r) (hwidth : d.stacks 140=width)
    (hw : 1+2*a.length*r.length ≤ width.length) :
    ∃ rf words n,
      n ≤ stageCost cacheRegs (by decide) cacheInputs cacheOutputs d (cacheState rf a r width words)
        (cacheBound a r width) ∧
      Eval initializeCache n d
        (returned cacheRegs (by decide) cacheInputs cacheOutputs d (cacheState rf a r width words)) ∧
      words.length=r.length ∧ (∀ word∈words,word.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range r.length).map (LayoutCoefficientRecurrence.H a.length) := by
  let regs := (prepared (by decide) cacheInputs d).regs ∘ cacheRegs
  have hp : projectState cacheRegs (workPort (by decide)) (prepared (by decide) cacheInputs d)=
      LayoutProgram.IntegerCache.state regs a r width [] [] [] [] [] [] [] := by
    apply prepared_eq cacheRegs (by decide) cacheInputs d _ cacheInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [cacheInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl <;> simp [LayoutProgram.IntegerCache.state,ha,hr,hwidth]
    · intro j hj
      have h20 : j≠20 := hj (139,20) (by simp [cacheInputs])
      have h21 : j≠21 := hj (138,21) (by simp [cacheInputs])
      have h22 : j≠22 := hj (140,22) (by simp [cacheInputs])
      fin_cases j <;> simp_all [LayoutProgram.IntegerCache.state]
  obtain ⟨rf,words,⟨n,hn,he⟩,hlen,hwords,hvalues,hden⟩ := LayoutProgram.IntegerCache.program_runsIn regs a r width hw
  have h := stage_eval LayoutProgram.IntegerCache.program cacheRegs (Fin.castAdd_injective _ _)
    (by decide) cacheInputs cacheOutputs d _ _ cacheInputs_protected cacheOutputs_protected hp he
  exact ⟨rf,words,_,by unfold stageCost cacheBound cacheState; omega,h,hlen,hwords,hvalues⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact state and cost of the paid per-node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog
namespace LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem addressState_frame (a : Data) (regs : Fin 3 → Bool) (r t : ℕ) (i : Fin 768)
    (hi : Protected i) (h648 : i≠648) (h649 : i≠649) :
    (addressState a regs r t).stacks i=a.stacks i := by
  apply returned_frame addressRegs (by decide) addressInputs addressOutputs a _ i hi
  intro p hp
  simp only [addressOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  · exact h648
  · exact h649

theorem countedState_frame (a : Data) (regs : Fin 8 → Bool) (records : List (List Bool))
    (i : Fin 768) (hi : Protected i) (h647 : i≠647) :
    (countedState a regs records).stacks i=a.stacks i := by
  apply returned_frame rowCountRegs (by decide) rowCountInputs rowCountOutputs a _ i hi
  intro p hp
  simp only [rowCountOutputs,List.mem_singleton] at hp
  subst p
  exact h647

theorem boot_eval_oai (a : Data) (r t : ℕ) (records : List (List Bool))
    (height R width : List Bool)
    (hr : a.stacks 130=List.replicate r true) (ht : a.stacks 307=List.replicate t true)
    (hrecords : a.stacks 136=SubexponentialSAT.Encoding.encodeList id records)
    (hheight : a.stacks 139=height) (hR : a.stacks 138=R) (hwidth : a.stacks 140=width)
    (hw : 1+2*height.length*R.length ≤ width.length) :
    ∃ ra rd rc words steps, steps ≤ bootCost a ra rd rc r t records height R width words ∧
      Eval boot steps a (bootState a ra rd rc r t records height R width words) ∧
      words.length=R.length ∧ (∀ w∈words,w.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range R.length).map (LayoutCoefficientRecurrence.H height.length) := by
  obtain ⟨ra,ta,hta,hea⟩ := initializeAddress_eval a r t hr ht
  let b := addressState a ra r t
  obtain ⟨rd,hed⟩ := countRows_eval b records
    ((addressState_frame a ra r t 136 (by decide) (by decide) (by decide)).trans hrecords)
  let c := countedState b rd records
  have cf (i : Fin 768) (hi : Protected i) (h647 : i≠647) (h648 : i≠648) (h649 : i≠649) :
      c.stacks i=a.stacks i :=
    (countedState_frame b rd records i hi h647).trans (addressState_frame a ra r t i hi h648 h649)
  obtain ⟨rc,words,tc,htc,hec,hlen,hword,hvalue⟩ := initializeCache_eval c height R width
    ((cf 139 (by decide) (by decide) (by decide) (by decide)).trans hheight)
    ((cf 138 (by decide) (by decide) (by decide) (by decide)).trans hR)
    ((cf 140 (by decide) (by decide) (by decide) (by decide)).trans hwidth) hw
  refine ⟨ra,rd,rc,words,_,?_,hea.seq (hed.seq hec),hlen,hword,hvalue⟩
  unfold bootCost
  dsimp [b,c] at htc ⊢
  omega

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval_oai
