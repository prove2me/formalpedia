-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:23:09.860553+00:00
-- url     : https://prove2.me/submissions/acf8c9c4-737d-4d96-bbf6-a1bb39754fcd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_bootstrap_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
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

theorem protected_ne_work {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) (j : Fin s) : i ≠ workPort hs j := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [workPort] at *
  rcases hi.1 with h | h <;> omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem prepared_frame {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (i : Fin 768) (hi : Protected i) : (prepared hs ins a).stacks i = a.stacks i := by
  apply prepare_frame _ _ _ _ _ hi.2 (protected_not_workPorts hs hi)
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact protected_ne_work hs hi q.2

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRetain
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the paid interpolation cache for the later source-polynomial
worker. These three copies are charged before the private head bank is cleared. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem retainedState_frame (a : Data) (i : Fin 768)
    (h659 : i≠659) (h710 : i≠710) (h711 : i≠711) (h712 : i≠712) :
    (retainedState a).stacks i=a.stacks i := by
  rw [retainedState,copyMany_frame]
  · simp [clearMany_stacks,retainedPorts,h659]
  · simp [retainedCopies,h710,h711,h712]

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

theorem bootState_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649] : List (Fin 768))) :
    (bootState a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  rcases hne with ⟨h640,h641,h642,h643,h647,h648,h649⟩
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ i hi,
    countedState_frame _ _ _ _ hi h647,addressState_frame _ _ _ _ _ hi h648 h649]
  intro p hp
  simp only [cacheOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact h640
  · exact h641
  · exact h642
  · exact h643

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Initialization of one node's physical Cartesian head loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem nodeStart_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649,660,665,710,711,712] : List (Fin 768))) :
    (nodeStart a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  have h659 : i≠659 := hi.2
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  obtain ⟨h640,h641,h642,h643,h647,h648,h649,h660,h665,h710,h711,h712⟩ := hne
  simp only [nodeStart,tupleInitialized,Function.update_of_ne h665,Function.update_of_ne h660]
  rw [retainedState_frame _ i h659 h710 h711 h712]
  apply bootState_frame a ra rd rc r t records height R width words i hi
  simp [h640,h641,h642,h643,h647,h648,h649]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLayoutMasters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Layout/source metadata are parked outside the native arithmetic bank.
CRT and scalar arithmetic use several ports128..141 as scratch; these values
are therefore physically reloaded for each node and cleared before CRT. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem load_valid : ∀ p ∈ loadPairs, p.1 ≠ p.2 ∧ p.1 ≠ 684 ∧ (684 : Fin 768) ≠ p.2 := by
  intro p hp
  simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp
  obtain ⟨i,rfl⟩ := hp
  constructor
  · intro h; have hv := congrArg Fin.val h; change 730+i.val=128+i.val at hv; omega
  constructor
  · intro h; have hv := congrArg Fin.val h; change 730+i.val=684 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change 684=128+i.val at hv; omega

theorem load_local_eval (a : LocalData) (ht : a.stacks 684 = []) :
    Eval loadLocal (loadCost a) a (loaded a) := copyMany_eval 684 loadPairs a load_valid ht

theorem loadCost_le (a : LocalData) (B : ℕ) (h : ∀ i,(a.stacks (high i)).length ≤ B) :
    loadCost a ≤ 14*(7*B+5) := by
  apply copyManyCost_le loadPairs a B load_sep
  intro p hp
  simp only [loadPairs,List.mem_map,List.mem_finRange,true_and] at hp
  obtain ⟨i,rfl⟩ := hp
  exact h i

end SubexponentialSAT.SqrtLog.LeafProgram.LayoutMasters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid node-start loading of the parked source bank. Only the original
layout copy program is called; no head enumeration is imported or executed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open LeafProgram LeafHeadSetupProgram

theorem prepared_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound B (prepared a) := by
  intro i
  rw [prepared_stack]
  split_ifs
  · simp
  · exact ha i

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) :=
  eval_liftCommand_from_state (clearMany clearPorts) 730 128 registers id a
    (Fin.castAdd_injective _ _) Function.injective_id
    (clearMany_eval clearPorts (projectState registers id a))

theorem result_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound B (result a) := by
  intro i
  by_cases he : ∃ j : Fin 14,stackMap (LayoutMasters.low j)=i
  · obtain ⟨j,rfl⟩ := he
    rw [result_low]
    exact ha _
  by_cases hc : i ∈ clearPorts
  · rcases List.mem_append.mp hc with hc|hc
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl
      · change ((result a).stacks (stackMap 684)).length ≤ B
        rw [result_empty a 684 (by decide)]
        exact Nat.zero_le B
      · change ((result a).stacks (stackMap 660)).length ≤ B
        rw [result_empty a 660 (by decide)]
        exact Nat.zero_le B
      · change ((result a).stacks (stackMap 665)).length ≤ B
        rw [result_empty a 665 (by decide)]
        exact Nat.zero_le B
    · obtain ⟨j,hj,hij⟩ := List.mem_map.mp hc
      obtain ⟨k,_,hk⟩ := List.mem_map.mp hj
      exact False.elim (he ⟨k,hk ▸ hij⟩)
  · rw [result_frame a i hc]
    exact ha i

theorem command_eval (a : Data) : Eval command (cost a) a (result a) := by
  have hz : (source a).stacks 684=[] :=
    (prepared_stack a 684).trans (ite_eq_left (by decide))
  have hlocal := LayoutMasters.load_local_eval (LayoutMasters.project (source a)) hz
  have hload : Eval LayoutMasters.load
      (LayoutMasters.loadCost (LayoutMasters.project (source a))+1) (source a) (loaded a) :=
    eval_call_from_state (compiled LayoutMasters.loadLocal 730 128)
      LayoutMasters.registers id (source a) (Fin.castAdd_injective _ _)
      Function.injective_id (compiled_halt_trace hlocal 730 128)
  have hwide := eval_liftCommand_from_state LayoutMasters.load 730 128 id stackMap (prepared a)
    Function.injective_id (Fin.castAdd_injective _ _) hload
  simpa only [command,cost,result,Nat.add_assoc,Nat.reduceAdd] using
    (prepare_eval a).seq hwide

theorem cost_le (a : Data) (B : ℕ) (ha : WordBound B a) : cost a+1 ≤ 132*B+125 := by
  have hp := clearManyCost_le clearPorts (projectState registers id a) B ha
  have hl := LayoutMasters.loadCost_le (LayoutMasters.project (source a)) B
    (fun i => prepared_bound a B ha (stackMap (LayoutMasters.high i)))
  have hn : clearPorts.length=17 := by decide
  rw [hn] at hp
  unfold cost prepareCost
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem clearOne_eval (i : Fin 896) (a : Data) :
    Eval (clearOne i) (2 * (a.stacks i).length + 3) a (cleared i a) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 a.regs a.stacks)

theorem clearMany_eval (ps : List (Fin 896)) (a : Data) :
    Eval (clearMany ps) (clearCost ps a) a (clearedMany ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih => exact (clearOne_eval p a).seq (ih _)

theorem clearCost_le (ps : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : clearCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearCost]
  | cons p ps ih =>
      have hb : ∀ i, ((cleared p a).stacks i).length ≤ B := by
        intro i
        by_cases hi : i = p
        · subst i; simp [cleared]
        · simpa [cleared, hi] using ha i
      have ht := ih (cleared p a) hb
      have hp := ha p
      simp only [clearCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_PairNativeSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical pair traversal initialization and ambient-mask expansion. The
five low scratch ports325..329 are reclaimed before the caller returns; the
pair controller and persistent node/layout words are not scratch. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
open OAI BitProgram StructuredCalls

namespace CountFalse

theorem popped_state (regs : Fin 3 → Bool) (mask out : List Bool) :
    UnaryForPrograms.popped ports (state regs mask out) =
      state (readRegs regs 0 1 mask.head?) mask.tail out := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ports, state]

theorem body_eval (regs : Fin 3 → Bool) (mask out : List Bool) (b : Bool)
    (hbit : regs 0 = b) (hone : regs 2 = true) :
    Eval body (if b then 1 else 2) (state regs mask out)
      (state regs mask (if b then out else true :: out)) := by
  cases b with
  | true => exact .ite_true hbit (.base (.skip _))
  | false =>
      apply Eval.ite_false hbit
      convert Eval.base (StructuredProgram.Eval.atom (.push (1 : Fin 2) (2 : Fin 3))
        (state regs mask out)) using 1
      all_goals try with_reducible_and_instances rfl
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i
        fin_cases i <;> simp [state, StructuredProgram.Atom.instr, execInstr, hone]

/-- Each actual mask pop charges one constant-cost branch; the mathematical
visit list is proof data and is absent from all executable stacks. -/
theorem visits (mask out : List Bool) (regs : Fin 3 → Bool) (hone : regs 2 = true) :
    ∃ costs ticks rf, ticks ≤ 4 * mask.length + 2 ∧ rf 2 = true ∧
      UnaryForPrograms.Visits ports body costs ticks (state regs mask out)
        (state rf [] (List.replicate (mask.countP (!·)) true ++ out)) := by
  induction mask generalizing regs out with
  | nil =>
      refine ⟨[],2,readRegs regs 0 1 none,by simp,?_,?_⟩
      · simp [readRegs, hone]
      · simpa only [popped_state, List.head?_nil, List.tail_nil, List.countP_nil,
          List.replicate_zero, List.nil_append] using
          UnaryForPrograms.Visits.done (p:=ports) (body:=body) (state regs [] out) rfl
  | cons b mask ih =>
      let r := readRegs regs 0 1 (some b)
      have hr : r 2 = true := by simp [r, readRegs, hone]
      let next := if b then out else true :: out
      obtain ⟨costs,ticks,rf,ht,hf,hv⟩ := ih next r hr
      have he := body_eval r mask out b (by simp [r, readRegs]) hr
      have hstep := UnaryForPrograms.Visits.step (p:=ports) (body:=body)
        (d:=state regs (b::mask) out) (by simp [state, ports])
        (by simpa only [popped_state, List.head?_cons, List.tail_cons] using he)
        (by simp [state, ports, UnaryForPrograms.popped]) hv
      refine ⟨(if b then 1 else 2)::costs, (if b then 1 else 2)+ticks+2, rf, ?_, hf, ?_⟩
      · cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
      · have hword : List.replicate ((b::mask).countP (!·)) true ++ out =
            List.replicate (mask.countP (!·)) true ++ next := by
          cases b <;> simp [next, List.replicate_succ', List.append_assoc]
        rw [hword]
        exact hstep

theorem command_eval (mask out : List Bool) (regs : Fin 3 → Bool) :
    ∃ ticks rf, ticks ≤ 4 * mask.length + 3 ∧
      Eval command ticks (state regs mask out)
        (state rf [] (List.replicate (mask.countP (!·)) true ++ out)) := by
  let r := Function.update regs 2 true
  obtain ⟨costs,ticks,rf,ht,_,hv⟩ := visits mask out r (by simp [r])
  have hs : Eval (.base (.atom (.set (2 : Fin 3) true))) 1
      (state regs mask out) (state r mask out) := .base (.atom _ _)
  exact ⟨1+ticks,rf,by omega,hs.seq hv.eval⟩

/-- Exact unary false-count and every source-prefix bound on one fixed local
program. Its input and output words both have at most the incoming mask size. -/
theorem trace_space (mask : List Bool) (regs : Fin 3 → Bool) :
    ∃ ticks rf, ticks ≤ 4 * mask.length + 4 ∧
      Trace program ticks ((state regs mask []).withPC (some program.entry))
        ((state rf [] (List.replicate (mask.countP (!·)) true)).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ ticks →
        Trace program prefixSteps ((state regs mask []).withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 6 * mask.length + 4 := by
  obtain ⟨ticks,rf,ht,he⟩ := command_eval mask [] regs
  have htime : ticks+1 ≤ 4*mask.length+4 := by omega
  refine ⟨ticks+1,rf,htime,?_,?_⟩
  · simpa only [program, List.append_nil] using compiled_halt_trace he 0 1
  · have hi : dataBits ((state regs mask []).withPC (some program.entry)) ≤ 2*mask.length := by
      apply StreamResources.dataBits_le_mul
      intro i
      fin_cases i <;> simp [state]
    intro prefixSteps intermediate hp ht i
    have hb := StructuredSpace.local_stack_bound program hi prefixSteps intermediate
      (hp.trans htime) ht i
    omega

end CountFalse


open SubexpSetupStorage

theorem countRegister_injective : Function.Injective countRegister := Fin.castLE_injective (by decide)
theorem countStack_injective : Function.Injective countStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [countStack]

theorem countPrepared_stack (a : Data) (i : Fin 896) :
    (countPrepared a).stacks i =
      if i = 325 then a.stacks 338 else if i ∈ scratch then [] else a.stacks i := by
  simp only [countPrepared, prepareState, beforeCopies, copyManyState, copyState_stack,
    resetMany_stacks, clearMany_stacks]
  by_cases h : i = 325
  · subst i
    simp [scratch]
  · by_cases hi : i=329 <;> simp [h, hi, scratch, clearMany_stacks]

theorem countMiddle_stack (a : Data) (rf : Fin 3 → Bool) (i : Fin 896) :
    (countMiddle a rf).stacks i =
      if i = 326 then List.replicate ((a.stacks 338).countP (!·)) true
      else if i ∈ scratch then [] else a.stacks i := by
  by_cases h0 : i = 325
  · subst i
    have h := embedState_stack countRegister countStack (countPrepared a)
      (CountFalse.state rf [] (List.replicate ((a.stacks 338).countP (!·)) true))
      countStack_injective 0
    simpa [countMiddle, countStack, CountFalse.state, scratch] using h
  · by_cases h1 : i = 326
    · subst i
      have h := embedState_stack countRegister countStack (countPrepared a)
        (CountFalse.state rf [] (List.replicate ((a.stacks 338).countP (!·)) true))
        countStack_injective 1
      simpa [countMiddle, countStack, CountFalse.state] using h
    · rw [countMiddle, embedState_stack_frame, countPrepared_stack]
      · simp [h0,h1]
      · rintro ⟨j,hj⟩
        fin_cases j <;> simp [countStack] at hj <;> simp_all

theorem countResult_stack (a : Data) (rf : Fin 3 → Bool) (i : Fin 896) :
    (countResult a rf).stacks i =
      if i = 832 then List.replicate ((a.stacks 338).countP (!·)) true
      else if i ∈ scratch then [] else a.stacks i := by
  simp only [countResult, finishState, resetMany_stacks, clearMany_stacks,
    copyManyState, copyState_stack, List.map_cons, List.map_nil]
  by_cases h : i ∈ scratch
  · have hi : i ≠ 832 := by intro he; subst i; norm_num [scratch, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at h
    simp [h,hi]
  · by_cases hi : i=832
    · subst i; simp [countMiddle_stack, scratch]
    · have h326 : i ≠ 326 := by intro he; subst i; exact h (by simp [scratch])
      simp [h, hi, h326, clearMany_stacks, countMiddle_stack]

theorem countCommand_eval (a : Data) :
    ∃ ticks rf, ticks ≤ prepareCost 329 scratch [(338,325)] a +
        (4 * (a.stacks 338).length + 4 + finishCost scratch [(326,832)] (countMiddle a rf)) ∧
      Eval countCommand ticks a (countResult a rf) := by
  have hp : project countRegister countStack (countPrepared a) =
      CountFalse.state ((countPrepared a).regs ∘ countRegister) (a.stacks 338) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [Function.comp_apply, countStack, countPrepared_stack, scratch]
  obtain ⟨ticks,rf,ht,htrace,_⟩ := CountFalse.trace_space (a.stacks 338)
    ((countPrepared a).regs ∘ countRegister)
  rw [← hp] at htrace
  have he := isolated_eval CountFalse.program countRegister countStack
    countRegister_injective countStack_injective 329 scratch [(338,325)] [(326,832)] a
    (CountFalse.state rf [] (List.replicate ((a.stacks 338).countP (!·)) true))
    (by simp) (by simp) (by rintro ⟨j,hj⟩; fin_cases j <;> norm_num [countStack, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hj)
    (by simpa only [countPrepared] using htrace)
  exact ⟨_,rf,by dsimp only [countMiddle, countPrepared]; omega,he⟩

/-- This setup is polynomial local work, so charging its entire finite run is
valid for all-prefix storage. It never charges a surrounding pair traversal. -/
theorem countCommand_cost (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B)
    (rf : Fin 3 → Bool) :
    prepareCost 329 scratch [(338,325)] a +
        (4 * (a.stacks 338).length + 4 + finishCost scratch [(326,832)] (countMiddle a rf)) ≤
      100 * (B+1) := by
  have hm := hb 338
  have hc : ((a.stacks 338).countP (!·)) ≤ B := List.countP_le_length.trans hm
  have h0 := clearManyCost_le [329] a B hb
  have h1 : ∀ i, ((clearManyState [329] a).stacks i).length ≤ B := by
    intro i
    rw [clearMany_stacks]
    split <;> simp_all
  have h2 := clearManyCost_le scratch (clearManyState [329] a) B h1
  have h3 : ∀ i, ((countMiddle a rf).stacks i).length ≤ B := by
    intro i
    rw [countMiddle_stack]
    split_ifs <;> simp_all
  have h4 := clearManyCost_le [832] (countMiddle a rf) B h3
  have h5 : ∀ i,
      ((copyManyState [(326,832)] (clearManyState [832] (countMiddle a rf))).stacks i).length ≤ B := by
    intro i
    simp only [copyManyState, copyState_stack, clearMany_stacks]
    by_cases h : i=832
    · subst i
      simpa [countMiddle_stack, scratch] using hc
    · simp [h, h3, clearMany_stacks]
  have h6 := clearManyCost_le scratch
    (copyManyState [(326,832)] (clearManyState [832] (countMiddle a rf))) B h5
  simp only [prepareCost, finishCost, List.map_cons, List.map_nil,
    copyManyCost, Nat.add_zero]
  have hp : (beforeCopies 329 scratch a).stacks 338 = a.stacks 338 := by
    simp [beforeCopies, resetMany_stacks, clearMany_stacks, scratch]
  rw [hp]
  have hout : (clearManyState [832] (countMiddle a rf)).stacks 326 =
      List.replicate ((a.stacks 338).countP (!·)) true := by
    simp [clearMany_stacks, countMiddle_stack]
  rw [hout, List.length_replicate]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, one_mul] at h0 h4
  have hs : scratch.length = 5 := rfl
  rw [hs] at h2 h6
  omega



/-- The real descending high mask has exactly one false bit per residual
coordinate, including both empty-coordinate edge cases. -/
theorem false_count_highMask {n : ℕ} (H : Finset (Fin n)) :
    (HighIncidenceProgram.descendingHighMask H).countP (!·) = n-H.card := by
  rw [HighIncidenceProgram.descendingHighMask, List.countP_map]
  have hp : (fun v : Fin n => !(decide (v ∈ H))) = (fun v => decide (v ∉ H)) := by
    funext v
    simp
  change (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates n).countP (fun v => !(decide (v ∈ H))) = _
  rw [hp]
  change ((List.finRange n).reverse).countP (fun v => decide (v ∉ H)) = _
  rw [List.countP_reverse, List.countP_eq_length_filter]
  exact HighIncidenceProgram.freeCoordinates_length H

theorem setupResult_stack (a : Data) (rf : Fin 3 → Bool) (i : Fin 896) :
    (setupResult a rf).stacks i =
      if i=832 then List.replicate ((a.stacks 338).countP (!·)) true
      else if i=833 then a.stacks 243
      else if i ∈ scratch ∨ i=834 ∨ i=835 then [] else a.stacks i := by
  simp only [setupResult, copyState_stack, clearMany_stacks]
  by_cases h833 : i=833
  · subst i
    simp [countResult_stack, scratch]
  · simp [h833, clearMany_stacks, countResult_stack, scratch]
    split_ifs <;> simp_all

theorem setupCommand_eval (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ ticks rf, ticks ≤ 120*(B+1) ∧ Eval setupCommand ticks a (setupResult a rf) := by
  obtain ⟨ticks,rf,ht,he⟩ := countCommand_eval a
  have ht' := ht.trans (countCommand_cost a B hb rf)
  have hm : ((a.stacks 338).countP (!·)) ≤ B := List.countP_le_length.trans (hb 338)
  have hc : ∀ i, ((countResult a rf).stacks i).length ≤ B := by
    intro i
    rw [countResult_stack]
    split_ifs <;> simp_all
  have hclear := clearMany_eval [833,834,835] (countResult a rf)
  have hcost := clearManyCost_le [833,834,835] (countResult a rf) B hc
  have htmp : (clearManyState [833,834,835] (countResult a rf)).stacks 329 = [] := by
    simp [clearMany_stacks, countResult_stack, scratch]
  have hcopy := copy_eval (243:Fin 896) 833 329
    (clearManyState [833,834,835] (countResult a rf)) (by decide) (by decide) (by decide) htmp
  have hsrc : (clearManyState [833,834,835] (countResult a rf)).stacks 243 = a.stacks 243 := by
    simp [clearMany_stacks, countResult_stack, scratch]
  refine ⟨_,rf,?_,he.seq (hclear.seq hcopy)⟩
  rw [hsrc]
  have hj := hb 243
  simp only [List.length_cons, List.length_nil] at hcost
  omega

/-- Both pair controllers are initialized by executed scans/copies. All
persistent caller ports outside the finite written set are preserved. -/
theorem setup_resources {n : ℕ} (a : Data) (H : Finset (Fin n)) (J B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (hj : a.stacks 243 = List.replicate J true)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : Data), ticks ≤ 120*(B+1)+1 ∧
      Trace (compiled setupCommand 338 832) ticks
        (a.withPC (some (compiled setupCommand 338 832).entry)) (b.withPC none) ∧
      b.stacks 832 = List.replicate (n-H.card) true ∧
      b.stacks 833 = List.replicate J true ∧ b.stacks 834 = [] ∧ b.stacks 835 = [] ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠832 → i≠833 → i≠834 → i≠835 → b.stacks i = a.stacks i) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ ticks →
        Trace (compiled setupCommand 338 832) prefixSteps
          (a.withPC (some (compiled setupCommand 338 832).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896*B+120*(B+1)+1 := by
  obtain ⟨ticks,rf,ht,he⟩ := setupCommand_eval a B hb
  refine ⟨ticks+1,setupResult a rf,by omega,compiled_halt_trace he 338 832,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setupResult_stack,hm,false_count_highMask]
  · simp [setupResult_stack,hj]
  · simp [setupResult_stack]
  · simp [setupResult_stack]
  · intro i hi
    have h832 : i≠832 := by intro h; subst i; norm_num [scratch, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi
    have h833 : i≠833 := by intro h; subst i; norm_num [scratch, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi
    simp [setupResult_stack,h832,h833,hi]
  · intro i hi h832 h833 h834 h835
    simp [setupResult_stack,hi,h832,h833,h834,h835]
  · have hmass : dataBits (a.withPC (some (compiled setupCommand 338 832).entry)) ≤ 896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro prefixSteps intermediate hp htrace i
    have hbound := StructuredSpace.local_stack_bound (compiled setupCommand 338 832)
      hmass prefixSteps intermediate (hp.trans (show ticks+1 ≤120*(B+1)+1 by omega)) htrace i
    omega



theorem callerRegister_injective : Function.Injective callerRegister := Fin.castLE_injective (by decide)

/-- The real shared-ABI setup call, ready for structured-command sequencing.
The boundary word bound is preserved even though all internal prefixes are charged. -/
theorem setupCaller_eval {n : ℕ} (a : CallerData) (H : Finset (Fin n)) (J B : ℕ)
    (hm : a.stacks 338 = HighIncidenceProgram.descendingHighMask H)
    (hj : a.stacks 243 = List.replicate J true)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (ticks : ℕ) (b : CallerData), ticks ≤ 120*(B+1)+1 ∧ Eval setupCaller ticks a b ∧
      b.stacks 832 = List.replicate (n-H.card) true ∧
      b.stacks 833 = List.replicate J true ∧ b.stacks 834 = [] ∧ b.stacks 835 = [] ∧
      (∀ i ∈ scratch, b.stacks i = []) ∧
      (∀ i, i ∉ scratch → i≠832 → i≠833 → i≠834 → i≠835 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) := by
  obtain ⟨ticks,b,ht,htrace,h832,h833,h834,h835,hs,hframe,_⟩ :=
    setup_resources (projectState callerRegister id a) H J B hm hj hb
  have he := eval_call_from_state (compiled setupCommand 338 832) callerRegister id a
    callerRegister_injective Function.injective_id htrace
  let out := embedState callerRegister id a b
  have hout : ∀ i, out.stacks i=b.stacks i := fun i =>
    embedState_stack callerRegister id a b Function.injective_id i
  refine ⟨ticks,out,ht,he,(hout 832).trans h832,(hout 833).trans h833,
    (hout 834).trans h834,(hout 835).trans h835,
    fun i hi => (hout i).trans (hs i hi),
    fun i hi h832 h833 h834 h835 => (hout i).trans (hframe i hi h832 h833 h834 h835),?_⟩
  have hn : n≤B := by
    have h:=hb 338
    simpa [hm,HighIncidenceProgram.descendingHighMask,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates] using h
  have hJ : J≤B := by simpa [hj] using hb 243
  intro i
  rw [hout]
  by_cases h832' : i=832
  · subst i; rw [h832,List.length_replicate]; exact (Nat.sub_le _ _).trans hn
  · by_cases h833' : i=833
    · subst i; simpa [h833] using hJ
    · by_cases h834' : i=834
      · subst i; simp [h834]
      · by_cases h835' : i=835
        · subst i; simp [h835]
        · by_cases hi : i∈scratch
          · simp [hs i hi]
          · rw [hframe i hi h832' h833' h834' h835']
            exact hb i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed indexed traversal of the actual framed node table. The installed
worker is a real command; its measured, frame-preserving execution remains an
explicit producer obligation. Neither the index nor a jet is semantic advice. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem transfer_store (regs : Fin 40 → Bool) (a b : Store) (src dst : Fin 768)
    (hsd : src ≠ dst) (hout : transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3*(tapes a src).length+3) (state regs a)
      (state (readRegs regs 0 1 none) b) := by
  have he := ListRegisterProgram.transfer_run src dst (0 : Fin 40) 1 hsd (by decide) regs (tapes a)
  apply Eval.call
  simpa only [state,ListRegisterProgram.Run,StructuredProgram.State.withPC,hout] using he

theorem parserRegs_self (regs : Fin 40 → Bool) :
    parserRegs regs (regs 37) (regs 38) (regs 39) = regs := by
  funext i
  by_cases h13 : i = 37 <;> by_cases h14 : i = 38 <;> by_cases h15 : i = 39 <;>
    simp [parserRegs,h13,h14,h15]

theorem record_state (regs : Fin 40 → Bool) (s : Store)
    (v pr f : Bool) (src out : List Bool) :
    RecordPrograms.state ports (state regs s) v pr f src out =
      state (parserRegs regs v pr f) {s with source := src,payload := out} := by
  simp only [RecordPrograms.state,ports,state,parserRegs,update_source,update_payload]

theorem reader_store (regs : Fin 40 → Bool) (s : Store) (bits tail : List Bool)
    (hs : s.source = Encoding.frame bits ++ tail) (hp : s.payload = []) :
    Eval reader (6*bits.length+4) (state regs s)
      (state (parserRegs regs false true (regs 39))
        {s with source := tail,payload := bits.reverse}) := by
  have he := RecordPrograms.reader_eval ports (state regs s) bits tail []
    (regs 37) (regs 38) (regs 39)
  rw [record_state,record_state,parserRegs_self] at he
  have hin : {s with source := Encoding.frame bits ++ tail,payload := []} = s := by
    rw [← hs,← hp]
  simpa only [reader,hin,List.append_nil] using he

theorem pop_store (regs : Fin 40 → Bool) (s : Store) (b : Bool) (tail : List Bool)
    (hs : s.source = b :: tail) :
    Eval pop 1 (state regs s)
      (state (parserRegs regs b true (regs 39)) {s with source := tail}) := by
  have he := RecordPrograms.pop_eval ports (state regs s) (regs 37) (regs 38) (regs 39)
    b tail s.payload
  rw [record_state,record_state,parserRegs_self] at he
  simpa [pop,ports,← hs] using he

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_RingNodeSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid traversal of the actual framed node table. The remaining cursor and
unary index are physical stacks, and the decoded node is transferred to the
original factor port. No list of semantic nodes is manufactured by the machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

theorem readNode_eval (regs : Fin 40 → Bool) (s : Store)
    (bits : List Bool) (tail : List (List Bool))
    (hs : s.source = Encoding.encodeList id (bits :: tail))
    (hp : s.payload = []) (hn : s.node = []) :
    Eval readNode (9*bits.length+8) (state regs s)
      (state (nodeRegs regs) (nodeRead s bits tail)) := by
  let a := {s with source := Encoding.frame bits ++ Encoding.encodeList id tail}
  let b := {s with source := Encoding.encodeList id tail, payload := bits.reverse}
  let r1 := parserRegs regs true true (regs 39)
  let r2 := parserRegs regs false true (regs 39)
  have h1 := pop_store regs s true a.source (by simpa [Encoding.encodeList, a] using hs)
  have h2 := reader_store r1 a bits (Encoding.encodeList id tail) rfl hp
  have hr : parserRegs r1 false true (r1 39) = r2 := by
    funext i
    by_cases h37 : i = 37 <;> by_cases h38 : i = 38 <;> by_cases h39 : i = 39 <;>
      simp [r1, r2, parserRegs, h37, h38, h39]
  have h3 := transfer_store r2 b (nodeRead s bits tail) 302 78 (by decide)
    (by simp [transferStacks, b, nodeRead, hn])
  rw [hr] at h2
  convert h1.seq (h2.seq h3) using 1
  · simp [readNode]
  · simp [b, tapes]
    omega
  · simp [r2, nodeRegs]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAssembler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/
namespace Nodes

theorem call_eval (c : Cmd 40 768) (a : Data) (b : LowData) (steps : ℕ)
    (he : Eval c steps (low a) b) :
    Eval (call c) (steps+1) a (installed a b) :=
  eval_liftCommand_from_state c 301 78 id lowPort a Function.injective_id
    (Fin.castAdd_injective 768 128) he

theorem beginNode_eval (a : Data) (bits : List Bool) (tail : List (List Bool))
    (hc : a.stacks 301=Encoding.encodeList id (bits::tail)) :
    Eval beginNode (beginNodeCost a bits) a (begunNode a bits tail) := by
  let c := low (clearedNode a)
  have hsource : (RingNodeSetup.storeOf c).source=Encoding.encodeList id (bits::tail) := by
    simpa [c,RingNodeSetup.storeOf,low,projectState,lowPort,clearedNode,
      NodeReadoutSpace.clearedMany_stack,nodeResetPorts] using hc
  have hp : (RingNodeSetup.storeOf c).payload=[] := by
    simp [c,RingNodeSetup.storeOf,low,projectState,lowPort,clearedNode,
      NodeReadoutSpace.clearedMany_stack,nodeResetPorts]
  have hn : (RingNodeSetup.storeOf c).node=[] := by
    simp [c,RingNodeSetup.storeOf,low,projectState,lowPort,clearedNode,
      NodeReadoutSpace.clearedMany_stack,nodeResetPorts]
  have hr := RingNodeSetup.readNode_eval c.regs (RingNodeSetup.storeOf c) bits tail hsource hp hn
  rw [RingNodeSetup.state_storeOf] at hr
  have he := (NodeReadoutSpace.clearMany_eval nodeResetPorts a).seq
    (call_eval _ (clearedNode a) (readLow a bits tail) _ hr)
  convert he using 1
  · rfl
  · unfold beginNodeCost
    omega
  · rfl



theorem installed_at (a : Data) (b : LowData) (i : Fin 896) (hi : i.val<768) :
    (installed a b).stacks i=b.stacks ⟨i.val,hi⟩ := by
  have hh : lowPort ⟨i.val,hi⟩=i := Fin.ext rfl
  simpa only [hh] using installed_low a b ⟨i.val,hi⟩

theorem readLow_stacks (a : Data) (bits : List Bool) (tail : List (List Bool)) (i : Fin 768) :
    (readLow a bits tail).stacks i=
      if i=301 then Encoding.encodeList id tail else if i=302 then [] else
        if i=78 then bits else (low (clearedNode a)).stacks i := by
  by_cases h301 : i=301
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  by_cases h302 : i=302
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  by_cases h78 : i=78
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  simp only [h301,h302,h78,ite_false]
  exact readLow_frame a bits tail i h301 h302 h78

theorem begunNode_stacks (a : Data) (bits : List Bool) (tail : List (List Bool)) (i : Fin 896) :
    (begunNode a bits tail).stacks i=
      if i=301 then Encoding.encodeList id tail else if i=78 then bits else
        if i∈nodeResetPorts then [] else a.stacks i := by
  by_cases hlo : i.val<768
  · let j : Fin 768 := ⟨i.val,hlo⟩
    have hj : lowPort j=i := Fin.ext rfl
    have h301 : (j=301) ↔ (i=301) := by simp [j,Fin.ext_iff]
    have h302 : (j=302) ↔ (i=302) := by simp [j,Fin.ext_iff]
    have h78 : (j=78) ↔ (i=78) := by simp [j,Fin.ext_iff]
    rw [begunNode,installed_at _ _ i hlo]
    change (readLow a bits tail).stacks j=_
    rw [readLow_stacks]
    simp only [h301,h302,h78]
    change (if i=301 then Encoding.encodeList id tail else if i=302 then [] else
      if i=78 then bits else (clearedNode a).stacks (lowPort j))=_
    rw [hj,clearedNode,NodeReadoutSpace.clearedMany_stack]
    by_cases h : i=302
    · simp [h,nodeResetPorts]
    · simp only [h,ite_false]
  · have hh := installed_high (clearedNode a) (readLow a bits tail) i (by omega)
    rw [begunNode,hh,clearedNode,NodeReadoutSpace.clearedMany_stack]
    have h301 : i≠301 := by intro h; subst i; exact hlo (by decide)
    have h78 : i≠78 := by intro h; subst i; exact hlo (by decide)
    simp [h301,h78]

theorem begunNode_bound (a : Data) (bits : List Bool) (tail : List (List Bool)) (B : ℕ)
    (hb : ∀ i,(a.stacks i).length ≤ B) (hbits : bits.length ≤ B)
    (htail : (Encoding.encodeList id tail).length ≤ B) :
    ∀ i,((begunNode a bits tail).stacks i).length ≤ B := by
  intro i
  rw [begunNode_stacks]
  split_ifs
  · exact htail
  · exact hbits
  · exact Nat.zero_le _
  · exact hb i

theorem beginNodeCost_le (a : Data) (bits : List Bool) (B : ℕ)
    (hb : ∀ i,(a.stacks i).length ≤ B) (hbits : bits.length ≤ B) :
    beginNodeCost a bits ≤ 27*B+36 := by
  have hc := NodeReadoutSpace.clearCost_le nodeResetPorts a B hb
  have hl : nodeResetPorts.length=9 := rfl
  rw [hl] at hc
  unfold beginNodeCost
  omega


end Nodes


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native entry cache is the actual output of the paid node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open RowSelectionProgram

theorem start_low (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 768) (hi : i.val < 340) : (start s a ra rd rc words).stacks i=a.stacks i := by
  apply nodeStart_frame
  · constructor
    · left; exact hi
    · intro h; have hh := congrArg Fin.val h; simp [temporary] at hh; omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem bootstrapResult_markers (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    (bootstrapResult s a ra rd rc words).stacks 660=a.stacks 660 ∧
      (bootstrapResult s a ra rd rc words).stacks 665=a.stacks 665 := by
  constructor
  · rw [bootstrapResult,retainedState_frame _ 660 (by decide) (by decide) (by decide) (by decide)]
    exact bootState_frame a ra rd rc s.r s.node.val s.records s.height (unary s.R)
      s.width words 660 (by decide) (by decide)
  · rw [bootstrapResult,retainedState_frame _ 665 (by decide) (by decide) (by decide) (by decide)]
    exact bootState_frame a ra rd rc s.r s.node.val s.records s.height (unary s.R)
      s.width words 665 (by decide) (by decide)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource
open LeafHeadSetupProgram QueryTupleState
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The cache bootstrap preserves the live source bank exactly. -/
theorem bootstrap_low (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 768) (hi : i.val < 340) :
    (SignatureHeadLoader.bootstrapResult s a ra rd rc words).stacks i = a.stacks i := by
  have hn660 : i ≠ 660 := by intro h; subst i; norm_num at hi
  have hn665 : i ≠ 665 := by intro h; subst i; norm_num at hi
  have he : (SignatureHeadLoader.bootstrapResult s a ra rd rc words).stacks i =
      (Native.start s a ra rd rc words).stacks i := by
    simp only [SignatureHeadLoader.bootstrapResult, Native.start, nodeStart,
      tupleInitialized, Function.update_of_ne hn660, Function.update_of_ne hn665]
  exact he.trans (Native.start_low s a ra rd rc words i hi)

/-- Generated cache bytes and the live master words belong to the same
actual bootstrap endpoint; the old tuple initializer is not invoked. -/
theorem bootstrap_ready (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (ha : Native.Ready s a) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool)
    (words : List (List Bool)) :
    Native.Ready s (SignatureHeadLoader.bootstrapResult s a ra rd rc words) := by
  have hf := bootstrap_low s a ra rd rc words
  obtain ⟨h660,h665⟩ := SignatureHeadLoader.bootstrapResult_markers s a ra rd rc words
  exact ⟨(hf 128 (by decide)).trans ha.ambient,
    (hf 129 (by decide)).trans ha.factors,(hf 130 (by decide)).trans ha.colors,
    (hf 131 (by decide)).trans ha.nodes,(hf 132 (by decide)).trans ha.wordWidth,
    (hf 133 (by decide)).trans ha.words,(hf 134 (by decide)).trans ha.low,
    (hf 135 (by decide)).trans ha.metadata,(hf 136 (by decide)).trans ha.plans,
    (hf 138 (by decide)).trans ha.order,(hf 139 (by decide)).trans ha.height,
    (hf 140 (by decide)).trans ha.width,
    (congrArg BinaryArithmetic.toNat (hf 141 (by decide))).trans ha.offset,
    (hf 307 (by decide)).trans ha.node,h660.trans ha.tuples,h665.trans ha.marker⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

/-- The paid reset, rather than an entry assumption, empties the node sum and caches. -/
theorem loadedNode_empty (a : Data) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 896) (hi : i ∈ ([710,711,712,850,851] : List (Fin 896))) :
    (loadedNode a bits tail).stacks i=[] := by
  have hn : i ∉ NativeLayoutLoad.clearPorts := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
  rw [loadedNode,NativeLayoutLoad.result_frame _ i hn,
    QueryAssembler.Nodes.begunNode_stacks]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;> simp [QueryAssembler.Nodes.nodeResetPorts]

theorem bootstrapped_low (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (i : Fin 768) :
    (bootstrapped s a ra rd rc words).stacks (QueryAssembler.Nodes.lowPort i)=
      (SignatureHeadLoader.bootstrapResult s
        (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a) ra rd rc words).stacks i :=
  embedState_stack _ _ _ _ (Fin.castAdd_injective 768 128) i

theorem bootstrapped_high (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 896) (hi : 768 ≤ i.val) :
    (bootstrapped s a ra rd rc words).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

theorem bootstrapped_ready (s : Native.Inputs) (a : Data)
    (ha : Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a))
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort
      (bootstrapped s a ra rd rc words)) := by
  rw [bootstrapped,projectState_embed SignatureHeadLoader.leafRegs
    QueryAssembler.Nodes.lowPort _ _ SignatureHeadLoader.leafRegs.injective
    (Fin.castAdd_injective 768 128)]
  exact QueryReadyConstruction.bootstrap_ready s _ ha ra rd rc words

/-- The bootstrap touches neither the low query data nor the retained upper
masters outside its three deliberately replaced cache words. -/
theorem bootstrapped_frame (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 896) (hi : i.val<340 ∨ 700 ≤ i.val)
    (h710 : i ≠ 710) (h711 : i ≠ 711) (h712 : i ≠ 712) :
    (bootstrapped s a ra rd rc words).stacks i=a.stacks i := by
  by_cases hlo : i.val<768
  · let j : Fin 768 := ⟨i.val,hlo⟩
    have hj : QueryAssembler.Nodes.lowPort j=i := Fin.ext rfl
    rw [←hj,bootstrapped_low]
    rcases hi with hi|hi
    · exact QueryReadyConstruction.bootstrap_low s _ ra rd rc words j hi
    · have hj710 : j ≠ 710 := fun h => h710 (hj.symm.trans (congrArg QueryAssembler.Nodes.lowPort h))
      have hj711 : j ≠ 711 := fun h => h711 (hj.symm.trans (congrArg QueryAssembler.Nodes.lowPort h))
      have hj712 : j ≠ 712 := fun h => h712 (hj.symm.trans (congrArg QueryAssembler.Nodes.lowPort h))
      have hj659 : j ≠ 659 := by intro h; have hh:=congrArg Fin.val h; change i.val=659 at hh; omega
      rw [SignatureHeadLoader.bootstrapResult,retainedState_frame _ j hj659 hj710 hj711 hj712]
      apply bootState_frame
      · exact ⟨Or.inr (by change 700 ≤ j.val at hi; omega),by
          intro h; have hh:=congrArg Fin.val h; change i.val=659 at hh; omega⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false]
        intro h
        rcases h with h|h|h|h|h|h|h
        all_goals have hh:=congrArg Fin.val h
        all_goals simp only [Fin.coe_ofNat_eq_mod,Nat.reduceMod] at hh
        all_goals change 700 ≤ j.val at hi
        all_goals omega
  · exact bootstrapped_high s a ra rd rc words i (by omega)

theorem bootstrapped_framePorts (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 896) (hi : i ∈ framePorts) :
    (bootstrapped s a ra rd rc words).stacks i=a.stacks i := by
  have hp : (i.val<340 ∨ 700 ≤ i.val) ∧ i ≠ 710 ∧ i ≠ 711 ∧ i ≠ 712 := by
    simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact bootstrapped_frame s a ra rd rc words i hp.1 hp.2.1 hp.2.2.1 hp.2.2.2

/-- The native readiness fields are all disjoint from pair initialization. -/
theorem ready_after_setup (s : Native.Inputs) (a b : Data)
    (h : Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a))
    (hf : ∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
      b.stacks i=a.stacks i) :
    Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort b) := by
  have hl (i : Fin 768) (hi : i ∈ ([128,129,130,131,132,133,134,135,136,138,139,140,141,307,660,665] : List (Fin 768))) :
      b.stacks (QueryAssembler.Nodes.lowPort i)=a.stacks (QueryAssembler.Nodes.lowPort i) := by
    apply hf
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    all_goals rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact ⟨(hl 128 (by decide)).trans h.ambient,(hl 129 (by decide)).trans h.factors,
    (hl 130 (by decide)).trans h.colors,(hl 131 (by decide)).trans h.nodes,
    (hl 132 (by decide)).trans h.wordWidth,(hl 133 (by decide)).trans h.words,
    (hl 134 (by decide)).trans h.low,(hl 135 (by decide)).trans h.metadata,
    (hl 136 (by decide)).trans h.plans,(hl 138 (by decide)).trans h.order,
    (hl 139 (by decide)).trans h.height,(hl 140 (by decide)).trans h.width,
    (congrArg BinaryArithmetic.toNat (hl 141 (by decide))).trans h.offset,
    (hl 307 (by decide)).trans h.node,(hl 660 (by decide)).trans h.tuples,
    (hl 665 (by decide)).trans h.marker⟩

/-- No successful layout or executable callback is assumed here: the parked
words determine native readiness, and the fixed prefix executes every read,
clear, copy and bootstrap before constructing the pair controllers. -/
theorem prepare_eval_oai (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool))
    (H : Finset (Fin s.n)) (J B : ℕ)
    (hsource : NativeLayoutLoad.SourceBank s a)
    (hcursor : a.stacks 301=Encoding.encodeList id (bits::tail))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (horder : a.stacks 243=List.replicate J true)
    (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B) :
    ∃ ra rd rc words ticks b,
      CacheCorrect s.height (unary s.R) s.width words ∧
      Eval prepareNode ticks a b ∧ ticks ≤ 20000*(B+1)^4+300*(B+1) ∧
      WordBound B b ∧
      Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort b) ∧
      b.stacks 832=List.replicate (s.n-H.card) true ∧ b.stacks 833=List.replicate J true ∧
      b.stacks 834=[] ∧ b.stacks 835=[] ∧ b.stacks 850=[] ∧ b.stacks 851=[] ∧
      (∀ i ∈ PairNativeSetup.scratch,b.stacks i=[]) ∧
      (∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
        b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) ∧
      Trace (compiled prepareNode 301 832) (ticks+1)
        (a.withPC (some (compiled prepareNode 301 832).entry)) (b.withPC none) ∧
      ∀ k z,k ≤ ticks+1 → Trace (compiled prepareNode 301 832) k
        (a.withPC (some (compiled prepareNode 301 832).entry)) z →
        ∀ i,(z.stacks i).length ≤ 896*B+20000*(B+1)^4+300*(B+1)+1 := by
  have hencoded := hb 301
  rw [hcursor,Encoding.length_encodeList_cons] at hencoded
  have hbits : bits.length ≤ B := by simp only [id_eq] at hencoded; omega
  have htail : (Encoding.encodeList id tail).length ≤ B := by omega
  have hbegun := QueryAssembler.Nodes.begunNode_bound a bits tail B hb hbits htail
  have hloaded : WordBound B (loadedNode a bits tail) := NativeLayoutLoad.result_bound _ B hbegun
  have hready := loadedNode_ready s a bits tail hsource
  obtain ⟨ra,rd,rc,words,tboot,hw,htboot,hboot,hBboot⟩ := bootstrap_run s _ B hready hloaded hcap
    (loadedNode_empty a bits tail 710 (by decide))
    (loadedNode_empty a bits tail 711 (by decide))
    (loadedNode_empty a bits tail 712 (by decide))
  let c := bootstrapped s (loadedNode a bits tail) ra rd rc words
  have hc_frame (i : Fin 896) (hi : i ∈ framePorts) : c.stacks i=a.stacks i :=
    (bootstrapped_framePorts s _ ra rd rc words i hi).trans (loadedNode_frame a bits tail i hi)
  obtain ⟨tsetup,b,htsetup,hsetup,h832,h833,h834,h835,hscratch,hframe,hB⟩ :=
    PairNativeSetup.setupCaller_eval c H J B
      ((hc_frame 338 (by decide)).trans hmask) ((hc_frame 243 (by decide)).trans horder) hBboot
  have htime1 := QueryAssembler.Nodes.beginNodeCost_le a bits B hb hbits
  have htime2 := NativeLayoutLoad.cost_le (QueryAssembler.Nodes.begunNode a bits tail) B hbegun
  have he : Eval prepareNode
      (QueryAssembler.Nodes.beginNodeCost a bits+
        (NativeLayoutLoad.cost (QueryAssembler.Nodes.begunNode a bits tail)+(tboot+tsetup))) a b :=
    (QueryAssembler.Nodes.beginNode_eval a bits tail hcursor).seq
      ((NativeLayoutLoad.command_eval _).seq (hboot.seq hsetup))
  have ht : QueryAssembler.Nodes.beginNodeCost a bits+
      (NativeLayoutLoad.cost (QueryAssembler.Nodes.begunNode a bits tail)+(tboot+tsetup)) ≤         20000*(B+1)^4+300*(B+1) := by omega
  refine ⟨ra,rd,rc,words,
    QueryAssembler.Nodes.beginNodeCost a bits+
      (NativeLayoutLoad.cost (QueryAssembler.Nodes.begunNode a bits tail)+(tboot+tsetup)),b,hw,he,ht,hB,
    ready_after_setup s c b (bootstrapped_ready s _ hready ra rd rc words) hframe,
    h832,h833,h834,h835,?_,?_,hscratch,hframe,compiled_halt_trace he 301 832,?_⟩
  · rw [hframe 850 (by decide) (by decide) (by decide) (by decide) (by decide),
      bootstrapped_high s _ ra rd rc words 850 (by decide)]
    exact loadedNode_empty a bits tail 850 (by decide)
  · rw [hframe 851 (by decide) (by decide) (by decide) (by decide) (by decide),
      bootstrapped_high s _ ra rd rc words 851 (by decide)]
    exact loadedNode_empty a bits tail 851 (by decide)
  · have hin : dataBits (a.withPC (some (compiled prepareNode 301 832).entry)) ≤ 896*B :=
      StreamResources.dataBits_le_mul _ hb
    intro k z hk hz i
    have hx := StructuredSpace.local_stack_bound (compiled prepareNode 301 832)
      (steps:=20000*(B+1)^4+300*(B+1)+1) hin k z (by omega) hz i
    exact hx.trans (by omega)

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval_oai
