-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexStep_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:38:52.03875+00:00
-- url     : https://prove2.me/submissions/342f67bc-56e9-4076-85e6-5a45f883a14a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_checkLoop_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCounter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem increment_eval (d : Data) (src : Fin 64) (hs : src≠41)
    (ht : d.stacks 41=[]) :
    Eval (increment src) (CounterPrograms.rippleCost true (d.stacks src)+1)
      d (incremented d src hs) := by
  let p := counterPorts src hs
  have he := eval_call_lifted (CounterPrograms.rippleProgram true)
    p.register (CounterForPrograms.stackPorts p) d p.register.injective
    (CounterForPrograms.stackPorts p).injective
    (CounterForPrograms.ripple_local_trace true (d.regs 0) (d.regs 1) (d.regs 2) (d.stacks src))
  have hm : (CounterForPrograms.stackPorts p : Fin 2 → Fin 64)=incrementStacks src := by
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  change Eval _ _ (CounterForPrograms.install p d (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks src) []) (incremented d src hs) at he
  have hself : CounterForPrograms.install p d (d.regs 0) (d.regs 1) (d.regs 2)
      (d.stacks src) []=d := by
    have hh := CounterForPrograms.install_self p d
    simpa [p,counterPorts,low3,ht] using hh
  rw [hself] at he
  rw [hm] at he
  simpa [increment, p, counterPorts] using he

theorem incremented_stacks (d : Data) (src : Fin 64) (hs : src≠41)
    (ht : d.stacks 41=[]) :
    (incremented d src hs).stacks=
      Function.update d.stacks src (CounterPrograms.ripple true (d.stacks src)) := by
  funext i
  let b := CounterForPrograms.localData false false (d.regs 2)
    (CounterPrograms.ripple true (d.stacks src)) []
  unfold incremented CounterForPrograms.install
  by_cases hi : i=src
  · subst i
    have he := embedState_stack (counterPorts src hs).register
      (CounterForPrograms.stackPorts (counterPorts src hs)) d b
      (CounterForPrograms.stackPorts (counterPorts src hs)).injective 0
    simpa [b,counterPorts,CounterForPrograms.localData,CounterPrograms.counterStacks] using he
  · by_cases h41 : i=41
    · subst i
      have he := embedState_stack (counterPorts src hs).register
        (CounterForPrograms.stackPorts (counterPorts src hs)) d b
        (CounterForPrograms.stackPorts (counterPorts src hs)).injective 1
      simpa [b,counterPorts,CounterForPrograms.localData,CounterPrograms.counterStacks,hi,ht] using he
    · have hn : ¬∃ j, CounterForPrograms.stackPorts (counterPorts src hs) j=i := by
        rintro ⟨j,hj⟩
        fin_cases j
        · apply hi; simpa [counterPorts] using hj.symm
        · apply h41; simpa [counterPorts] using hj.symm
      have he := embedState_stack_frame (counterPorts src hs).register
        (CounterForPrograms.stackPorts (counterPorts src hs)) d b i hn
      simpa [hi] using he

theorem incremented_register (d : Data) (src : Fin 64) (hs : src≠41)
    (i : Fin 16) (hi : 3 ≤ i.val) : (incremented d src hs).regs i=d.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hjlt : (low3 j).val < 3 := by simp [low3]
  rw [show (counterPorts src hs).register j = low3 j by rfl] at hj
  rw [hj] at hjlt
  exact (Nat.not_lt_of_ge hi) hjlt

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.Subexp

theorem matrixWords_flatMap (rows : List (List (List Bool))) :
    MatrixVectorProgram.matrixWords rows=rows.flatMap MatrixProgramSupport.words := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simpa [MatrixVectorProgram.matrixWords] using congrArg (MatrixProgramSupport.words x++·) ih

theorem matrixFrames_rows {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) :
    CodeSearchProgram.matrixFrames Q=
      (List.ofFn fun a => CodeSearchProgram.scalarFrames (List.ofFn (Q a))).flatten := by
  rw [CodeSearchProgram.matrixFrames,matrixWords_flatMap]
  simp only [List.flatMap,CodeSearchProgram.scalarFrames,List.map_ofFn,Function.comp_def]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_eval (src dst : Fin 64) (d : Data)
    (hsd : src≠dst) (hst : src≠24) (htd : (24 : Fin 64)≠dst)
    (htmp : d.stacks 24=[]) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copied src dst d) :=
  Subexp.TupleProgram.copy_eval src dst 24 0 1 hsd hst htd (by decide) d htmp

theorem copied_register (src dst : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (copied src dst d).regs i=d.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  simp [copied,readRegs,h0,h1]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStream
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

theorem collectedRows_append {m : ℕ} (b : ℕ)
    (rs ss : List (List (Fin m × SparseCode.F3))) (tail : List Bool) :
    collectedRows b (rs++ss) tail=collectedRows b ss (collectedRows b rs tail) := by
  simp [collectedRows,rowRecords,List.reverse_append,List.flatMap_append,List.append_assoc]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem sideStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (b : ℕ) (ready : LocalReady base D m b (base.regs 12) v)
    (hq : base.stacks 10=CodeSearchProgram.matrixFrames Q)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D) (ht : (base.stacks 7).length=t)
    (h0 : base.stacks 0=[]) (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) (h16 : base.stacks 16=[]) :
    ∃ n rf, Eval (sideStep side) n base
      ⟨rf,Function.update base.stacks 12
        (collectedRows b (checkRows m shifts Q side v) (base.stacks 12))⟩ ∧
      n ≤ sideCost base D t b ∧ (∀ j : Fin 16, 13 ≤ j.val → rf j=base.regs j) := by
  let d0 : Data := ⟨Function.update base.regs 12 side,base.stacks⟩
  let d1 := copied 10 0 d0
  let d2 := copied 7 16 d1
  have set : Eval (.base (.atom (.set 12 side))) 1 base d0 := .base (.atom _ _)
  have c1 := copy_eval 10 0 d0 (by decide) (by decide) (by decide)
    (ready.work 24 (by decide) (by decide))
  have c2 := copy_eval 7 16 d1 (by decide) (by decide) (by decide)
    (by simpa [d1,d0,copied,copyStacks] using ready.work 24 (by decide) (by decide))
  have rd : LocalReady d2 D m b side v := by
    constructor
    · simp [d2,d1,d0,copied,readRegs]
    · simpa [d2,d1,d0,copied,copyStacks] using ready.vertex
    · simpa [d2,d1,d0,copied,copyStacks] using ready.degree
    · simpa [d2,d1,d0,copied,copyStacks] using ready.modulus
    · simpa [d2,d1,d0,copied,copyStacks] using ready.width
    · exact ready.capacity
    · intro j hj hk
      have hj0 : j≠0 := by intro hne; have hv := congrArg Fin.val hne; change j.val=0 at hv; omega
      have hj16 : j≠16 := by intro hne; have hv := congrArg Fin.val hne; change j.val=16 at hv; omega
      simpa [d2,d1,d0,copied,copyStacks,hj0,hj16] using ready.work j hj hk
  obtain ⟨nl,e,hl,inv,he16,hnl⟩ := checkLoop_eval d2 shifts Q side v b rd
    (by simp [d2,d1,d0,copied,copyStacks,h0,hq,matrixSuffix,matrixFrames_rows])
    (by simpa [d2,d1,d0,copied,copyStacks] using hs)
    (by simpa [d2,d1,d0,copied,copyStacks] using hD)
    (by simpa [d2,d1,d0,copied,copyStacks] using h1)
    (by simpa [d2,d1,d0,copied,copyStacks] using h13)
    (by simpa [d2,d1,d0,copied,copyStacks] using h14)
    (by simpa [d2,d1,d0,copied,copyStacks] using h15)
    (by simpa [d2,d1,d0,copied,copyStacks,h16] using ht)
  have hdrop : (List.ofFn fun a => CodeSearchProgram.scalarFrames (List.ofFn (Q a))).drop t = [] := by
    apply List.drop_eq_nil_of_le
    simp
  have e0 : e.stacks 0=[] := by simpa only [matrixSuffix,hdrop,List.flatten_nil] using inv.source
  have htake : (checkRows m shifts Q side v).take t = checkRows m shifts Q side v := by
    apply List.take_of_length_le
    simp [checkRows]
  have e12 : e.stacks 12=collectedRows b (checkRows m shifts Q side v) (base.stacks 12) := by
    simpa only [htake,d2,d1,d0,copied,copyStacks,
      Function.update_of_ne (by decide : (12 : Fin 64) ≠ 16),
      Function.update_of_ne (by decide : (12 : Fin 64) ≠ 0)] using inv.output
  have hout : e.stacks=Function.update base.stacks 12
      (collectedRows b (checkRows m shifts Q side v) (base.stacks 12)) := by
    funext j
    by_cases hj0 : j=0
    · subst j; simp [e0,h0]
    by_cases hj12 : j=12
    · subst j; simp [e12]
    by_cases hj16 : j=16
    · subst j; simp [he16,h16]
    simpa [d2,d1,d0,copied,copyStacks,hj0,hj12,hj16] using inv.other j hj0 hj12 hj16
  have e_eq : e=(⟨e.regs,Function.update base.stacks 12
      (collectedRows b (checkRows m shifts Q side v) (base.stacks 12))⟩ : Data) := by
    cases e; simp_all
  have costeq : rowCost d2 D b=rowCost base D b := by
    simp [rowCost,portWidth,d2,d1,d0,copied,copyStacks]
  refine ⟨1+((7*(d0.stacks 10).length+5)+((7*(d1.stacks 7).length+5)+nl)),
    e.regs,?_,?_,?_⟩
  · rw [←e_eq]
    exact set.seq (c1.seq (c2.seq hl))
  · simp only [d1,d0,copied,copyStacks,
      Function.update_noteq (by decide : (7 : Fin 64)≠0)]
    rw [costeq] at hnl
    unfold sideCost
    omega
  · intro j hj
    rw [inv.registers j (by omega),copied_register 7 16 d1 j (by omega),
      copied_register 10 0 d0 j (by omega)]
    have hj12 : j≠12 := by intro hne; have hv := congrArg Fin.val hne; change j.val=12 at hv; omega
    simp [d0,hj12]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertexStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem vertexStep_eval_oai {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (v : Cayley.Cube r)
    (b : ℕ) (ready : LocalReady base D m b (base.regs 12) v)
    (hq : base.stacks 10=CodeSearchProgram.matrixFrames Q)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D) (ht : (base.stacks 7).length=t)
    (h0 : base.stacks 0=[]) (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) (h16 : base.stacks 16=[]) :
    ∃ n rf, Eval vertexStep n base
      ⟨rf,Function.update (Function.update base.stacks 12
        (collectedRows b (vertexRows m shifts Q v) (base.stacks 12))) 2
          (CounterPrograms.ripple true (base.stacks 2))⟩ ∧
      n ≤ vertexCost base D t b ∧ (∀ j : Fin 16, 13 ≤ j.val → rf j=base.regs j) := by
  obtain ⟨nl,rl,hl,hnl,hrl⟩ := sideStep_eval base shifts Q false v b ready hq hs hD ht
    h0 h1 h13 h14 h15 h16
  let d1 : Data := ⟨rl,Function.update base.stacks 12
    (collectedRows b (checkRows m shifts Q false v) (base.stacks 12))⟩
  have rd : LocalReady d1 D m b (d1.regs 12) v := by
    constructor
    · rfl
    · simpa [d1] using ready.vertex
    · simpa [d1] using ready.degree
    · simpa [d1] using ready.modulus
    · simpa [d1] using ready.width
    · exact ready.capacity
    · intro j hj hk
      have hj12 : j≠12 := by intro hne; have hv := congrArg Fin.val hne; change j.val=12 at hv; omega
      simpa [d1,hj12] using ready.work j hj hk
  obtain ⟨nr,rr,hr,hnr,hrr⟩ := sideStep_eval d1 shifts Q true v b rd
    (by simpa [d1] using hq) (by simpa [d1] using hs)
    (by simpa [d1] using hD) (by simpa [d1] using ht)
    (by simpa [d1] using h0) (by simpa [d1] using h1)
    (by simpa [d1] using h13) (by simpa [d1] using h14)
    (by simpa [d1] using h15) (by simpa [d1] using h16)
  let d2 : Data := ⟨rr,Function.update d1.stacks 12
    (collectedRows b (checkRows m shifts Q true v) (d1.stacks 12))⟩
  have h41 : d2.stacks 41=[] := by simpa [d2,d1] using ready.work 41 (by decide) (by decide)
  have inc := increment_eval d2 2 (by decide) h41
  have out : (incremented d2 2 (by decide)).stacks=
      Function.update (Function.update base.stacks 12
        (collectedRows b (vertexRows m shifts Q v) (base.stacks 12))) 2
          (CounterPrograms.ripple true (base.stacks 2)) := by
    rw [incremented_stacks d2 2 (by decide) h41]
    simp [d2,d1,vertexRows,collectedRows_append]
  have final : incremented d2 2 (by decide)=
      (⟨(incremented d2 2 (by decide)).regs,
      Function.update (Function.update base.stacks 12
        (collectedRows b (vertexRows m shifts Q v) (base.stacks 12))) 2
          (CounterPrograms.ripple true (base.stacks 2))⟩ : Data) := by
    exact CounterForPrograms.data_ext (a := incremented d2 2 (by decide)) rfl out
  refine ⟨nl+(nr+(CounterPrograms.rippleCost true (d2.stacks 2)+1)),
    (incremented d2 2 (by decide)).regs,?_,?_,?_⟩
  · rw [←final]
    exact hl.seq (hr.seq inc)
  · have hinc := CounterPrograms.rippleCost_le true (d2.stacks 2)
    have same : sideCost d1 D t b=sideCost base D t b := by
      simp [sideCost,rowCost,portWidth,d1]
    rw [same] at hnr
    simp only [d2,d1,Function.update_noteq (by decide : (2 : Fin 64)≠12)] at hinc ⊢
    unfold vertexCost
    omega
  · intro j hj
    rw [incremented_register d2 2 (by decide) j (by omega)]
    exact (hrr j hj).trans (hrl j hj)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexStep_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexStep_eval_oai
