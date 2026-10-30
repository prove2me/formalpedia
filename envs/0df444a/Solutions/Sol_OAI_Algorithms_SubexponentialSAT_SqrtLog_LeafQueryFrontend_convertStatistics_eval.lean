-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:55:45.167616+00:00
-- url     : https://prove2.me/submissions/96da8be2-8791-4fe0-800f-3f2ebea5ccdc

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S130

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
theorem registers_injective (n : ℕ) (hn : n ≤ 40) : Function.Injective (registers n hn) := by
  intro i j h; apply Fin.ext
  exact congrArg (fun z : Fin 40 => z.val) h

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native unary-to-binary conversion for each statistics output. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval (r : Fin 3 → Bool) (input : List Bool) :
    ∃ n output, n ≤ input.length*(8*input.length+10)+4 ∧
      BinaryArithmetic.toNat output = input.length ∧ output.length ≤ input.length ∧
      Eval command n (state r input []) (state (fun _ => false) [] output) := by
  obtain ⟨output,hv,hl,n,hn,ht⟩ := CounterPrograms.length_correct_from (r 0) (r 1) input
  have hregs : Function.update r 2 false = CounterPrograms.counterRegs (r 0) (r 1) false := by
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have hreset : Eval (.base (.atom (.set (2 : Fin 3) false))) 1 (state r input [])
      (state (CounterPrograms.counterRegs (r 0) (r 1) false) input []) := by
    have h := Eval.base (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) (state r input []))
    simpa [state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hregs] using h
  have hc : Eval (.call CounterPrograms.lengthProgram) n
      (state (CounterPrograms.counterRegs (r 0) (r 1) false) input [])
      (state (fun _ => false) [] output) := by
    apply Eval.call
    convert ht using 1
    · simp [state,CounterPrograms.lengthCfg,
        StructuredProgram.State.withPC]
    · simp [state,SubexponentialSAT.BitProgram.terminal
        ]
      first | done | (first | done | (funext i; fin_cases i <;> rfl))
  refine ⟨1+n,output,by omega,(CounterPrograms.value_eq_toNat output).symm.trans hv,hl,hreset.seq hc⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinaryFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation and frame contract for converting a computed unary statistic
into a binary output without disturbing the enclosing machine's data. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem lifted_eval {r s : ℕ} (rr : Fin 3 → Fin r) (ss : Fin 3 → Fin s)
    (hr : Function.Injective rr) (hs : Function.Injective ss)
    (d : State r s) (input : List Bool)
    (hp : projectState rr ss d = state (d.regs ∘ rr) input []) :
    ∃ n output, ∃ b : State r s,
      n ≤ input.length*(8*input.length+10)+5 ∧
      BinaryArithmetic.toNat output = input.length ∧ output.length ≤ input.length ∧
      b.stacks (ss 0) = [] ∧ b.stacks (ss 1) = output ∧ b.stacks (ss 2) = [] ∧
      (∀ i, i ∉ Set.range rr → b.regs i = d.regs i) ∧
      (∀ i, i ∉ Set.range ss → b.stacks i = d.stacks i) ∧
      Eval (.call (ProgramLinking.liftProgram program rr ss)) n d b := by
  obtain ⟨n,output,hn,hv,hl,he⟩ := command_eval (d.regs ∘ rr) input
  let small := state (fun _ => false) [] output
  let b := embedState rr ss d small
  have ht := compiled_halt_trace he 0 1
  rw [←hp] at ht
  have hc := eval_call_from_state program rr ss d hr hs (b := small) ht
  refine ⟨n+1,output,b,by omega,hv,hl,?_,?_,?_,?_,?_,hc⟩
  · exact embedState_stack rr ss d small hs 0
  · exact embedState_stack rr ss d small hs 1
  · exact embedState_stack rr ss d small hs 2
  · exact fun i hi => embedState_register_frame rr ss d small i hi
  · exact fun i hi => embedState_stack_frame rr ss d small i hi

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem binaryPorts_injective (src dst : Fin 768) (hsd : src≠dst)
    (hs : src≠647) (hd : dst≠647) : Function.Injective (binaryPorts src dst) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [binaryPorts]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendNumerics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem binary_eval (a : Data) (src dst : Fin 768) (input : List Bool)
    (hsd : src≠dst) (hs : src≠647) (hd : dst≠647)
    (hsrc : a.stacks src=input) (hout : a.stacks dst=[]) (htmp : a.stacks 647=[]) :
    ∃ n word b, Eval (binary src dst) n a b ∧
      n ≤ input.length*(8*input.length+10)+5 ∧
      BinaryArithmetic.toNat word=input.length ∧ word.length ≤ input.length ∧
      b.stacks dst=word ∧ b.stacks src=[] ∧ b.stacks 647=[] ∧
      (∀ i, i≠src → i≠dst → i≠647 → b.stacks i=a.stacks i) := by
  have hp : projectState r3 (binaryPorts src dst) a =
      LeafStatisticsProgram.Binary.state (a.regs ∘ r3) input [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [binaryPorts,hsrc,hout,htmp]
  obtain ⟨n,word,b,hn,hv,hl,h0,h1,h2,hr,hframe,he⟩ := LeafStatisticsProgram.Binary.lifted_eval
    r3 (binaryPorts src dst) (registers_injective ..) (binaryPorts_injective src dst hsd hs hd) a input hp
  refine ⟨n,word,b,he,hn,hv,hl,h1,h0,h2,?_⟩
  intro i hi0 hi1 hi2
  apply hframe
  rintro ⟨j,hj⟩
  fin_cases j <;> simp [binaryPorts] at hj <;> simp_all

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendConvert
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem convertStatistics_eval_oai (a : Data) (free occ arity factors mass : ℕ)
    (ht : a.stacks 647=[])
    (h626 : a.stacks 626=List.replicate free true)
    (h341 : a.stacks 341=[])
    (h627 : a.stacks 627=List.replicate occ true)
    (h343 : a.stacks 343=[])
    (h642 : a.stacks 642=List.replicate arity true)
    (h344 : a.stacks 344=[])
    (h613 : a.stacks 613=List.replicate factors true)
    (h345 : a.stacks 345=[])
    (h628 : a.stacks 628=List.replicate mass true)
    (h347 : a.stacks 347=[])
    : ∃ n b, Eval convertStatistics n a b ∧
      n ≤ conversionCost free + conversionCost occ + conversionCost arity + conversionCost factors + conversionCost mass ∧
      BinaryArithmetic.toNat (b.stacks 341)=free ∧
      (b.stacks 341).length ≤ free ∧
      BinaryArithmetic.toNat (b.stacks 343)=occ ∧
      (b.stacks 343).length ≤ occ ∧
      BinaryArithmetic.toNat (b.stacks 344)=arity ∧
      (b.stacks 344).length ≤ arity ∧
      BinaryArithmetic.toNat (b.stacks 345)=factors ∧
      (b.stacks 345).length ≤ factors ∧
      BinaryArithmetic.toNat (b.stacks 347)=mass ∧
      (b.stacks 347).length ≤ mass ∧
      b.stacks 647=[] ∧
      (∀ i : Fin 768, i≠626 → i≠341 → i≠627 → i≠343 → i≠642 → i≠344 → i≠613 → i≠345 → i≠628 → i≠347 → i≠647 → b.stacks i=a.stacks i) := by
  have hx1src : a.stacks 626=List.replicate free true := h626
  have hx1out : a.stacks 341=[] := h341
  obtain ⟨n1,w1,a1,he1,hn1,hv1,hl1,hd1,hs1,ht1,hf1⟩ := binary_eval a 626 341
    (List.replicate free true) (by decide) (by decide) (by decide) hx1src hx1out ht
  simp only [List.length_replicate] at hn1 hv1 hl1
  have hx2src : a1.stacks 627=List.replicate occ true := (hf1 627 (by decide) (by decide) (by decide)).trans (h627)
  have hx2out : a1.stacks 343=[] := (hf1 343 (by decide) (by decide) (by decide)).trans (h343)
  obtain ⟨n2,w2,a2,he2,hn2,hv2,hl2,hd2,hs2,ht2,hf2⟩ := binary_eval a1 627 343
    (List.replicate occ true) (by decide) (by decide) (by decide) hx2src hx2out ht1
  simp only [List.length_replicate] at hn2 hv2 hl2
  have hx3src : a2.stacks 642=List.replicate arity true := (hf2 642 (by decide) (by decide) (by decide)).trans ((hf1 642 (by decide) (by decide) (by decide)).trans (h642))
  have hx3out : a2.stacks 344=[] := (hf2 344 (by decide) (by decide) (by decide)).trans ((hf1 344 (by decide) (by decide) (by decide)).trans (h344))
  obtain ⟨n3,w3,a3,he3,hn3,hv3,hl3,hd3,hs3,ht3,hf3⟩ := binary_eval a2 642 344
    (List.replicate arity true) (by decide) (by decide) (by decide) hx3src hx3out ht2
  simp only [List.length_replicate] at hn3 hv3 hl3
  have hx4src : a3.stacks 613=List.replicate factors true := (hf3 613 (by decide) (by decide) (by decide)).trans ((hf2 613 (by decide) (by decide) (by decide)).trans ((hf1 613 (by decide) (by decide) (by decide)).trans (h613)))
  have hx4out : a3.stacks 345=[] := (hf3 345 (by decide) (by decide) (by decide)).trans ((hf2 345 (by decide) (by decide) (by decide)).trans ((hf1 345 (by decide) (by decide) (by decide)).trans (h345)))
  obtain ⟨n4,w4,a4,he4,hn4,hv4,hl4,hd4,hs4,ht4,hf4⟩ := binary_eval a3 613 345
    (List.replicate factors true) (by decide) (by decide) (by decide) hx4src hx4out ht3
  simp only [List.length_replicate] at hn4 hv4 hl4
  have hx5src : a4.stacks 628=List.replicate mass true := (hf4 628 (by decide) (by decide) (by decide)).trans ((hf3 628 (by decide) (by decide) (by decide)).trans ((hf2 628 (by decide) (by decide) (by decide)).trans ((hf1 628 (by decide) (by decide) (by decide)).trans (h628))))
  have hx5out : a4.stacks 347=[] := (hf4 347 (by decide) (by decide) (by decide)).trans ((hf3 347 (by decide) (by decide) (by decide)).trans ((hf2 347 (by decide) (by decide) (by decide)).trans ((hf1 347 (by decide) (by decide) (by decide)).trans (h347))))
  obtain ⟨n5,w5,a5,he5,hn5,hv5,hl5,hd5,hs5,ht5,hf5⟩ := binary_eval a4 628 347
    (List.replicate mass true) (by decide) (by decide) (by decide) hx5src hx5out ht4
  simp only [List.length_replicate] at hn5 hv5 hl5
  have hout1 : a5.stacks 341=w1 := (hf5 341 (by decide) (by decide) (by decide)).trans ((hf4 341 (by decide) (by decide) (by decide)).trans ((hf3 341 (by decide) (by decide) (by decide)).trans ((hf2 341 (by decide) (by decide) (by decide)).trans (hd1))))
  have hout2 : a5.stacks 343=w2 := (hf5 343 (by decide) (by decide) (by decide)).trans ((hf4 343 (by decide) (by decide) (by decide)).trans ((hf3 343 (by decide) (by decide) (by decide)).trans (hd2)))
  have hout3 : a5.stacks 344=w3 := (hf5 344 (by decide) (by decide) (by decide)).trans ((hf4 344 (by decide) (by decide) (by decide)).trans (hd3))
  have hout4 : a5.stacks 345=w4 := (hf5 345 (by decide) (by decide) (by decide)).trans (hd4)
  have hout5 : a5.stacks 347=w5 := (hd5)
  refine ⟨n1+(n2+(n3+(n4+n5))),a5,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,ht5,?_⟩
  · simpa [convertStatistics,sequence] using he1.seq (he2.seq (he3.seq (he4.seq (he5.seq (Eval.base (.skip _))))))
  · dsimp [conversionCost]; omega
  · simpa [hout1] using hv1
  · simpa [hout1] using hl1
  · simpa [hout2] using hv2
  · simpa [hout2] using hl2
  · simpa [hout3] using hv3
  · simpa [hout3] using hl3
  · simpa [hout4] using hv4
  · simpa [hout4] using hl4
  · simpa [hout5] using hv5
  · simpa [hout5] using hl5
  · intro i h626 h341 h627 h343 h642 h344 h613 h345 h628 h347 h647
    exact (hf5 i h628 h347 h647).trans ((hf4 i h613 h345 h647).trans ((hf3 i h642 h344 h647).trans ((hf2 i h627 h343 h647).trans ((hf1 i h626 h341 h647).trans (rfl)))))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics_eval_oai
