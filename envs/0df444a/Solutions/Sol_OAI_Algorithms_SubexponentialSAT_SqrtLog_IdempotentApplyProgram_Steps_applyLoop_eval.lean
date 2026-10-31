-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:57:58.4617+00:00
-- url     : https://prove2.me/submissions/fb4f4ca0-8826-4e3c-9f77-3693817257b9

import Mathlib
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Steps_loop_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed record-control code for sparse-hash evaluation. This module fixes
all parsing and traversal code. Arithmetic components below are finite native
commands, to be instantiated by the separate dictionary modules; no semantic
function is called by the machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem copy_eval (d : Machine) (src dst tmp : Fin 96)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7*(d.stacks src).length+5) d (copied d src dst) := by
  apply Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 8) 1 hsd hst htd
    (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [copied,StackRoutines.copyResult,StructuredProgram.State.withPC,
    StackRoutines.copyProgram,Nat.add_assoc] using hh

theorem clear_eval (d : Machine) (src : Fin 96) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [cleared,StackRoutines.clearResult,StructuredProgram.State.withPC,
    StackRoutines.clearProgram,Nat.add_assoc] using hh

theorem transfer_eval (d : Machine) (src dst : Fin 96) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (transferred d src dst) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [transferred,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Split-memory rules for composing the actual low arithmetic workspace with
persistent high interpreter data. All movement lemmas retain primitive costs. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem high_injective : Function.Injective highPort := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change 56+i.val = 56+j.val at hh
  omega

theorem low_ne_high (i : Fin 56) (j : Fin 40) : lowPort i ≠ highPort j := by
  intro h
  have hh := congrArg Fin.val h
  change i.val = 56+j.val at hh
  omega

theorem update_high (low high) (i : Fin 40) (word : List Bool) :
    Function.update (tapes low high) (highPort i) word = tapes low (Function.update high i word) := by
  funext j
  induction j using (Fin.addCases (m := 56) (n := 40)) with
  | left j =>
    change (Function.update (tapes low high) (highPort i) word) (lowPort j) =
      tapes low (Function.update high i word) (lowPort j)
    simp [low_ne_high j i]
  | right j =>
    change (Function.update (tapes low high) (highPort i) word) (highPort j) =
      tapes low (Function.update high i word) (highPort j)
    by_cases hj : j = i
    · subst j; simp
    · have hh : highPort j ≠ highPort i := fun h => hj (high_injective h)
      simp [hh,hj]

theorem clear_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool)
    (src : Fin 40) :
    Eval (clear (highPort src)) (2*(high src).length+3) (state regs low high)
      (state (readRegs regs 0 1 none) low (Function.update high src [])) := by
  simpa only [state,cleared,StackRoutines.clearStacks,tapes_high,update_high] using
    Native.clear_eval (state regs low high) (highPort src)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native high-register movement used by the Horner controller. Each rule
retains the full cost of copying or reversing the actual serialized data. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open BitProgram StructuredCalls
open HashCircuitProgram.Native

theorem copy_high_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (src dst tmp : Fin 40)
    (hsd : src≠dst) (hst : src≠tmp) (htd : tmp≠dst) (htmp : high tmp=[]) :
    Eval (copy (Memory.highPort src) (Memory.highPort dst) (Memory.highPort tmp))
      (7*(high src).length+5) (Memory.state regs low high)
      (Memory.state (readRegs regs 0 1 none) low
        (Function.update high dst (high src++high dst))) := by
  have h:=copy_eval (Memory.state regs low high)
    (Memory.highPort src) (Memory.highPort dst) (Memory.highPort tmp)
    (Memory.high_injective.ne hsd) (Memory.high_injective.ne hst)
    (Memory.high_injective.ne htd) (by simpa [Memory.state] using htmp)
  simpa only [copied,Memory.state,StackRoutines.copyStacks,Memory.tapes_high,
    Memory.update_high] using h

theorem transfer_high_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (src dst : Fin 40) (hsd : src≠dst) :
    Eval (transfer (Memory.highPort src) (Memory.highPort dst))
      (3*(high src).length+3) (Memory.state regs low high)
      (Memory.state (readRegs regs 0 1 none) low
        (Function.update (Function.update high src []) dst ((high src).reverse++high dst))) := by
  have h:=transfer_eval (Memory.state regs low high)
    (Memory.highPort src) (Memory.highPort dst) (Memory.high_injective.ne hsd)
  simpa only [transferred,Memory.state,StackRoutines.transferStacks,Memory.tapes_high,
    Memory.update_high] using h

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte order for descending Horner application. A single whole-tape reversal
puts the last digit first and each digit's coefficients in c,b,a order. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open SubexpQuarticRing

theorem triplesTape_reverse {B : ℕ} (vs : List (Triple (Word B))) :
    (triplesTape vs).reverse=descendingTape vs.reverse := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp [triplesTape,descendingTape,tripleTape,List.reverse_cons,List.map_append,
      List.flatten_append,List.reverse_append]
    simpa [triplesTape,descendingTape,List.map_reverse,List.append_assoc] using ih

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Native high-register services for the quadratic and Horner steps. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram
namespace Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]


theorem seq_tail {r s : ℕ} {a b c : Cmd r s} {n m : ℕ} {x y z : State r s}
    (hab : Eval (.seq a b) n x y) (hc : Eval c m y z) :
    Eval (.seq a (.seq b c)) (n+m) x z := by
  cases hab with
  | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)

end Steps
end SubexponentialSAT.SqrtLog.IdempotentApplyProgram


/-! Complete native evaluation of one degree-two coefficient digit. -/


/-! The native Horner accumulator update, including every move and cleanup. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem move_eval (regs : Regs) (low : Fin 56 → List Bool) (high : Data)
    (src dst : Fin 40) (hne : src≠dst) (hs : src≠14) (hd : dst≠14)
    (hempty : high dst=[]) (htmp : high 14=[]) :
    Eval (.seq (copy (Memory.highPort src) (Memory.highPort dst) 70)
        (clear (Memory.highPort src))) (9*(high src).length+8)
      (Memory.state regs low high)
      (Memory.state (readRegs (readRegs regs 0 1 none) 0 1 none) low
        (Function.update (Function.update high src []) dst (high src))) := by
  have hc:=copy_high_high regs low high src dst 14 hne hs hd.symm htmp
  simp only [hempty,List.append_nil] at hc
  have he:=Memory.clear_high (readRegs regs 0 1 none) low
    (Function.update high dst (high src)) src
  simp only [Function.update_of_ne hne] at he
  have hstate : Function.update (Function.update high dst (high src)) src []=
      Function.update (Function.update high src []) dst (high src) := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=dst <;> simp_all
  rw [hstate] at he
  convert hc.seq he using 1 <;> first | rfl | omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps


/-! Measured descending Horner loop over the actual computed coefficient tape. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem peek_eval (regs : Regs) (l : Fin 56 → List Bool) (high : Data) :
    Eval peekCoefficients 1 (Memory.state regs l high)
      (Memory.state (readRegs regs 0 7 (high 23).head?) l high) := by
  exact .base (.atom _ _)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

/-- Tape reversal, native Horner evaluation and final scratch reclamation. -/
theorem applyLoop_eval_oai (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (hg : high 30=Product.bytes g)
    (htape : high 22=triplesTape vs) (h5 : high 5=[]) (h23 : high 23=[])
    (h28 : high 28=[]) (h29 : high 29=[]) (h31 : high 31=[])
    (hshape : (high 32).length=n) (hready : scalarReady 11 high) :
    ∃ cost ≤ applyLoopCost ctx h g vs (high 38), ∃ rr,
      Eval applyLoop cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx)
          (Function.update (Function.update (Function.update high 30 []) 38 []) 11
            (Product.bytes (loopResult ctx h g vs.reverse [])))) := by
  let tape:=triplesTape vs
  let r1:=readRegs regs 0 1 none
  let h1:=Function.update high (28:Fin 40) tape
  have e1:=copy_high_high regs (low ctx) high 22 28 14 (by decide) (by decide) (by decide)
    (hready 14 (by simp))
  simp only [htape,h28,List.append_nil] at e1
  change Eval _ _ _ (Memory.state r1 (low ctx) h1) at e1
  let r2:=readRegs r1 0 1 none
  let h2:=Function.update (Function.update h1 (28:Fin 40) []) 23 tape.reverse
  have e2:=transfer_high_high r1 (low ctx) h1 28 23 (by decide)
  have ht1 : h1 28=tape:=by simp [h1]
  have h23' : h1 23=[]:=by simpa [h1] using h23
  simp only [ht1,h23',List.append_nil] at e2
  change Eval _ _ _ (Memory.state r2 (low ctx) h2) at e2
  let rp:=readRegs r2 0 7 (h2 23).head?
  have ep:=peek_eval r2 (low ctx) h2
  have ready2 : scalarReady 11 h2 := by
    simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false] at hready ⊢
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [h2,h1,hready]
  obtain ⟨kl,bl,rl,el⟩:=loop_eval ctx hd hB h g vs.reverse [] rp h2
    (by simpa [h2,h1] using hh) (by simpa [h2,h1] using hg)
    (by simpa [h2,h1,Product.bytes,Normalize.bytes,Squarefree.Program.encodeDictionary,
      Squarefree.Program.rawEntries] using h31)
    (by simpa [h2,h1] using h5) (by simpa [h2,h1] using h29)
    (by simp [h2,tape,triplesTape_reverse])
    (by simpa [h2,h1] using hshape) ready2 (by simp [rp,readRegs])
  let result:=Product.bytes (loopResult ctx h g vs.reverse [])
  let hl:=Function.update (Function.update h2 (23:Fin 40) []) 31 result
  change Eval _ _ _ (Memory.state rl (low ctx) hl) at el
  have em:=move_eval rl (low ctx) hl 31 11 (by decide) (by decide) (by decide)
    (by simpa [hl,h2,h1] using hready 11 (by simp))
    (by simpa [hl,h2,h1] using hready 14 (by simp))
  have hres : hl 31=result:=by simp [hl]
  simp only [hres] at em
  let rm:=readRegs (readRegs rl 0 1 none) 0 1 none
  let hm:=Function.update (Function.update hl (31:Fin 40) []) 11 result
  change Eval _ _ _ (Memory.state rm (low ctx) hm) at em
  have eg:=Memory.clear_high rm (low ctx) hm 30
  have hgm : hm 30=Product.bytes g:=by simpa [hm,hl,h2,h1] using hg
  simp only [hgm] at eg
  let rg:=readRegs rm 0 1 none
  let hgc:=Function.update hm (30:Fin 40) []
  have ek:=Memory.clear_high rg (low ctx) hgc 38
  have hkey : hgc 38=high 38:=by simp [hgc,hm,hl,h2,h1]
  simp only [hkey] at ek
  let rk:=readRegs rg 0 1 none
  let hk:=Function.update hgc (38:Fin 40) []
  have eall:=e1.seq (e2.seq (ep.seq (el.seq (seq_tail em (eg.seq (ek.seq
    (Eval.base (StructuredProgram.Eval.skip (Memory.state rk (low ctx) hk)))))))))
  have hout : hk=Function.update (Function.update (Function.update high 30 []) 38 []) 11 result := by
    funext i
    by_cases hi11 : i=11
    · subst i
      simp [hk,hgc,hm,hl,h2,h1]
    by_cases hi30 : i=30
    · subst i
      simp [hk,hgc,hm,hl,h2,h1]
    by_cases hi38 : i=38
    · subst i
      simp [hk,hgc,hm,hl,h2,h1]
    by_cases hi23 : i=23
    · subst i
      simp [hk,hgc,hm,hl,h2,h1,h23]
    by_cases hi28 : i=28
    · subst i
      simp [hk,hgc,hm,hl,h2,h1,h28]
    by_cases hi31 : i=31
    · subst i
      simp [hk,hgc,hm,hl,h2,h1,h31]
    simp [hk,hgc,hm,hl,h2,h1,hi11,hi30,hi38,hi23,hi28,hi31]
  rw [hout] at eall
  refine ⟨_,?_,rk,eall⟩
  dsimp [applyLoopCost,tape,result] at *
  omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.applyLoop_eval_oai
