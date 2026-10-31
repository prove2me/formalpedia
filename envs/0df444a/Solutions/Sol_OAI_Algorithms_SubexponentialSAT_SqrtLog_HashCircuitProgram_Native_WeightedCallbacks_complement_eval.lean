-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.complement_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:48:59.408884+00:00
-- url     : https://prove2.me/submissions/5f4c2dc1-6856-4870-926a-3c8f2f847fcc

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_WeightedCore_command_eval

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

theorem low_injective : Function.Injective lowPort := Fin.castAdd_injective _ _
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

theorem update_low (low high) (i : Fin 56) (word : List Bool) :
    Function.update (tapes low high) (lowPort i) word = tapes (Function.update low i word) high := by
  funext j
  induction j using (Fin.addCases (m := 56) (n := 40)) with
  | left j =>
    change (Function.update (tapes low high) (lowPort i) word) (lowPort j) =
      tapes (Function.update low i word) high (lowPort j)
    by_cases hj : j = i
    · subst j; simp
    · have hh : lowPort j ≠ lowPort i := fun h => hj (low_injective h)
      simp [hh,hj]
  | right j =>
    change (Function.update (tapes low high) (lowPort i) word) (highPort j) =
      tapes (Function.update low i word) high (highPort j)
    simp [(low_ne_high i j).symm]

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

theorem embed_low (regs rr : Fin 8 → Bool) (low next : Fin 56 → List Bool) (high : Fin 40 → List Bool) :
    embedState id lowPort (state regs low high) (⟨rr,next⟩ : State 8 56) = state rr next high := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; simp [state]
  · intro i hi
    induction i using (Fin.addCases (m := 56) (n := 40)) with
    | left i => exact False.elim (hi ⟨i,rfl⟩)
    | right i => simp [state,tapes]

/-- A preserving copy from high persistent memory into arithmetic workspace. -/
theorem copy_high_low (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool)
    (src tmp : Fin 40) (dst : Fin 56) (hne : src ≠ tmp) (htmp : high tmp = []) :
    Eval (copy (highPort src) (lowPort dst) (highPort tmp)) (7*(high src).length+5)
      (state regs low high)
      (state (readRegs regs 0 1 none) (Function.update low dst (high src ++ low dst)) high) := by
  have h := Native.copy_eval (state regs low high) (highPort src) (lowPort dst) (highPort tmp)
    (low_ne_high dst src).symm (fun he => hne (high_injective he))
    (low_ne_high dst tmp).symm (by simpa [state] using htmp)
  simpa only [state,copied,StackRoutines.copyStacks,tapes_high,tapes_low,update_low] using h

/-- A preserving copy of a result back into persistent high memory. -/
theorem copy_low_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool)
    (src : Fin 56) (dst tmp : Fin 40) (hne : tmp ≠ dst) (htmp : high tmp = []) :
    Eval (copy (lowPort src) (highPort dst) (highPort tmp)) (7*(low src).length+5)
      (state regs low high)
      (state (readRegs regs 0 1 none) low (Function.update high dst (low src ++ high dst))) := by
  have h := Native.copy_eval (state regs low high) (lowPort src) (highPort dst) (highPort tmp)
    (low_ne_high src dst) (low_ne_high src tmp) (fun he => hne (high_injective he))
    (by simpa [state] using htmp)
  simpa only [state,copied,StackRoutines.copyStacks,tapes_high,tapes_low,update_high] using h

theorem clear_low (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool)
    (src : Fin 56) :
    Eval (clear (lowPort src)) (2*(low src).length+3) (state regs low high)
      (state (readRegs regs 0 1 none) (Function.update low src []) high) := by
  simpa only [state,cleared,StackRoutines.clearStacks,tapes_low,update_low] using
    Native.clear_eval (state regs low high) (lowPort src)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramArithmeticNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Component: HashCircuitProgramArithmetic. All public namespaces and APIs are retained. -/


/-! Native arithmetic wiring for the hash interpreter. Scale and normalized
addition are fixed imported instruction tables. Product is wired separately
when the native product table is supplied by its implementation module. -/

/-! Component: HashCircuitProgram. All public namespaces and APIs are retained. -/


/-! The fixed native sparse-hash row instruction table. All arithmetic
components are now concrete native programs: there are no operation-valued
parameters in `command` or `program`. The complete serialized semantic and
primitive-time theorem must additionally discharge the local callback
contracts for this table; no such theorem is asserted merely by compilation. -/

/-! Component: HashCircuitProgramMemoryExtra. All public namespaces and APIs are retained. -/


namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The low core's measured execution is lifted without touching high tapes. -/
theorem weightedCore_lift {cost : ℕ} {regs rr : Fin 8 → Bool}
    {a b : MomentsProgram.Product.Store} (high : Fin 40 → List Bool)
    (h : Eval WeightedCore.command cost (MomentsProgram.Product.state regs a)
      (MomentsProgram.Product.state rr b)) :
    Eval weightedCore (cost+1) (state regs (MomentsProgram.Product.tapes a) high)
      (state rr (MomentsProgram.Product.tapes b) high) := by
  have hh := eval_liftCommand h 41 42 id arithmeticPorts
    (state regs (MomentsProgram.Product.tapes a) high) Function.injective_id low_injective
  simpa only [weightedCore, MomentsProgram.Product.state,
    show arithmeticPorts = lowPort from rfl, embed_low] using hh

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

/-! Component: HashCircuitProgramWeightedCallbacks. All public namespaces and APIs are retained. -/


/-! The two concrete weighted arithmetic adapters used by the hash evaluator.
The statements expose exact dictionary bytes and restoration of the common
arithmetic workspace. In particular they do not assume callback correctness. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open Memory

variable {K : Type*} [DecidableEq K]

/-- A cached scalar and seed are physically copied, applied and reclaimed.
For the literal-complement use they are the represented minus-one and one. -/
theorem complement_eval_oai (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width uCap zCap : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (key : K → List Bool) (hk : Function.Injective key)
    (entries seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ha : high 5 = Squarefree.ScaleProgram.encode key entries)
    (hc : high 20 = RingProgram.flat scalar)
    (hs : high 13 = Normalize.bytes key seed) (htmp : high 14 = []) :
    let idle := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree uCap zCap
    let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
    let result := Normalize.bytes key (Normalize.run p t M cache weighted seed)
    ∃ cost ≤ 36*(high 5).length+18*(high 20).length+7*(high 13).length+
      9*result.length+9*degree.length+Squarefree.ScaleProgram.budget key entries+
      Normalize.work p t M cache key weighted seed+73,
      ∃ rr, Eval complement cost (Memory.state regs (Product.tapes idle) high)
        (Memory.state rr (Product.tapes idle) (complementedHigh high result)) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree uCap zCap
  let a := Squarefree.ScaleProgram.encode key entries
  let c := RingProgram.flat scalar
  let s := Normalize.bytes key seed
  let weighted := Squarefree.ScaleProgram.scaled p t M cache table scalar entries
  let result := Normalize.bytes key (Normalize.run p t M cache weighted seed)
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  let r3 := readRegs r2 0 1 none
  have h1 := Memory.copy_high_low regs (Product.tapes e) high 5 14 41 (by decide) htmp
  have hz41 : Product.tapes e 41 = [] := rfl
  simp only [ha,hz41,List.append_nil,update_product_right] at h1
  have h2 := Memory.copy_high_low r1 (Product.tapes {e with right := a}) high 20 14 44 (by decide) htmp
  have hz44 : Product.tapes {e with right := a} 44 = [] := rfl
  simp only [hc,hz44,List.append_nil,update_product_coeff] at h2
  have h3 := Memory.copy_high_low r2 (Product.tapes {e with right := a,coeff := c}) high 13 14 42 (by decide) htmp
  have hz42 : Product.tapes {e with right := a,coeff := c} 42 = [] := rfl
  simp only [hs,hz42,List.append_nil,update_product_acc] at h3
  obtain ⟨k,hkCost,r4,hcore⟩ := WeightedCore.command_eval p t M cache hz table scalar degree width hd hw
    key hk entries seed r3 {e with right := a,coeff := c,acc := s}
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h4 := weightedCore_lift high hcore
  change Eval weightedCore (k+1)
    (Memory.state r3 (Product.tapes {e with right := a,coeff := c,acc := s}) high)
    (Memory.state r4 (Product.tapes {e with right := a,acc := result}) high) at h4
  have h5 := Memory.clear_high r4 (Product.tapes {e with right := a,acc := result}) high 5
  simp only [ha] at h5
  let r5 := readRegs r4 0 1 none
  let high1 := Function.update high (5 : Fin 40) []
  have htmp1 : high1 14 = [] := by simpa [high1] using htmp
  have h6 := Memory.copy_low_high r5 (Product.tapes {e with right := a,acc := result}) high1 42 5 14 (by decide) htmp1
  have hres : Product.tapes {e with right := a,acc := result} 42 = result := rfl
  have hhigh1 : high1 5 = [] := by simp [high1]
  simp only [hres,hhigh1,List.append_nil] at h6
  let r6 := readRegs r5 0 1 none
  let high2 := Function.update high1 (5 : Fin 40) result
  have h7 := Memory.clear_low r6 (Product.tapes {e with right := a,acc := result}) high2 42
  simp only [hres,update_product_acc] at h7
  let r7 := readRegs r6 0 1 none
  have h8 := Memory.clear_low r7 (Product.tapes {e with right := a,acc := []}) high2 41
  have hra : Product.tapes {e with right := a,acc := []} 41 = a := rfl
  simp only [hra,update_product_right] at h8
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  refine ⟨11*a.length+7*c.length+7*s.length+9*result.length+k+30,?_,readRegs r7 0 1 none,?_⟩
  · rw [ha,hc,hs]
    dsimp only [a,c,s,e,Product.idle,weighted,result] at hkCost ⊢
    omega
  · convert hrun using 1 <;> first | rfl | (dsimp only [a,c,s,weighted,result]; omega)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks

/-! Component: HashCircuitProgramProduct. All public namespaces and APIs are retained. -/


/-! Concrete product callback refinement. Both sparse operands are copied from
persistent interpreter stacks into the real product program. The result is
copied back, and all temporary operands are physically reclaimed. -/

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.complement_eval_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.complement_eval_oai.{u_1}
