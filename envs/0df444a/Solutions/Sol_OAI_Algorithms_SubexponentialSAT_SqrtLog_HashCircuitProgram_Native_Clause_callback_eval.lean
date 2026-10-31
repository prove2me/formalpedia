-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:46:18.947667+00:00
-- url     : https://prove2.me/submissions/1fae6e35-2f76-4dd2-85fe-7427171fd977

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S146
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_WeightedCallbacks_complement_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_fetchLiteral_from_state
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Product_step_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed caller framing for the native sparse-hash interpreter. Low ports
0--55 are reserved for arithmetic. Literal lookup uses 56--62, leaving the
clause, row and constant accumulators physically untouched. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem literalRegisters_injective : Function.Injective literalRegisters :=
  Fin.castAdd_injective _ _
theorem literalStacks_injective : Function.Injective literalStacks := by
  intro i j h
  have h' := congrArg Fin.val h
  apply Fin.ext
  simp only [literalStacks] at h'
  omega

theorem literalFrame_stack (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) (i : Fin 96)
    (hi : i.val < 56 ∨ 63 ≤ i.val) :
    (literalFrame base regs positive scan query result table).stacks i = base.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  simp only [literalStacks] at hh
  have := j.isLt
  omega

@[simp] theorem literalFrame_result (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) :
    (literalFrame base regs positive scan query result table).stacks 61 = result := by
  exact embedState_stack literalRegisters literalStacks base _ literalStacks_injective 5

@[simp] theorem literalFrame_table (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) :
    (literalFrame base regs positive scan query result table).stacks 62 = table := by
  exact embedState_stack literalRegisters literalStacks base _ literalStacks_injective 6

@[simp] theorem literalFrame_sign (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) :
    (literalFrame base regs positive scan query result table).regs 5 = positive := by
  exact embedState_register literalRegisters literalStacks base _ literalRegisters_injective 5

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

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

theorem recordReturn_eval (d : Machine) : Eval recordReturn 3 d (returned d) := by
  exact (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) d)).seq
    ((Eval.base (StructuredProgram.Eval.atom (.set (1 : Fin 8) true) _)).seq
      (Eval.base (StructuredProgram.Eval.atom (.set (2 : Fin 8) false) _)))

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_injective {n : ℕ} :
    Function.Injective (encodeMask (n := n)) := by
  intro a b h
  have hf : (fun i : Fin n => decide (i ∈ a)) =
      (fun i : Fin n => decide (i ∈ b)) := List.ofFn_injective h
  ext i
  have hi := congrFun hf i
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all

theorem encodeIndex_injective {n : ℕ} :
    Function.Injective (encodeIndex (n := n)) := by
  intro a b h
  have hfirst : a.u = b.u ∧
      Encoding.encodeNat a.z ++ encodeMask a.vars =
        Encoding.encodeNat b.z ++ encodeMask b.vars := by
    simpa [encodeIndex, List.append_assoc] using congrArg Encoding.readNat h
  have hsecond : a.z = b.z ∧ encodeMask a.vars = encodeMask b.vars := by
    simpa using congrArg Encoding.readNat hfirst.2
  have hs := encodeMask_injective hsecond.2
  cases a
  cases b
  cases hfirst.1
  cases hsecond.1
  cases hs
  rfl

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem peek_eval (regs : Fin 8 → Bool) (a : Store) :
    Eval peek 1 (state regs a) (ready regs a) := .base (.atom _ _)

theorem ready_nil {n B d : ℕ} (regs : Fin 8 → Bool) (e : Store)
    (right seed : List (Entry n B d)) : (ready regs (working e [] right seed)).regs 7 = false := by
  simp [ready,state,working,readRegs,Normalize.bytes,Squarefree.Program.rawEntries,
    Squarefree.Program.encodeDictionary]

theorem ready_cons {n B d : ℕ} (regs : Fin 8 → Bool) (e : Store)
    (a : Entry n B d) (left right seed : List (Entry n B d)) :
    (ready regs (working e (a::left) right seed)).regs 7 = true := by
  cases hk : Squarefree.encodeIndex a.1 <;>
    simp [ready,state,working,readRegs,Normalize.bytes,Squarefree.Program.rawEntries,
      Squarefree.Program.encodeDictionary,Encoding.frame,hk]

theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right seed : List (Entry n (baseWidth p t) d)) (regs : Fin 8 → Bool) :
    ∃ k ≤ work p t M cache table u J left right seed, ∃ rr,
      Eval loop k (ready regs (working (environment p t M cache table degree width u J) left right seed))
        (state rr (working (environment p t M cache table degree width u J) [] right
          (run p t M cache table u J left right seed))) := by
  induction left generalizing seed regs with
  | nil =>
    exact ⟨1,le_rfl,readRegs regs 0 7 none,Eval.while_false (ready_nil regs _ right seed)⟩
  | cons a left ih =>
    let initial := readRegs regs 0 7 (bytes (a::left)).head?
    let next := Normalize.run p t M cache (block p t M cache table u J a right) seed
    obtain ⟨k,hk,r1,hs⟩ := step_eval p t M cache hz table degree width hd hw u J a left right seed initial
    obtain ⟨v,hv,rr,ht⟩ := ih next r1
    have hp := peek_eval r1 (working (environment p t M cache table degree width u J) left right next)
    have hrun := Eval.while_true (ready_cons regs _ a left right seed) (hs.seq hp) ht
    exact ⟨_,by dsimp only [next] at hv; dsimp [work]; omega,rr,hrun⟩

theorem program_run_seed (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right seed : List (Entry n (baseWidth p t) d)) (regs : Fin 8 → Bool) :
    ∃ rr, RunsIn program (work p t M cache table u J left right seed+2)
      ((state regs (working (environment p t M cache table degree width u J) left right seed)).withPC
        (some program.entry))
      ((state rr (working (environment p t M cache table degree width u J) [] right
        (run p t M cache table u J left right seed))).withPC none) := by
  obtain ⟨k,hk,rr,he⟩ := loop_eval p t M cache hz table degree width hd hw u J left right seed regs
  have hrun := (peek_eval regs _).seq he
  exact ⟨rr,1+k+1,by omega,compiled_halt_trace hrun 40 42⟩

/-- Public product ABI, with all scratch stacks empty at return. -/
theorem program_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (Entry n (baseWidth p t) d)) (regs : Fin 8 → Bool) :
    ∃ rr, RunsIn program (work p t M cache table u J left right []+2)
      ((state regs (input M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
        (List.replicate u true) (List.replicate J true) (bytes left) (bytes right))).withPC (some program.entry))
      ((state rr (output M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
        (List.replicate u true) (List.replicate J true) (bytes right)
        (bytes (run p t M cache table u J left right [])))).withPC none) := by
  simpa only [working,environment,input,output,idle,Normalize.bytes,Squarefree.Program.encodeDictionary,List.map_nil,Squarefree.Program.rawEntries] using
    program_run_seed p t M cache hz table degree width hd hw u J left right [] regs

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

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


/-! Component: HashCircuitProgramWeightedCallbacks. All public namespaces and APIs are retained. -/


/-! The two concrete weighted arithmetic adapters used by the hash evaluator.
The statements expose exact dictionary bytes and restoration of the common
arithmetic workspace. In particular they do not assume callback correctness. -/

/-! Component: HashCircuitProgramProduct. All public namespaces and APIs are retained. -/


/-! Concrete product callback refinement. Both sparse operands are copied from
persistent interpreter stacks into the real product program. The result is
copied back, and all temporary operands are physically reclaimed. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
namespace ProductCallback

private theorem update_left (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 40 w =
      MomentsProgram.Product.tapes {s with left := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
private theorem update_right (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 41 w =
      MomentsProgram.Product.tapes {s with right := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
private theorem update_acc (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 42 w =
      MomentsProgram.Product.tapes {s with acc := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]

/-- Fully native callback theorem. The only numerical assumptions specify the
actual represented coefficient ring and runtime shapes; there is no abstract
arithmetic-command or callback-cost premise. -/
theorem eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J : ℕ) (left right : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ha : high 11 = MomentsProgram.Product.bytes left)
    (hb : high 5 = MomentsProgram.Product.bytes right) (htmp : high 14 = []) :
    let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
      degree (List.replicate u true) (List.replicate J true)
    let result := MomentsProgram.Product.bytes (MomentsProgram.Product.run p t M cache table u J left right [])
    ∃ cost ≤ 9*(MomentsProgram.Product.bytes left).length +
        11*(MomentsProgram.Product.bytes right).length + 9*result.length +
        MomentsProgram.Product.work p t M cache table u J left right [] + 29,
      ∃ rr, Eval (productAdapter product) cost
        (Memory.state regs (MomentsProgram.Product.tapes e) high)
        (Memory.state rr (MomentsProgram.Product.tapes e) (resultHigh high result)) := by
  dsimp only
  let e := MomentsProgram.Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
    degree (List.replicate u true) (List.replicate J true)
  let a := MomentsProgram.Product.bytes left
  let b := MomentsProgram.Product.bytes right
  let result := MomentsProgram.Product.bytes (MomentsProgram.Product.run p t M cache table u J left right [])
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  have h1 := Memory.copy_high_low regs (MomentsProgram.Product.tapes e) high 11 14 40 (by decide) htmp
  simp only [update_left] at h1
  have hzero40 : MomentsProgram.Product.tapes e 40 = [] := rfl
  simp only [ha,hzero40,List.append_nil] at h1
  have h2 := Memory.copy_high_low r1 (MomentsProgram.Product.tapes {e with left := a}) high
    5 14 41 (by decide) htmp
  simp only [update_right] at h2
  have hzero41 : MomentsProgram.Product.tapes {e with left := a} 41 = [] := rfl
  simp only [hb,hzero41,List.append_nil] at h2
  obtain ⟨r3,k,hk,htrace⟩ := MomentsProgram.Product.program_run p t M cache hz table degree width hd hw
    u J left right r2
  have hp := eval_call_lifted MomentsProgram.Product.program id Memory.lowPort
    (Memory.state r2 (MomentsProgram.Product.tapes {e with left := a,right := b}) high)
    Function.injective_id Memory.low_injective htrace
  simp only [MomentsProgram.Product.state,Memory.embed_low] at hp
  change Eval product k
    (Memory.state r2 (MomentsProgram.Product.tapes {e with left := a,right := b}) high)
    (Memory.state r3 (MomentsProgram.Product.tapes {e with right := b,acc := result}) high) at hp
  have h3 := Memory.clear_high r3 (MomentsProgram.Product.tapes {e with right := b,acc := result}) high 11
  simp only [ha] at h3
  let r4 := readRegs r3 0 1 none
  let high1 := Function.update high (11 : Fin 40) []
  have h4 := Memory.clear_high r4 (MomentsProgram.Product.tapes {e with right := b,acc := result}) high1 5
  have hhigh1 : high1 5 = b := by simpa [high1,b] using hb
  simp only [hhigh1] at h4
  let r5 := readRegs r4 0 1 none
  let high2 := Function.update high1 (5 : Fin 40) []
  have htmp2 : high2 14 = [] := by simpa [high2,high1] using htmp
  have h5 := Memory.copy_low_high r5 (MomentsProgram.Product.tapes {e with right := b,acc := result})
    high2 42 11 14 (by decide) htmp2
  have hres : MomentsProgram.Product.tapes {e with right := b,acc := result} 42 = result := rfl
  have hhigh2 : high2 11 = [] := by simp [high2,high1]
  simp only [hres,hhigh2,List.append_nil] at h5
  let r6 := readRegs r5 0 1 none
  let high3 := Function.update high2 (11 : Fin 40) result
  have h6 := Memory.clear_low r6 (MomentsProgram.Product.tapes {e with right := b,acc := result}) high3 42
  simp only [hres,update_acc] at h6
  let r7 := readRegs r6 0 1 none
  have h7 := Memory.clear_low r7 (MomentsProgram.Product.tapes {e with right := b,acc := []}) high3 41
  have hb41 : MomentsProgram.Product.tapes {e with right := b,acc := []} 41 = b := rfl
  simp only [hb41,update_right] at h7
  have hrun := h1.seq (h2.seq (hp.seq (h3.seq (h4.seq (h5.seq (h6.seq h7))))))
  refine ⟨9*a.length+11*b.length+9*result.length+k+27,?_,readRegs r7 0 1 none,?_⟩
  · dsimp only [a,b,result] at *
    omega
  · convert hrun using 1 <;> first | rfl | (dsimp only [a,b,result]; omega)

end ProductCallback
end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLiteralState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct-call interface from the actual caller state. This avoids preparing
an extra machine-state embedding between the record parser and literal lookup. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem project_lookup (d : Machine) (query table : List Bool)
    (h : LookupReady d table) (hq : d.stacks 58 = query) :
    projectState literalRegisters literalStacks d = data (callerRegs d) (d.regs 5) [] query [] table := by
  apply congrArg₂ StructuredProgram.State.mk
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  · funext i; fin_cases i
    · exact h.scan
    · exact h.temporary
    · exact hq
    · exact h.compare
    · exact h.scratch
    · exact h.output
    · exact h.saved

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLiteralMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem literalFrame_memory (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (rr : Fin 5 → Bool) (positive : Bool) (payload table : List Bool) :
    let d := Memory.state regs low high
    let result := literalFrame d rr positive [] [] payload table
    result = Memory.state result.regs low (literalHigh high payload table) := by
  dsimp only
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    induction i using (Fin.addCases (m := 56) (n := 40)) with
    | left i =>
      have h := literalFrame_stack (Memory.state regs low high) rr positive [] [] payload table
        (Fin.castAdd 40 i) (Or.inl i.isLt)
      simpa [literalFrame, embedState, Memory.state, Memory.tapes] using h
    | right i =>
      rw [Memory.tapes, Fin.addCases_right]
      refine Fin.addCases (m := 7) (n := 33) (fun j => ?_) (fun j => ?_) i
      · rw [literalHigh, Fin.addCases_left]
        have h := embedState_stack literalRegisters literalStacks (Memory.state regs low high)
          (data rr positive [] [] payload table) literalStacks_injective j
        fin_cases j <;> simpa [literalFrame, embedState, literalHigh, Memory.state, Memory.tapes,
          Fin.addCases_left, Fin.addCases_right,
          literalStacks, data, extend, SubexponentialSAT.SubexpRecordScan.recordState,
          SubexponentialSAT.SubexpRecordScan.storage] using h
      · have h := literalFrame_stack (Memory.state regs low high) rr positive [] [] payload table
          (Fin.natAdd 56 (Fin.natAdd 7 j)) (Or.inr (by simp; omega))
        simpa [literalFrame, embedState, literalHigh, Memory.state, Memory.tapes] using h

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff


/-! Component: HashCircuitProgramLiteralCallback. All public namespaces and APIs are retained. -/


/-! Literal callback with actual lookup, polarity, sparse product, and return.
The represented minus-one and one values are explicit cached inputs. All work
is performed by the fixed native commands wired into the row interpreter. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one payload left : List (Product.Entry n (baseWidth p t) d))

theorem eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (degree width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (u J v : ℕ) (positive : Bool) (entries : List (List Bool × List Bool))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (hlookup : entries.lookup (Encoding.encodeNat v) = some (Product.bytes payload))
    (h0 : high 0 = []) (h1 : high 1 = []) (h3 : high 3 = []) (h4 : high 4 = []) (h5 : high 5 = [])
    (h2 : high 2 = (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse)
    (h6 : high 6 = Squarefree.Program.lookupRecords entries)
    (hleft : high 11 = Product.bytes left) (hone : high 13 = Product.bytes one)
    (hminus : high 20 = RingProgram.flat minusOne) (htmp : high 14 = []) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    ∃ cost ≤ budget p t M cache table minusOne one payload left degree u J v positive entries,
      ∃ rr, Eval (literalStep arithmetic) cost (Memory.state regs (Product.tapes e) high)
        (Memory.state (returned (Memory.state rr (Product.tapes e) high)).regs (Product.tapes e)
          (outputHigh high (Squarefree.Program.lookupRecords entries)
            (Product.bytes (result p t M cache table minusOne one payload left u J positive)))) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let start := Memory.state regs (Product.tapes e) high
  let lookupTable := Squarefree.Program.lookupRecords entries
  have hready : LookupReady start lookupTable := by
    constructor
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h0
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h1
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h3
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h4
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h5
    · simpa [start,lookupTable,Memory.state,Memory.tapes] using h6
  have hquery : start.stacks 58 = (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse := by
    simpa [start,Memory.state,Memory.tapes] using h2
  have hproject := project_lookup start
    (Encoding.encodeNat (2*v+(if positive then 1 else 0))).reverse lookupTable hready hquery
  obtain ⟨nf,hnf,rf,hf,hflag⟩ := fetchLiteral_from_state start (callerRegs start) (start.regs 5)
    positive v (Product.bytes payload) entries hlookup hproject
  let fetched := literalFrame start rf positive [] [] (Product.bytes payload) lookupTable
  let hfHigh := literalHigh high (Product.bytes payload) lookupTable
  have hmem : fetched = Memory.state fetched.regs (Product.tapes e) hfHigh :=
    literalFrame_memory regs (Product.tapes e) high rf positive (Product.bytes payload) lookupTable
  have hsign : fetched.regs 5 = positive :=
    literalFrame_sign start rf positive [] [] (Product.bytes payload) lookupTable
  change Eval fetchLiteral nf start fetched at hf
  rw [hmem] at hf
  let chosen := value p t M cache table minusOne one payload positive
  let hcHigh := Function.update hfHigh (5 : Fin 40) (Product.bytes chosen)
  have hchoose : ∃ nc ≤ (if positive then negateBudget p t M cache table minusOne one payload degree else 0)+1,
      ∃ rc, Eval (.ite 5 complement (.base .skip)) nc
        (Memory.state fetched.regs (Product.tapes e) hfHigh)
        (Memory.state rc (Product.tapes e) hcHigh) := by
    cases hp : positive with
    | false =>
      have hsame : hcHigh = hfHigh := by
        funext i
        by_cases hi : i = 5
        · subst i; simp [hcHigh,hfHigh,chosen,value,hp,literalHigh]
        · simp [hcHigh,hi]
      refine ⟨1,by simp [],fetched.regs,?_⟩
      rw [hsame]
      apply Eval.ite_false (by simpa [Memory.state,hp] using hsign)
      exact Eval.base (StructuredProgram.Eval.skip _)
    | true =>
      obtain ⟨nc,hnc,rc,hcomp⟩ := WeightedCallbacks.complement_eval p t M cache hz table minusOne
        degree width (List.replicate u true) (List.replicate J true) hd hw
        Squarefree.encodeIndex Squarefree.encodeIndex_injective payload one fetched.regs hfHigh
        (by rfl) (by simpa [hfHigh,literalHigh] using hminus)
        (by simpa [hfHigh,literalHigh] using hone) (by simpa [hfHigh,literalHigh] using htmp)
      have hout : WeightedCallbacks.complementedHigh hfHigh
          (Normalize.bytes Squarefree.encodeIndex (negative p t M cache table minusOne one payload)) = hcHigh := by
        funext i; fin_cases i <;> simp [WeightedCallbacks.complementedHigh,hcHigh,chosen,value,hp,negative]
      change Eval complement nc (Memory.state fetched.regs (Product.tapes e) hfHigh)
        (Memory.state rc (Product.tapes e) (WeightedCallbacks.complementedHigh hfHigh
          (Normalize.bytes Squarefree.encodeIndex (negative p t M cache table minusOne one payload)))) at hcomp
      rw [hout] at hcomp
      refine ⟨nc+1,?_,rc,Eval.ite_true (by simpa [Memory.state,hp] using hsign) hcomp⟩
      simpa [hp,negateBudget,hfHigh,literalHigh,hone,hminus,negative,Product.bytes] using Nat.add_le_add_right hnc 1
  obtain ⟨nc,hnc,rc,hchoose⟩ := hchoose
  obtain ⟨np,hnp,rp,hprod⟩ := ProductCallback.eval p t M cache hz table degree width hd hw
    u J left chosen rc hcHigh
    (by simpa [hcHigh,hfHigh,literalHigh] using hleft)
    (by simp [hcHigh]) (by simpa [hcHigh,hfHigh,literalHigh] using htmp)
  let out := outputHigh high lookupTable (Product.bytes (result p t M cache table minusOne one payload left u J positive))
  have hout : ProductCallback.resultHigh hcHigh
      (Product.bytes (Product.run p t M cache table u J left chosen [])) = out := by
    funext i; fin_cases i <;> simp [ProductCallback.resultHigh,hcHigh,hfHigh,literalHigh,outputHigh,out,result,chosen]
  rw [hout] at hprod
  have hreturn := recordReturn_eval (Memory.state rp (Product.tapes e) out)
  refine ⟨nf+nc+np+3,?_,rp,?_⟩
  · dsimp only [budget,result]
    dsimp only [chosen] at hnp
    simp only [Product.bytes] at hnf hnc hnp ⊢
    omega
  · convert hf.seq (hchoose.seq (hprod.seq hreturn)) using 1 <;> first | rfl | omega

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback

/-! Component: HashCircuitProgramClause. All public namespaces and APIs are retained. -/


/-! Typed clause traversal using the fixed native literal callback. Input is
still the original unary literal encoding; the type is used only to specify
which dictionary entry the native decoder and lookup retrieve. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem record_state (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool)
    (acc src payload : List Bool) (v pr f : Bool) :
    RecordPrograms.state literalPorts (base regs e high acc) v pr f src payload =
      Memory.state (Function.update (Function.update (Function.update regs 0 v) 1 pr) 2 f)
        (Product.tapes e) (recordHigh high acc src payload) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.update (Function.update (Memory.tapes (Product.tapes e) (baseHigh high acc))
      (Memory.highPort 7) src) (Memory.highPort 2) payload =
      Memory.tapes (Product.tapes e) (recordHigh high acc src payload)
    rw [Memory.update_high,Memory.update_high]
    rfl

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

theorem callback_eval_oai (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (l : SAT.Literal (Fin n)) (acc : List (Product.Entry n (baseWidth p t) d)) (tail : List Bool) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    ∃ k ≤ cost p t M cache table minusOne one incidence degree u J entries l acc,
      ∃ rr, Eval (literalStep arithmetic) k
        (RecordPrograms.state literalPorts (base regs e high (Product.bytes acc))
          false true false tail (literalBits l).reverse)
        (RecordPrograms.state literalPorts
          (base rr e high (Product.bytes (step p t M cache table minusOne one incidence u J l acc)))
          false true false tail []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let r0 := Function.update (Function.update (Function.update regs 0 false) 1 true) 2 false
  let h0 := recordHigh high (Product.bytes acc) tail (literalBits l).reverse
  obtain ⟨k,hk,rr,he⟩ := LiteralCallback.eval p t M cache table minusOne one (incidence l.variable) acc hz
    degree width hd hw u J l.variable.val l.positive entries r0 h0 (hl l.variable)
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,baseHigh,literalHigh])
    (by simp [h0,recordHigh,literalBits,Encoding.literalCode])
    (by simpa [h0,recordHigh,baseHigh,literalHigh] using ht)
    (by simp [h0,recordHigh,baseHigh])
    (by simpa [h0,recordHigh,baseHigh,literalHigh] using ho)
    (by simpa [h0,recordHigh,baseHigh,literalHigh] using hm)
    (by simpa [h0,recordHigh,baseHigh,literalHigh] using htmp)
  have hh : LiteralCallback.outputHigh h0 (Squarefree.Program.lookupRecords entries)
      (Product.bytes (step p t M cache table minusOne one incidence u J l acc)) =
      recordHigh high (Product.bytes (step p t M cache table minusOne one incidence u J l acc)) tail [] := by
    funext i; fin_cases i <;> simp [LiteralCallback.outputHigh,h0,recordHigh,baseHigh,literalHigh,ht]
  change Eval (literalStep arithmetic) k (Memory.state r0 (Product.tapes e) h0)
    (Memory.state (returned (Memory.state rr (Product.tapes e) h0)).regs (Product.tapes e)
      (LiteralCallback.outputHigh h0 (Squarefree.Program.lookupRecords entries)
        (Product.bytes (step p t M cache table minusOne one incidence u J l acc)))) at he
  rw [hh] at he
  refine ⟨k,hk,rr,?_⟩
  rw [record_state,record_state]
  exact he

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

/-! Component: HashCircuitProgramRow. All public namespaces and APIs are retained. -/


/-! The actual nested hash-row interpreter. The only inputs below are serialized
literal clauses, flat represented scalars, the selected incidence dictionary,
and the ring/cache words used by the native services. -/

/-! Component: HashCircuitProgramRun. All public namespaces and APIs are retained. -/


/-! Compiled fixed-program trace for one serialized sparse hash row. The
initial accumulator is physically cleared, and the final halt is charged. -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval_oai
