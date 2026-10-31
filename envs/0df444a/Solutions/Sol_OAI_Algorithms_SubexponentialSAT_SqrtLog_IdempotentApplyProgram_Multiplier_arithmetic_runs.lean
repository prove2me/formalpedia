-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.arithmetic_runs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:54:48.379895+00:00
-- url     : https://prove2.me/submissions/8f52b876-cab6-4364-9468-47ea3f3625b4

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S146
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_WeightedCallbacks_complement_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_add_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Product_step_eval

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

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native sparse arithmetic services shared by multiplier construction and Horner evaluation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem mul_eval (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data) (ha : high 11=Product.bytes a)
    (hb : high 5=Product.bytes b) (htmp : high 14=[]) :
    ∃ cost ≤ mulCost c a b, ∃ rr,
      Eval (productAdapter product) cost (Memory.state regs (low c) high)
        (Memory.state rr (low c) (binaryResult high (Product.bytes (mul c a b)))) := by
  exact ProductCallback.eval p t c.modulus c.cache c.zeroBound c.table
    (List.replicate d true) c.width (by simp) c.widthLength c.u c.J a b regs high ha hb htmp

theorem add_eval (c : Context p t n d) (a b : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data) (ha : high 11=Product.bytes a)
    (hb : high 5=Product.bytes b) (htmp : high 14=[]) :
    ∃ cost ≤ addCost c a b, ∃ rr,
      Eval add cost (Memory.state regs (low c) high)
        (Memory.state rr (low c) (binaryResult high (Product.bytes (plus c a b)))) := by
  simpa only [addCost, low, plus, addStored, Product.bytes, List.length_replicate] using
    IdempotentApplyProgram.add_eval p t c.modulus c.cache Squarefree.encodeIndex
      Squarefree.encodeIndex_injective (RingTriple.tableEncoding c.table)
      (List.replicate d true) c.width (List.replicate c.u true) (List.replicate c.J true)
      (by simp) c.widthLength a b regs high ha hb htmp


end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKernel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierArithmetic. -/

/-! Native construction of the cubic multiplier before its U shift. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

theorem Runs.seq {a b : Cmd 8 96} {A B : ℕ} {low} {x y z : Data}
    (ha : Runs a A low x y) (hb : Runs b B low y z) :
    Runs (.seq a b) (A+B) low x z := by
  intro regs
  obtain ⟨i,hi,r1,h1⟩:=ha regs
  obtain ⟨j,hj,r2,h2⟩:=hb r1
  exact ⟨i+j,Nat.add_le_add hi hj,r2,h1.seq h2⟩

theorem Runs.skip (low) (high : Data) : Runs (.base .skip) 0 low high high := by
  intro regs
  exact ⟨0,le_rfl,regs,Eval.base (.skip _)⟩

theorem work_update5 (high : Data) (a b c z) :
    Function.update (work high a b c) 5 z=work high z b c := by
  funext i; by_cases h5:i=5 <;> by_cases h11:i=11 <;> by_cases h29:i=29 <;>
    simp_all [work]
theorem work_update11 (high : Data) (a b c z) :
    Function.update (work high a b c) 11 z=work high a z c := by
  funext i; by_cases h5:i=5 <;> by_cases h11:i=11 <;> by_cases h29:i=29 <;>
    simp_all [work,Function.update_apply]
theorem work_update29 (high : Data) (a b c z) :
    Function.update (work high a b c) 29 z=work high a b z := by simp [work]
theorem work_binary (high : Data) (a b c z) :
    binaryResult (work high a b c) z=work high [] z c := by
  simp only [binaryResult,work_update11,work_update5]

/-- All inputs are ordinary stored data. No arithmetic callback premise is used. -/
theorem arithmetic_runs_oai (c : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (high : Data)
    (hh : high 12=Product.bytes h) (ho : high 13=Product.bytes one)
    (hm : high 20=RingProgram.flat minus) (htmp : high 14=[]) :
    Runs arithmetic (arithmeticCost c minus h one) (low c)
      (work high [] [] []) (work high [] (Product.bytes (cubic c minus h one)) []) := by
  let a:=complemented c minus h one
  let b:=plus c a one
  let q:=mul c b a
  let H:=Product.bytes h
  let O:=Product.bytes one
  let A:=Product.bytes a
  let B:=Product.bytes b
  let Q:=Product.bytes q
  let G:=Product.bytes (mul c q h)
  have h61 : (61 : Fin 96) = Memory.highPort 5 := by decide
  have h67 : (67 : Fin 96) = Memory.highPort 11 := by decide
  have h68 : (68 : Fin 96) = Memory.highPort 12 := by decide
  have h69 : (69 : Fin 96) = Memory.highPort 13 := by decide
  have h85 : (85 : Fin 96) = Memory.highPort 29 := by decide
  have hc (src dst : Fin 40) (hsd:src≠dst) (hst:src≠14) (htd:(14:Fin 40)≠dst)
      (x : Data) (hx:x 14=[]) :
      Runs (copy (Memory.highPort src) (Memory.highPort dst) 70)
        (7*(x src).length+5) (low c) x (Function.update x dst (x src++x dst)) := by
    intro regs
    exact ⟨_,le_rfl,_,copy_high_high regs (low c) x src dst 14 hsd hst htd hx⟩
  have he (src : Fin 40) (x : Data) :
      Runs (clear (Memory.highPort src)) (2*(x src).length+3) (low c)
        x (Function.update x src []) := by
    intro regs
    exact ⟨_,le_rfl,_,Memory.clear_high regs (low c) x src⟩
  have h1 : Runs (copy 68 61 70) (7*H.length+5) (low c)
      (work high [] [] []) (work high H [] []) := by
    rw [h68, h61]
    have hh':work high [] [] [] 12=H:=by simpa [work,H] using hh
    simpa only [hh',work_5,List.append_nil,work_update5] using
      hc 12 5 (by decide) (by decide) (by decide) (work high [] [] []) (by simpa [work] using htmp)
  have h2 : Runs complement (complementCost c minus h one) (low c)
      (work high H [] []) (work high A [] []) := by
    intro regs
    have h':=WeightedCallbacks.complement_eval p t c.modulus c.cache c.zeroBound c.table
      minus (List.replicate d true) c.width (List.replicate c.u true) (List.replicate c.J true)
      (by simp) c.widthLength Squarefree.encodeIndex Squarefree.encodeIndex_injective h one regs
      (work high H [] []) (by rfl) (by simpa [work] using hm) (by simpa [work] using ho)
      (by simpa [work] using htmp)
    simpa [low,complementCost,WeightedCallbacks.complementedHigh,work_update5,
      H,A,a,complemented,hm,ho] using h'
  have h3 : Runs (copy 61 85 70) (7*A.length+5) (low c)
      (work high A [] []) (work high A [] A) := by
    rw [h61, h85]
    simpa only [work_5,work_29,List.append_nil,work_update29] using
      hc 5 29 (by decide) (by decide) (by decide) (work high A [] []) (by simpa [work] using htmp)
  have h4 : Runs (copy 61 67 70) (7*A.length+5) (low c)
      (work high A [] A) (work high A A A) := by
    rw [h61, h67]
    simpa only [work_5,work_11,List.append_nil,work_update11] using
      hc 5 11 (by decide) (by decide) (by decide) (work high A [] A) (by simpa [work] using htmp)
  have h5 : Runs (clear 61) (2*A.length+3) (low c)
      (work high A A A) (work high [] A A) := by
    rw [h61]
    simpa only [work_5,work_update5] using he 5 (work high A A A)
  have h6 : Runs (copy 69 61 70) (7*O.length+5) (low c)
      (work high [] A A) (work high O A A) := by
    rw [h69, h61]
    have ho':work high [] A A 13=O:=by simpa [work,O] using ho
    simpa only [ho',work_5,List.append_nil,work_update5] using
      hc 13 5 (by decide) (by decide) (by decide) (work high [] A A) (by simpa [work] using htmp)
  have h7 : Runs add (addCost c a one) (low c)
      (work high O A A) (work high [] B A) := by
    intro regs
    simpa only [work_binary] using Steps.add_eval c a one regs (work high O A A)
      (by rfl) (by rfl) (by simpa [work] using htmp)
  have h8 : Runs (copy 85 61 70) (7*A.length+5) (low c)
      (work high [] B A) (work high A B A) := by
    rw [h85, h61]
    simpa only [work_29,work_5,List.append_nil,work_update5] using
      hc 29 5 (by decide) (by decide) (by decide) (work high [] B A) (by simpa [work] using htmp)
  have h9 : Runs (productAdapter product) (mulCost c b a) (low c)
      (work high A B A) (work high [] Q A) := by
    intro regs
    simpa only [work_binary] using Steps.mul_eval c b a regs (work high A B A)
      (by rfl) (by rfl) (by simpa [work] using htmp)
  have h10 : Runs (clear 85) (2*A.length+3) (low c)
      (work high [] Q A) (work high [] Q []) := by
    rw [h85]
    simpa only [work_29,work_update29] using he 29 (work high [] Q A)
  have h11 : Runs (copy 68 61 70) (7*H.length+5) (low c)
      (work high [] Q []) (work high H Q []) := by
    rw [h68, h61]
    have hh':work high [] Q [] 12=H:=by simpa [work,H] using hh
    simpa only [hh',work_5,List.append_nil,work_update5] using
      hc 12 5 (by decide) (by decide) (by decide) (work high [] Q []) (by simpa [work] using htmp)
  have h12 : Runs (productAdapter product) (mulCost c q h) (low c)
      (work high H Q []) (work high [] G []) := by
    intro regs
    simpa only [work_binary] using Steps.mul_eval c q h regs (work high H Q [])
      (by rfl) (by rfl) (by simpa [work] using htmp)
  have hrun:=h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq
    (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (Runs.skip (low c) (work high [] G [])))))))))))))
  simpa only [arithmetic,sequence,List.foldr_cons,List.foldr_nil,arithmeticCost,
    Nat.add_assoc,Nat.add_zero,cubic,H,O,A,a,b,q,G] using hrun

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplier. -/

/-! Concrete preparation of the stored multiplier used by native Horner evaluation. -/

/-! Source component: IdempotentApplyProgramMultiplierSemantics. -/

/-! The multiplier produced by the native preparation is U H(H-1)(H-2). -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.arithmetic_runs_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.arithmetic_runs_oai
