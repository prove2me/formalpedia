-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:13:42.827248+00:00
-- url     : https://prove2.me/submissions/f5c3e9aa-0ccd-4678-807c-4522cf4f3fbb

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_Row_program_runs
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Multiplier_arithmetic_runs
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Multiplier_shiftU_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Steps_applyLoop_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseLiteralPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Padding arbitrary literal payloads for the dense interpreter

The existing five-label padding table already truncates long inputs. This
module proves that behavior without a length precondition, then connects the
table to the actual framed operand stack. The cached dense zero array supplies
the requested bit width; no dimension is baked into the program control.
-/

namespace SubexponentialSAT.SubexpDenseLiteralPadding

open BitProgram StructuredCalls ModularArithmetic ModularPrograms
open SubexpConvolutionControl (Store Code ExecutesIn)

theorem padding_exit_any (regs : Fin 8 → Bool) (input output : List Bool) :
    Trace paddingProgram 3 (paddingCfg (some 0) regs [] input output)
      (paddingCfg none (readRegs regs 1 3 none) [] input output) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, paddingProgram, execInstr,
    paddingCfg, readRegs, operandStacks, Function.update_apply]

theorem padding_trace_any (regs : Fin 8 → Bool) (shape input output : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace paddingProgram (4 * shape.length + 3)
        (paddingCfg (some 0) regs shape input output)
        (paddingCfg none rf [] (input.drop shape.length) ((padTo shape input).reverse ++ output)) := by
  induction shape generalizing regs input output with
  | nil =>
      refine ⟨readRegs regs 1 3 none, ?_⟩
      simpa [padTo] using padding_exit_any regs input output
  | cons bit shape ih =>
      obtain ⟨rf, ht⟩ := ih (paddingRegs regs bit input) input.tail
        (input.head?.getD false :: output)
      refine ⟨rf, ?_⟩
      have h := (padding_round regs bit shape input output).trans ht
      cases input <;> convert h using 1 <;>
        simp [padTo, List.reverse_cons, List.append_assoc] <;> omega

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct a cached sparse constant from a shape word and a forward flat
coefficient. Zero support bits, key delimiters, reversal, record framing and
cleanup all execute on the native bit machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem padStacks_injective : Function.Injective padStacks := Fin.castAdd_injective _ _

private theorem embedPad (regs rr : Fin 8 → Bool)
    (shape input before coeff rev out shape' input' after : List Bool) :
    embedState id padStacks (data regs shape input before coeff rev out)
      (⟨rr,ModularPrograms.operandStacks shape' input' after⟩ : State 8 3) =
        data rr shape' input' after coeff rev out := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id padStacks_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi; fin_cases i <;> simp_all [padStacks,data,Fin.exists_fin_succ]

theorem pad_eval (regs : Fin 8 → Bool) (shape coeff : List Bool) :
    ∃ rr, Eval pad (4*shape.length+3) (data regs shape [] [] coeff [] [])
      (data rr [] [] (List.replicate shape.length false) coeff [] []) := by
  obtain ⟨rr,h⟩ := SubexponentialSAT.SubexpDenseLiteralPadding.padding_trace_any regs shape [] []
  have ht : Trace ModularPrograms.paddingProgram (4*shape.length+3)
      ((⟨regs,ModularPrograms.operandStacks shape [] []⟩ : State 8 3).withPC
        (some ModularPrograms.paddingProgram.entry))
      ((⟨rr,ModularPrograms.operandStacks [] (([] : List Bool).drop shape.length)
        ((ModularArithmetic.padTo shape []).reverse ++ [])⟩ : State 8 3).withPC none) := by
    simpa [ModularPrograms.paddingCfg,ModularPrograms.paddingProgram,StructuredProgram.State.withPC] using h
  have he := eval_call_lifted ModularPrograms.paddingProgram id padStacks
    (data regs shape [] [] coeff [] []) Function.injective_id padStacks_injective ht
  simp only [embedPad] at he
  have hp : ModularArithmetic.padTo shape [] = List.replicate shape.length false := by
    clear h ht he
    induction shape with
    | nil => rfl
    | cons b shape ih => simpa [ModularArithmetic.padTo,List.replicate_succ] using congrArg (false :: ·) ih
  refine ⟨rr,?_⟩
  simpa [hp] using he

theorem tag_eval (regs : Fin 8 → Bool) (n : ℕ) (coeff : List Bool) :
    Eval tag 3 (data regs [] [] (List.replicate n false) coeff [] [])
      (data (Function.update regs 0 false) [] [] (key n) coeff [] []) := by
  let d := data regs [] [] (List.replicate n false) coeff [] []
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) d)).seq
    ((Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 6) (0 : Fin 8)) _)).seq
      (Eval.base (StructuredProgram.Eval.atom (.push (2 : Fin 6) (0 : Fin 8)) _)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;>
      simp [d,data,key,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr,List.replicate_succ]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

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

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-! Component: HashCircuitProgramClause. All public namespaces and APIs are retained. -/


/-! Typed clause traversal using the fixed native literal callback. Input is
still the original unary literal encoding; the type is used only to specify
which dictionary entry the native decoder and lookup retrieve. -/

/-! Component: HashCircuitProgramRow. All public namespaces and APIs are retained. -/


/-! The actual nested hash-row interpreter. The only inputs below are serialized
literal clauses, flat represented scalars, the selected incidence dictionary,
and the ring/cache words used by the native services. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem record_state (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool)
    (acc src payload : List Bool) (v pr f : Bool) :
    RecordPrograms.state rowPorts (base regs e high acc) v pr f src payload =
      Memory.state (Function.update (Function.update (Function.update regs 0 v) 1 pr) 2 f)
        (Product.tapes e) (recordHigh high acc src payload) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.update (Function.update (Memory.tapes (Product.tapes e) (baseHigh high acc))
      (Memory.highPort 8) src) (Memory.highPort 10) payload =
      Memory.tapes (Product.tapes e) (recordHigh high acc src payload)
    rw [Memory.update_high,Memory.update_high]
    rfl

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

/-! Component: HashCircuitProgramRun. All public namespaces and APIs are retained. -/


/-! Compiled fixed-program trace for one serialized sparse hash row. The
initial accumulator is physically cleared, and the final halt is charged. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierKey. -/

/-! Construction and application of the U monomial by actual native instructions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native


theorem keyPorts_injective : Function.Injective keyPorts := by decide

theorem uKey_encode (n : ℕ) :
    Squarefree.encodeIndex (uKey n)=true :: List.replicate (n+2) false := by
  simp [uKey,Squarefree.encodeIndex,Encoding.encodeNat,Squarefree.encodeMask,
    List.ofFn_const,List.replicate_succ]

private theorem embed_key (regs rr : Fin 8 → Bool) (bank : Fin 96 → List Bool)
    (shape key output shape' key' : List Bool)
    (h90:bank 90=[]) (h81:bank 81=[]) (h92:bank 92=[]) (h93:bank 93=[]) :
    embedState id keyPorts (keyState regs bank shape key output)
      (HashCircuitProgram.Constant.data rr shape' [] key' [] [] [])=keyState rr bank shape' key' output := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id keyPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> simp [keyPorts,keyState,HashCircuitProgram.Constant.data,h90,h81,h92,h93]
  · intro i hi
    have h89:i≠89:=by intro he; apply hi; exact ⟨0,he.symm⟩
    have h91:i≠91:=by intro he; apply hi; exact ⟨2,he.symm⟩
    simp [keyState,Function.update_apply,h89,h91]

/-- The shape tape is preserved; the only resulting stack change is the new U key. -/
theorem makeUKey_command_eval (x : State 8 96)
    (h70:x.stacks 70=[]) (h89:x.stacks 89=[]) (h90:x.stacks 90=[])
    (h91:x.stacks 91=[]) (h81:x.stacks 81=[]) (h92:x.stacks 92=[])
    (h93:x.stacks 93=[]) (h94:x.stacks 94=[]) :
    ∃ rr, Eval makeUKeyCommand (20*(x.stacks 88).length+50) x
      ⟨rr,Function.update x.stacks 94 (Squarefree.encodeIndex (uKey (x.stacks 88).length))⟩ := by
  let shape:=x.stacks 88
  let n:=shape.length
  let r1:=readRegs x.regs 0 1 none
  have h1:=copy_eval x 88 89 70 (by decide) (by decide) (by decide) h70
  have h1' : Eval (copy 88 89 70) (7*n+5) x (keyState r1 x.stacks shape [] []) := by
    convert h1 using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi:i=89 <;> by_cases hj:i=91 <;> by_cases hk:i=94 <;>
        simp_all [copied,StackRoutines.copyStacks,shape]
  obtain ⟨r2,h2⟩:=HashCircuitProgram.Constant.pad_eval r1 shape []
  have h2':=eval_liftCommand h2 0 2 id keyPorts
    (keyState r1 x.stacks shape [] []) Function.injective_id keyPorts_injective
  rw [embed_key _ _ _ _ _ _ _ _ h90 h81 h92 h93,
      embed_key _ _ _ _ _ _ _ _ h90 h81 h92 h93] at h2'
  have h3:=eval_liftCommand (HashCircuitProgram.Constant.tag_eval r2 n []) 2 2 id keyPorts
    (keyState r2 x.stacks [] (List.replicate n false) []) Function.injective_id keyPorts_injective
  rw [embed_key _ _ _ _ _ _ _ _ h90 h81 h92 h93,
      embed_key _ _ _ _ _ _ _ _ h90 h81 h92 h93] at h3
  let r3:=Function.update r2 (0:Fin 8) false
  let r4:=Function.update r3 (0:Fin 8) true
  let z:=Squarefree.encodeIndex (uKey n)
  have h4 : Eval (.base (.atom (.set 0 true))) 1
      (keyState r3 x.stacks [] (HashCircuitProgram.Constant.key n) []) (keyState r4 x.stacks [] (HashCircuitProgram.Constant.key n) []) := by
    exact Eval.base (StructuredProgram.Eval.atom _ _)
  have h5 : Eval (.base (.atom (.push 91 0))) 1
      (keyState r4 x.stacks [] (HashCircuitProgram.Constant.key n) []) (keyState r4 x.stacks [] z []) := by
    have hp:=Eval.base (StructuredProgram.Eval.atom (.push (91:Fin 96) (0:Fin 8))
      (keyState r4 x.stacks [] (HashCircuitProgram.Constant.key n) []))
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi:i=91 <;> by_cases hj:i=94 <;>
        simp [keyState,z,uKey_encode,HashCircuitProgram.Constant.key,r4,Function.update_apply,hi,hj,StructuredProgram.Atom.instr,execInstr]
  let r6:=readRegs r4 0 1 none
  have h6:=copy_eval (keyState r4 x.stacks [] z []) 91 94 70
    (by decide) (by decide) (by decide) (by simpa [keyState] using h70)
  have h6' : Eval (copy 91 94 70) (7*(n+3)+5)
      (keyState r4 x.stacks [] z []) (keyState r6 x.stacks [] z z) := by
    convert h6 using 1
    · simp [keyState,z,Squarefree.encodeIndex_length,uKey]; omega
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; by_cases hi:i=94 <;>
          simp_all [copied,StackRoutines.copyStacks,keyState,Function.update_apply]
  have h7:=clear_eval (keyState r6 x.stacks [] z z) 91
  have h7' : Eval (clear 91) (2*(n+3)+3)
      (keyState r6 x.stacks [] z z) (keyState (readRegs r6 0 1 none) x.stacks [] [] z) := by
    convert h7 using 1
    · simp [keyState,z,Squarefree.encodeIndex_length,uKey]; omega
    · apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; by_cases hi:i=91 <;> by_cases hj:i=94 <;>
          simp [StackRoutines.clearStacks,keyState,Function.update_apply,hi,hj]
  have hrun:=h1'.seq (h2'.seq (h3.seq (h4.seq (h5.seq (h6'.seq
    (h7'.seq (Eval.base (.skip _))))))))
  refine ⟨readRegs r6 0 1 none,?_⟩
  convert hrun using 1
  · rfl
  · dsimp [n, shape]
    omega
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i = 89 <;> by_cases hj : i = 91 <;> by_cases hk : i = 94 <;>
        simp_all [keyState, z, n, shape]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier


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

theorem work_empty (high : Data) (h5:high 5=[]) (h11:high 11=[]) (h29:high 29=[]) :
    work high [] [] []=high := by
  funext i; by_cases h5':i=5 <;> by_cases h11':i=11 <;> by_cases h29':i=29 <;>
    simp_all [work]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native

theorem makeUKey_eval (x : State 8 96)
    (h70:x.stacks 70=[]) (h89:x.stacks 89=[]) (h90:x.stacks 90=[])
    (h91:x.stacks 91=[]) (h81:x.stacks 81=[]) (h92:x.stacks 92=[])
    (h93:x.stacks 93=[]) (h94:x.stacks 94=[]) :
    ∃ rr, Eval makeUKey (20*(x.stacks 88).length+50) x
      ⟨rr,Function.update x.stacks 94 (Squarefree.encodeIndex (uKey (x.stacks 88).length))⟩ := by
  simpa only [makeUKey,makeUKeyCommand,uKeyPorts,keyPorts,sequence] using
    makeUKey_command_eval x h70 h89 h90 h91 h81 h92 h93 h94

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplier. -/

/-! Concrete preparation of the stored multiplier used by native Horner evaluation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem bytes_byteEntries (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    Product.bytes xs=Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (byteEntries xs)) := by
  simp [Product.bytes,Normalize.bytes,byteEntries,Squarefree.KeyMapProgram.encoded,
    Squarefree.Program.encodeDictionary,List.map_map,Function.comp_def]

omit [Fact p.Prime] in
theorem byteEntries_shiftForward (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    byteEntries (shiftForward a u J xs)=Squarefree.KeyMapProgram.mapped a u J (byteEntries xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b,c⟩
    by_cases hk:(a.join b).Kept u J <;>
      simp [shiftForward,byteEntries,Squarefree.KeyMapProgram.mapped,hk] at ih ⊢ <;> exact ih

omit [Fact p.Prime] in
theorem bytes_shifted (c : Context p t n d) (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    Product.bytes (shifted c xs)=Squarefree.Program.rawEntries
      (Squarefree.KeyMapProgram.encoded
        (Squarefree.KeyMapProgram.mapped (uKey n) c.u c.J (byteEntries xs)).reverse) := by
  rw [bytes_byteEntries]
  simp only [shifted,byteEntries,List.map_reverse]
  change Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded
    (byteEntries (shiftForward (uKey n) c.u c.J xs)).reverse)=_
  rw [byteEntries_shiftForward]
  rfl

/-- Sequence composition accounts for the zero-cost final skip explicitly. -/
theorem eval_sequence_append (xs ys : List (Cmd 8 96))
    {i j : ℕ} {x y z : State 8 96}
    (hx : Eval (sequence xs) i x y) (hy : Eval (sequence ys) j y z) :
    Eval (sequence (xs++ys)) (i+j) x z := by
  induction xs generalizing i x with
  | nil =>
    cases hx with
    | base hx => cases hx; simpa [sequence] using hy
  | cons a xs ih =>
    cases hx with
    | seq ha hb =>
      simpa only [sequence,List.cons_append,List.foldr_cons,Nat.add_assoc] using
        ha.seq (ih hb)

/-- Actual native execution from H and cached constants to the computed multiplier.
All low tapes and all high tapes other than output86 and U-key94 are preserved. -/
theorem prepareMultiplier_eval (c : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (ho : high 13=Product.bytes one)
    (hm : high 20=RingProgram.flat minus) (hn:(high 32).length=n) (hc:ready high) :
    ∃ k ≤ prepareCost c minus h one, ∃ rr,
      Eval prepareMultiplier k (Memory.state regs (low c) high)
        (Memory.state rr (low c) (Function.update
          (Function.update high 38 (Squarefree.encodeIndex (uKey n))) 30
            (Product.bytes (prepared c minus h one)))) := by
  let raw:=cubic c minus h one
  let high1:=work high [] (Product.bytes raw) []
  let high2:=Function.update high1 (38:Fin 40) (Squarefree.encodeIndex (uKey n))
  have hempty:work high [] [] []=high:=work_empty high
    (hc 5 (by simp)) (hc 11 (by simp)) (hc 29 (by simp))
  obtain ⟨ka,hka,r1,ha⟩:=arithmetic_runs c minus h one high hh ho hm (hc 14 (by simp)) regs
  rw [hempty] at ha
  obtain ⟨r2,hk⟩:=makeUKey_eval (Memory.state r1 (low c) high1)
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 14) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 14 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 33) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 33 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 34) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 34 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 35) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 35 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 25) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 25 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 36) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 36 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 37) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 37 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 38) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 38 (by simp))
  have hn1:((Memory.state r1 (low c) high1).stacks 88).length = n := by
    change (Memory.tapes (low c) high1 (Memory.highPort 32)).length = n
    rw [Memory.tapes_high]
    simpa [high1,work] using hn
  rw [hn1] at hk
  change Eval makeUKey (20*n+50) (Memory.state r1 (low c) high1)
    ⟨r2,Function.update (Memory.tapes (low c) high1) (Memory.highPort 38)
      (Squarefree.encodeIndex (uKey n))⟩ at hk
  rw [Memory.update_high] at hk
  change Eval makeUKey (20*n+50) (Memory.state r1 (low c) high1)
    (Memory.state r2 (low c) high2) at hk
  have hclean : ∀ i ∈ ([80,81,82,83,84,85,89,90,91,92]:List (Fin 96)),
      (Memory.state r2 (low c) high2).stacks i=[] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · change Memory.tapes (low c) high2 (Memory.highPort 24)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 24 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 25)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 25 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 26)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 26 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 27)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 27 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 28)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 28 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 29)=[]
      rw [Memory.tapes_high]
      simp [high2,high1,work]
    · change Memory.tapes (low c) high2 (Memory.highPort 33)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 33 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 34)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 34 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 35)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 35 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 36)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 36 (by simp)
  obtain ⟨ks,hks,r3,hs⟩:=shiftU_eval (uKey n) c.u c.J (byteEntries raw)
    (Memory.state r2 (low c) high2)
    (by
      change Memory.tapes (low c) high2 (Memory.highPort 11) = _
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using bytes_byteEntries raw)
    (by
      change Memory.tapes (low c) high2 (Memory.highPort 38)=_
      rw [Memory.tapes_high]
      simp [high2]) (by rfl) (by rfl) hclean
  change Eval shiftU ks (Memory.state r2 (low c) high2)
    ⟨r3,Function.update (Function.update (Memory.tapes (low c) high2)
      (Memory.highPort 11) []) (Memory.highPort 30)
      (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded
        (Squarefree.KeyMapProgram.mapped (uKey n) c.u c.J (byteEntries raw)).reverse)++high2 30)⟩ at hs
  rw [Memory.update_high,Memory.update_high] at hs
  have h30:high2 30=[]:=by simpa [high2,high1,work] using hc 30 (by simp)
  have hresult : Function.update (Function.update high2 11 []) 30
      (Product.bytes (prepared c minus h one)) =
      Function.update (Function.update high 38 (Squarefree.encodeIndex (uKey n))) 30
      (Product.bytes (prepared c minus h one)) := by
    funext i
    by_cases hi:i=30 <;> by_cases hj:i=38 <;> by_cases ha:i=5 <;>
      by_cases hb:i=11 <;> by_cases hsave:i=29 <;>
      simp [high2,high1,work,hi,hj,ha,hb,hsave,hc 5 (by simp),hc 11 (by simp),hc 29 (by simp)]
  have hs' : Eval shiftU ks (Memory.state r2 (low c) high2)
      (Memory.state r3 (low c) (Function.update (Function.update high 38
        (Squarefree.encodeIndex (uKey n))) 30 (Product.bytes (prepared c minus h one)))) := by
    rw [h30,List.append_nil,←bytes_shifted c raw] at hs
    change Eval shiftU ks (Memory.state r2 (low c) high2)
      (Memory.state r3 (low c) (Function.update (Function.update high2 11 []) 30
        (Product.bytes (prepared c minus h one)))) at hs
    rw [hresult] at hs
    exact hs
  have htail:=hk.seq (hs'.seq (Eval.base (.skip _)))
  have hrun:=eval_sequence_append
    [copy 68 61 70, complement,copy 61 85 70,copy 61 67 70,clear 61,
      copy 69 61 70,add,copy 85 61 70,productAdapter product,clear 85,
      copy 68 61 70,productAdapter product] [makeUKey,shiftU] ha htail
  refine ⟨ka+(20*n+50+(ks+0)),?_,r3,?_⟩
  · dsimp only [raw] at hks
    dsimp only [prepareCost]
    omega
  · exact hrun

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplierSemantics. -/

/-! The multiplier produced by the native preparation is U H(H-1)(H-2). -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full native application of a computed idempotent coefficient array.
The multiplier is built from H and ordinary cached constants; the indicator
is then computed by the measured Horner loop. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

/-- No desired polynomial is supplied to the command: only H, scalar constants,
and the computed base-coefficient tape occur in the initial memory contract. -/
theorem command_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (ho : high 13=Product.bytes one)
    (hm : high 20=RingProgram.flat minus) (htape : high 22=triplesTape vs)
    (h23 : high 23=[]) (hshape : (high 32).length=n) (hready : Multiplier.ready high) :
    ∃ cost, cost+1 ≤ applicationBudget ctx minus h one vs ∧ ∃ rr,
      Eval command cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx) (Function.update high 11 (Product.bytes (applied ctx minus h one vs)))) := by
  obtain ⟨kp,bp,rp,ep⟩:=Multiplier.prepareMultiplier_eval ctx minus h one regs high hh ho hm hshape hready
  let prepared:=Multiplier.prepared ctx minus h one
  let mid:=Function.update (Function.update high (38:Fin 40)
    (Squarefree.encodeIndex (Multiplier.uKey n))) 30 (Product.bytes prepared)
  have rmid : scalarReady 11 mid := by
    simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false]
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply hready <;> simp
  obtain ⟨kl,bl,rl,el⟩:=applyLoop_eval ctx hd hB h prepared vs rp mid
    (by simpa [mid] using hh) (by simp [mid])
    (by simpa [mid] using htape) (by simpa [mid] using hready 5 (by simp))
    (by simpa [mid] using h23) (by simpa [mid] using hready 28 (by simp))
    (by simpa [mid] using hready 29 (by simp))
    (by simpa [mid] using hready 31 (by simp))
    (by simpa [mid] using hshape) rmid
  have hout : Function.update (Function.update (Function.update mid 30 []) 38 []) 11
      (Product.bytes (loopResult ctx h prepared vs.reverse []))=
      Function.update high 11 (Product.bytes (applied ctx minus h one vs)) := by
    have h30:=hready 30 (by simp)
    have h38:=hready 38 (by simp)
    funext i
    by_cases hi : i=30 <;> by_cases hj : i=38 <;> by_cases hk : i=11 <;>
      simp_all [mid,applied,prepared,Function.update_apply]
  rw [hout] at el
  refine ⟨kp+kl,?_,rl,ep.seq el⟩
  have hkey : mid 38=Squarefree.encodeIndex (Multiplier.uKey n):=by simp [mid]
  rw [hkey] at bl
  dsimp [applicationBudget,prepared] at bp bl ⊢
  omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIndicator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A closed native sparse-hash indicator service. It first interprets the
actual inline weighted-clause row and then applies the computed idempotent
coefficient tape. The resulting indicator is never supplied as input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Indicator

attribute [local simp] Fin.addCases

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

theorem record_apply_ready (high : Fin 40 → List Bool) (hash : List Bool)
    (hready : IdempotentApplyProgram.Multiplier.ready high) :
    IdempotentApplyProgram.Multiplier.ready (Row.recordHigh high hash [] []) := by
  intro i hi
  have h := hready i hi
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | rfl | simpa [Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using h

/-- Both constituent executions are derived from their concrete native
programs. All dimensions, clauses, and coefficients remain runtime data. -/
theorem command_eval_oai {p t n d : ℕ} [Fact p.Prime] (ctx : Context p t n d)
    (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minus)
    (htape : high 22 = IdempotentApplyProgram.triplesTape digits)
    (h23 : high 23 = []) (hshape : (high 32).length = n)
    (hready : IdempotentApplyProgram.Multiplier.ready high) :
    let e := Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
      (RingTriple.tableEncoding ctx.table) (List.replicate d true)
      (List.replicate ctx.u true) (List.replicate ctx.J true)
    ∃ k rr, k ≤ 7 + DynamicFold.work Row.payload
        (Row.value p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J)
        (Row.cost p t ctx.modulus ctx.cache ctx.table minus one incidence
          (List.replicate d true) ctx.u ctx.J entries) ws [] +
        IdempotentApplyProgram.applicationBudget ctx minus (rawHash ctx minus one incidence ws) one digits ∧
      Eval command k
        (RecordPrograms.state rowPorts (Row.base regs e high []) false true false
          (Encoding.encodeList id (ws.map Row.payload)) [])
        (Memory.state rr (low ctx) (Function.update
          (Row.recordHigh high (Product.bytes (rawHash ctx minus one incidence ws)) [] [])
          11 (Product.bytes (result ctx minus one incidence ws digits)))) := by
  dsimp only
  let e := Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
    (RingTriple.tableEncoding ctx.table) (List.replicate d true)
    (List.replicate ctx.u true) (List.replicate ctx.J true)
  let h := rawHash ctx minus one incidence ws
  have htmp : high 14 = [] := hready 14 (by simp)
  obtain ⟨r1,k1,hk1,he1⟩ := Row.program_runs p t ctx.modulus ctx.cache ctx.table minus one incidence
    (List.replicate d true) ctx.u ctx.J entries ctx.zeroBound ctx.width (by simp) ctx.widthLength
    hl regs high ht ho hm htmp ws
  have first : Eval (.call HashCircuitProgram.Native.program) k1
      (RecordPrograms.state rowPorts (Row.base regs e high []) false true false
        (Encoding.encodeList id (ws.map Row.payload)) [])
      (Memory.state (Function.update (Function.update (Function.update r1 0 false) 1 true) 2 false)
        (low ctx) (Row.recordHigh high (Product.bytes h) [] [])) := by
    have he := Eval.call HashCircuitProgram.Native.program he1
    change Eval (.call HashCircuitProgram.Native.program) k1
      (RecordPrograms.state rowPorts (Row.base regs e high []) false true false
        (Encoding.encodeList id (ws.map Row.payload)) [])
      (RecordPrograms.state rowPorts (Row.base r1 e high (Product.bytes h)) false true false [] []) at he
    rw [Row.record_state r1 e high (Product.bytes h) [] [] false true false] at he
    exact he
  let middle := Row.recordHigh high (Product.bytes h) [] []
  obtain ⟨k2,hk2,r2,he2⟩ := IdempotentApplyProgram.command_eval ctx hd hB minus h one digits
    (Function.update (Function.update (Function.update r1 0 false) 1 true) 2 false) middle
    (by simp [middle,Row.recordHigh,Row.baseHigh])
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using ho)
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using hm)
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using htape)
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using h23)
    (by simpa [middle,Row.recordHigh,Row.baseHigh,Clause.baseHigh,literalHigh] using hshape)
    (record_apply_ready high (Product.bytes h) hready)
  dsimp only [h] at hk2
  refine ⟨k1+k2,r2,by omega,?_⟩
  exact first.seq he2

end SubexponentialSAT.SqrtLog.LeafProgram.Indicator

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval_oai
