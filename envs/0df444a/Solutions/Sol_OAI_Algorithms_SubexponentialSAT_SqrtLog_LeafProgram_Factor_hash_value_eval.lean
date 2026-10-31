-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:12:25.863024+00:00
-- url     : https://prove2.me/submissions/f3e5d002-3697-4618-b328-62bffef67324

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_marked_tail_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Indicator_command_eval

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentSetupProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete storage and framed service calls for each head assignment. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem clear_eval (a : Data) (src : Fin 768) :
    Eval (clear src) (2*(a.stacks src).length+3) a (cleared a src) := by
  apply Eval.call
  have he := halt_after_trace _
    (clearProgram_trace src (0 : Fin 40) 1 a.regs a.stacks) 2 rfl rfl
  simpa [cleared,clearResult,clearStacks,StructuredProgram.State.withPC,clearProgram,
    Nat.add_assoc] using he

end SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Wide native factor arithmetic and paid tape movement. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls


theorem nativeRegisters_injective : Function.Injective nativeRegisters :=
  Fin.castAdd_injective 8 32
theorem nativeStacks_injective : Function.Injective nativeStacks :=
  Fin.castAdd_injective 96 672


end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed per-assignment factor evaluation. Factors are dispatched by runtime
ID; hash rows are expanded and tested by the computed idempotent, the marked
clause is multiplied directly, and added neutral factors contribute one.
Every operation below is an actual finite instruction table or native loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

theorem indicatorStacks_injective : Function.Injective indicatorStacks :=
  (Equiv.swap 78 143).injective.comp nativeStacks_injective

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid cleanup and multiplication after a real factor service. The running
product remains on151 and all source/cache tapes are framed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native

theorem clear_eval (a : Data) (i : Fin 768) :
    Eval (clear i) (2*(a.stacks i).length+3) a (cleared a i) :=
  LeafAssignmentSetupProgram.clear_eval a i

theorem lowReady_clear (a : Data) (e : MomentsProgram.Product.Store)
    (h : lowReady a e) (j : Fin 768) (hj : 56 ≤ j.val) :
    lowReady (cleared a j) e := by
  intro i
  have hn : nativeStacks (Memory.lowPort i) ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change i.val=j.val at hv
    omega
  simpa only [cleared,LeafAssignmentSetupProgram.cleared,Function.update_of_ne hn] using h i

theorem hash_tail_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (u J : ℕ) (seed factor : List (MomentsProgram.Product.Entry n (baseWidth p t) d))
    (a : Data)
    (hlo : lowReady a (MomentsProgram.Product.idle M.bits width cache.zero.val
      (RingTriple.tableEncoding table) degree (List.replicate u true) (List.replicate J true)))
    (hseed : a.stacks 151=MomentsProgram.Product.bytes seed)
    (hfactor : a.stacks 67=MomentsProgram.Product.bytes factor)
    (h61 : a.stacks 61=[]) (h70 : a.stacks 70=[]) (h159 : a.stacks 159=[]) :
    let result := MomentsProgram.Product.run p t M cache table u J seed factor []
    ∃ k b, k ≤ 2*(a.stacks 68).length+2*(a.stacks 62).length+6+
        productBudget p t M cache table u J seed factor ∧
      Eval (.seq (clear 68) (.seq (clear 62) accumulate)) k a b ∧
      b.stacks=Function.update (Function.update (Function.update
        (Function.update a.stacks 68 []) 62 []) 67 []) 151 (MomentsProgram.Product.bytes result) := by
  dsimp only
  let c := cleared a 68
  obtain ⟨k,b,hk,he,hb⟩ := marked_tail_eval p t M cache hz table degree width hd hw u J seed factor c
    (lowReady_clear a _ hlo 68 (by decide))
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using hseed)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using hfactor)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h61)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h70)
    (by simpa [c,cleared,LeafAssignmentSetupProgram.cleared] using h159)
  have hc : c.stacks 62=a.stacks 62 := by simp [c,LeafAssignmentSetupProgram.cleared]
  rw [hc] at hk
  exact ⟨_,b,by omega,(clear_eval a 68).seq he,hb⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorServicesBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact framing tools for the fixed wide indicator and marked-clause calls.
The functions below only describe states; executable code remains Factor's
already defined finite service tables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorServices
open SubexponentialSAT BitProgram StructuredCalls
open HashCircuitProgram HashCircuitProgram.Native

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

theorem ready_eval (a : Data) : Eval Factor.indicatorReady 3 a (readied a) := by
  let a1 : Data := ⟨Function.update a.regs 0 false,a.stacks⟩
  let a2 : Data := ⟨Function.update a1.regs 1 true,a.stacks⟩
  have h1 : Eval (.base (.atom (.set 0 false))) 1 a a1 :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  have h2 : Eval (.base (.atom (.set 1 true))) 1 a1 a2 :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  have h3 : Eval (.base (.atom (.set 2 false))) 1 a2 (readied a) :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  exact h1.seq (h2.seq h3)

theorem input_tapes (map : Fin 96 → Fin 768) (a : Data) (lo : Fin 56 → List Bool)
    (hlow : ∀ i, a.stacks (map (Memory.lowPort i))=lo i) :
    Memory.tapes lo (high map a) = a.stacks ∘ map := by
  funext i
  induction i using (Fin.addCases (m:=56) (n:=40)) with
  | left i =>
    change Memory.tapes lo (high map a) (Memory.lowPort i)=a.stacks (map (Memory.lowPort i))
    simpa only [Memory.tapes_low] using (hlow i).symm
  | right i =>
    change Memory.tapes lo (high map a) (Memory.highPort i)=a.stacks (map (Memory.highPort i))
    simp only [Memory.tapes_high,high]

theorem row_high_input (map : Fin 96 → Fin 768) (a : Data) (source : List Bool)
    (hs : a.stacks (map 64)=source)
    (hw : ∀ i∈indicatorScratch,a.stacks (map i)=[]) :
    Row.recordHigh (high map a) [] source [] = high map a := by
  funext i
  fin_cases i <;> simp [Row.recordHigh,Row.baseHigh,HashCircuitProgram.Native.Clause.baseHigh,literalHigh,high]
  all_goals first | exact hs | exact hs.symm | (apply hw; decide)

theorem row_output_tapes (lo : Fin 56 → List Bool) (h : Fin 40 → List Bool)
    (source hash result : List Bool) :
    Memory.tapes lo (Function.update (Row.recordHigh h hash [] []) 11 result) =
      Function.update (Function.update (Function.update
        (Memory.tapes lo (Row.recordHigh h [] source [])) 64 []) 67 result) 68 hash := by
  change _ = Function.update (Function.update (Function.update
    (Memory.tapes lo (Row.recordHigh h [] source [])) (Memory.highPort 8) [])
      (Memory.highPort 11) result) (Memory.highPort 12) hash
  rw [Memory.update_high,Memory.update_high,Memory.update_high]
  apply congrArg (Memory.tapes lo)
  funext i
  fin_cases i <;> simp [Row.recordHigh,Row.baseHigh,HashCircuitProgram.Native.Clause.baseHigh,literalHigh]

theorem extend_project (map : Fin 96 → Fin 768) (hm : Function.Injective map) (a : Data) :
    Function.extend map (a.stacks ∘ map) a.stacks = a.stacks := by
  exact congrArg (fun b : Data => b.stacks)
    (embedState_project Factor.nativeRegisters map a Factor.nativeRegisters_injective hm)

theorem indicator_embed (a : Data) (rr : Fin 8 → Bool) (lo : Fin 56 → List Bool)
    (source hash result : List Bool)
    (hi : Memory.tapes lo (Row.recordHigh (high Factor.indicatorStacks a) [] source [])=
      a.stacks ∘ Factor.indicatorStacks) :
    embedState Factor.nativeRegisters Factor.indicatorStacks (readied a)
      (Memory.state rr lo (Function.update (Row.recordHigh (high Factor.indicatorStacks a) hash [] []) 11 result)) =
      indicatorFinished a rr hash result := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.extend Factor.indicatorStacks
      (Memory.tapes lo (Function.update (Row.recordHigh (high Factor.indicatorStacks a) hash [] []) 11 result))
      a.stacks = _
    rw [row_output_tapes lo _ source hash result,hi]
    rw [ProgramLinking.extend_update Factor.indicatorStacks_injective,
      ProgramLinking.extend_update Factor.indicatorStacks_injective,
      ProgramLinking.extend_update Factor.indicatorStacks_injective,extend_project]
    rfl
    exact Factor.indicatorStacks_injective

end SubexponentialSAT.SqrtLog.LeafProgram.FactorServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual wide factor service calls, including the indicator's three parser
register writes, compiled returns, and exact caller frame. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorServices
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

variable {p t n d : ℕ} [Fact p.Prime]

theorem indicator_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (a : Factor.Data)
    (hlow : ∀ i, a.stacks (Factor.indicatorStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 64=Encoding.encodeList id (ws.map Row.payload))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (htape : a.stacks 143=IdempotentApplyProgram.triplesTape digits)
    (hshape : (a.stacks 88).length=n)
    (hwork : ∀ i∈indicatorScratch,a.stacks (Factor.indicatorStacks i)=[]) :
    ∃ k rr, k ≤ indicatorBudget ctx minus one incidence entries ws digits ∧
      Eval Factor.indicator k a (indicatorFinished a rr
        (Product.bytes (Indicator.rawHash ctx minus one incidence ws))
        (Product.bytes (Indicator.result ctx minus one incidence ws digits))) := by
  let h := high Factor.indicatorStacks a
  let source := Encoding.encodeList id (ws.map Row.payload)
  have hready : IdempotentApplyProgram.Multiplier.ready h := by
    intro i hi
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals (apply hwork; decide)
  have hinput : Memory.tapes (low ctx) (Row.recordHigh h [] source [])=a.stacks ∘ Factor.indicatorStacks := by
    rw [row_high_input Factor.indicatorStacks a source hsource hwork]
    exact input_tapes Factor.indicatorStacks a (low ctx) hlow
  obtain ⟨k,rr,hk,he⟩ := Indicator.command_eval ctx hd hB minus one incidence entries hl ws digits
    (a.regs ∘ Factor.nativeRegisters) h
    (by exact htable) (by exact hone) (by exact hminus) (by exact htape)
    (by exact hwork 79 (by decide)) (by exact hshape) hready
  have hproject : projectState Factor.nativeRegisters Factor.indicatorStacks (readied a)=
      RecordPrograms.state rowPorts
        (Row.base (a.regs ∘ Factor.nativeRegisters)
          (Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
            (RingTriple.tableEncoding ctx.table) (List.replicate d true)
            (List.replicate ctx.u true) (List.replicate ctx.J true)) h [])
        false true false source [] := by
    rw [Row.record_state]
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [readied,Factor.nativeRegisters]
    · exact hinput.symm
  dsimp only [source] at hproject
  rw [← hproject] at he
  have hc := eval_liftCommand_from_state Indicator.command 64 67 Factor.nativeRegisters
    Factor.indicatorStacks (readied a) Factor.nativeRegisters_injective Factor.indicatorStacks_injective he
  rw [indicator_embed a rr (low ctx) source _ _ hinput] at hc
  refine ⟨3+(k+1),rr,?_,(ready_eval a).seq hc⟩
  unfold indicatorBudget
  omega

theorem indicator_frame (a : Factor.Data) (rr : Fin 8 → Bool) (hash result : List Bool)
    (i : Fin 768) (h64 : i≠64) (h67 : i≠67) (h68 : i≠68) :
    (indicatorFinished a rr hash result).stacks i=a.stacks i := by
  simp [indicatorFinished,h64,h67,h68]

@[simp] theorem indicator_theta (a : Factor.Data) (rr : Fin 8 → Bool) (hash result : List Bool) :
    (indicatorFinished a rr hash result).stacks 78=a.stacks 78 :=
  indicator_frame a rr hash result 78 (by decide) (by decide) (by decide)

@[simp] theorem indicator_index (a : Factor.Data) (rr : Fin 8 → Bool) (hash result : List Bool) :
    (indicatorFinished a rr hash result).stacks 307=a.stacks 307 :=
  indicator_frame a rr hash result 307 (by decide) (by decide) (by decide)

end SubexponentialSAT.SqrtLog.LeafProgram.FactorServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Execution of the computed factor value and its multiplication into the
current head product. Input incidence dictionaries are the physically
produced tables supplied by the preceding service. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem low_ne (i : Fin 56) (j : Fin 768) (hj : 56 ≤ j.val) :
    nativeStacks (Memory.lowPort i)  ≠  j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=j.val at hv
  omega

theorem indicatorStacks_low (i : Fin 56) :
    indicatorStacks (Memory.lowPort i)=nativeStacks (Memory.lowPort i) := by
  have h78 := low_ne i 78 (by decide)
  have h143 := low_ne i 143 (by decide)
  simp [indicatorStacks,Equiv.swap_apply_def,h78,h143]

omit [Fact (Nat.Prime p)] in
private theorem indicator_lowReady (ctx : Context p t n d) (a : Data)
    (rr : Fin 8 → Bool) (hash result : List Bool)
    (hlow : ∀ i,a.stacks (indicatorStacks (Memory.lowPort i))=low ctx i) :
    lowReady (FactorServices.indicatorFinished a rr hash result)
      (Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
        (RingTriple.tableEncoding ctx.table) (List.replicate d true)
        (List.replicate ctx.u true) (List.replicate ctx.J true)) := by
  intro i
  rw [FactorServices.indicator_frame _ _ _ _ _ (low_ne i 64 (by decide))
    (low_ne i 67 (by decide)) (low_ne i 68 (by decide))]
  simpa only [indicatorStacks_low, low] using hlow i

/-- The native indicator is applied to the actual expanded row, then its
result is multiplied into151. The old hash and incidence table are cleared. -/
theorem hash_value_eval_oai (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n,entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (a : Data)
    (hlow : ∀ i,a.stacks (indicatorStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 64=Encoding.encodeList id (ws.map Row.payload))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (htape : a.stacks 143=IdempotentApplyProgram.triplesTape digits)
    (hshape : (a.stacks 88).length=n)
    (hwork : ∀ i ∈ FactorServices.indicatorScratch,a.stacks (indicatorStacks i)=[])
    (hseed : a.stacks 151=Product.bytes seed) (htmp : a.stacks 159=[]) :
    let factor := Indicator.result ctx minus one incidence ws digits
    let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor []
    ∃ k b,k ≤ FactorServices.indicatorBudget ctx minus one incidence entries ws digits+
        (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
          2*(a.stacks 62).length+6+productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor) ∧
      Eval (.seq indicator (.seq (clear 68) (.seq (clear 62) accumulate))) k a b ∧
      b.stacks=Function.update (Function.update (Function.update (Function.update
        (Function.update a.stacks 64 []) 67 []) 68 []) 62 []) 151 (Product.bytes result) := by
  dsimp only
  obtain ⟨ki,ri,hki,hi⟩ := FactorServices.indicator_eval ctx hd hB minus one incidence entries hl
    ws digits a hlow hsource htable hone hminus htape hshape hwork
  let mid := FactorServices.indicatorFinished a ri
    (Product.bytes (Indicator.rawHash ctx minus one incidence ws))
    (Product.bytes (Indicator.result ctx minus one incidence ws digits))
  have h61 : a.stacks 61=[] := by
    simpa only [show indicatorStacks 61 = 61 by decide] using hwork 61 (by decide)
  have h70 : a.stacks 70=[] := by
    simpa only [show indicatorStacks 70 = 70 by decide] using hwork 70 (by decide)
  obtain ⟨kt,b,hkt,ht,hb⟩ := hash_tail_eval p t ctx.modulus ctx.cache ctx.zeroBound ctx.table
    (List.replicate d true) ctx.width (by simp) ctx.widthLength ctx.u ctx.J seed
    (Indicator.result ctx minus one incidence ws digits) mid
    (indicator_lowReady ctx a ri _ _ hlow)
    (by simpa [mid,FactorServices.indicatorFinished] using hseed)
    (by simp [mid,FactorServices.indicatorFinished])
    (by simpa [mid,FactorServices.indicatorFinished] using h61)
    (by simpa [mid,FactorServices.indicatorFinished] using h70)
    (by simpa [mid,FactorServices.indicatorFinished] using htmp)
  have hm68 : mid.stacks 68=Product.bytes (Indicator.rawHash ctx minus one incidence ws) := by
    simp [mid,FactorServices.indicatorFinished]
  have hm62 : mid.stacks 62=a.stacks 62 := by simp [mid,FactorServices.indicatorFinished]
  rw [hm68,hm62] at hkt
  refine ⟨ki+kt,b,by omega,hi.seq ht,?_⟩
  rw [hb]
  funext i
  by_cases h64 : i=64 <;> by_cases h67 : i=67 <;> by_cases h68 : i=68 <;>
    by_cases h62 : i=62 <;> by_cases h151 : i=151 <;>
    simp [mid,FactorServices.indicatorFinished,h64,h67,h68,h62,h151]


end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval_oai
