-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:23:33.424438+00:00
-- url     : https://prove2.me/submissions/cf1b6e9c-36dd-4353-9f06-7ddb87beee87

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches_hashFactor_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches_markedFactor_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_Input_payload_correct
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_dispatch_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_hash_step_value
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_marked_step_value
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_neutral_callback_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSparsifyEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact syntax and normalization bridges for the word-based node search. -/

namespace SubexponentialSAT.ExecSparsifyEncoding

open ExecCNF ExecSunflowerCodeTransport

theorem encodeList_map {α β : Type*} (f : α → β) (enc : β → List Bool) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

end SubexponentialSAT.ExecSparsifyEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Public raw-input ABI and the uniform paid execution theorem. All control
tables are fixed independently of source size, raw tuple length and ring width.
Repeated source references and zero coefficients remain separate records. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem original_payload_length_le (clauses : List (List Bool)) (p : List Bool)
    (hp : p∈clauses) : p.length ≤ (Encoding.encodeList id clauses).length := by
  induction clauses with
  | nil => simp at hp
  | cons q qs ih =>
      have hq := Encoding.length_frame q
      simp only [Encoding.encodeList,id_eq,Encoding.length_frame,List.length_cons,List.length_append] at *
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · have hh := ih hp
        omega

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramOrigin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-clause provenance for a raw tuple, including repetitions.
The integer lift is taken BEFORE the tuple terms are added; its reduction, not
its value in the thickened ring, equals the combined ternary selector row. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open scoped BigOperators
open LeafProgram

/-- Original literal byte order is retained, including repeated literals. -/
theorem clausePayload_codes {n : ℕ} (ls : List (SAT.Literal (Fin n))) :
    clausePayload ls = Encoding.encodeList Encoding.encodeNat (ls.map Encoding.literalCode) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      change true :: (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++
        clausePayload ls) = _
      simp only [List.map_cons,Encoding.encodeList]
      rw [ih]

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor dispatcher in the native leaf's actual bank.  The parsed ID
is retained for incidence preparation.  The mark flag is read from a tape,
not inserted as a program parameter. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem stackMap_injective : Function.Injective stackMap := by decide

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

open BitProgram StructuredCalls SubexpScanPrimitives


theorem payload_length_le (records : List (List Bool × List Bool)) (query payload : List Bool)
    (h : records.lookup query = some payload) :
    payload.length ≤ (SelectorProgram.rawRecords records).length := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp [SelectorProgram.rawRecords, List.flatMap_append]
  omega

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem lookup_eq (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (hvertex : Function.Injective encodeVertex) (v : V) :
    (records P encodeVertex encodeType).lookup (encodeVertex v) =
      some (value P encodeType v).encode :=
  lookup_graph_encoded _ _ _ hvertex v
    (by simpa using PackingReorder.mem_storageVertices P v)

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem stream_length (ps : List (ℕ × ℕ)) :
    (stream ps).length=8*mass ps+24*ps.length+1 := by
  induction ps with
  | nil => simp [stream,Encoding.encodeList,mass]
  | cons p ps ih =>
      change (true::(Encoding.frame (pairPayload p.1 p.2)++stream ps)).length=_
      simp only [List.length_cons,List.length_append,Encoding.length_frame,pairPayload_length,ih]
      simp only [mass,List.map_cons,List.sum_cons]
      unfold mass at ih
      omega

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem mem_workerPorts (i : Fin 768) : i ∈ workerPorts ↔ 340 ≤ i.val ∧ i.val < 680 := by
  simp only [workerPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=i.val at hv
    omega
  · intro hi
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem basePort_protected (i : Fin 768) :
    basePort i ≠ 640 ∧ basePort i ≠ 641 ∧ basePort i ≠ 642 ∧ basePort i ≠ 647 ∧
      basePort i ≠ 650 ∧ basePort i ≠ 651 ∧ basePort i ≠ 670 ∧ basePort i ≠ 671 := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem basePort_high (i : Fin 768) :
    (basePort i).val < 768 ∨ (885 ≤ (basePort i).val ∧ (basePort i).val ≤ 892) := by
  simp only [basePort]
  split_ifs <;> simp_all only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] <;> omega

theorem basePort_outside (i : Fin 896)
    (hi : i ∈ protectedPorts ∨ (768 ≤ i.val ∧ (i.val < 885 ∨ 892 < i.val))) :
    ¬ ∃ j, basePort j = i := by
  rintro ⟨j, hj⟩
  rcases hi with hi | hi
  · simp only [protectedPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    have hp := basePort_protected j
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.1 hj
    · exact hp.2.1 hj
    · exact hp.2.2.1 hj
    · exact hp.2.2.2.1 hj
    · exact hp.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.2 hj
  · have hm := basePort_high j
    rw [hj] at hm
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorDispatchFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte-store frame for the paid factor dispatcher. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem finished_stacks (a : Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hwork : ∀ i ∈ scratch, a.stacks i = []) :
    (finished a rf rows clauses marked mark factor).stacks =
      Function.update a.stacks 154
        (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor) := by
  funext i
  by_cases hin : ∃ j, stackMap j = i
  · obtain ⟨j,rfl⟩ := hin
    rw [show (finished a rf rows clauses marked mark factor).stacks (stackMap j) =
        LeafFactorDispatchProgram.outputStacks rows clauses marked mark factor j from
      embedState_stack register stackMap (staged a) _ stackMap_injective j]
    fin_cases j <;>
      simp_all [stackMap,LeafFactorDispatchProgram.outputStacks,
        LeafFactorDispatchProgram.baseStacks,LeafFactorDispatchProgram.unary,scratch]
  · have h152 : i ≠ 152 := by intro h; subst i; exact hin ⟨2,rfl⟩
    have h154 : i ≠ 154 := by intro h; subst i; exact hin ⟨15,rfl⟩
    rw [show (finished a rf rows clauses marked mark factor).stacks i = (staged a).stacks i from
      embedState_stack_frame register stackMap (staged a) _ i hin]
    simp [staged,copied,afterCopy,StackRoutines.copyStacks,h152,h154]

end SubexponentialSAT.SqrtLog.LeafProgram.FactorDispatch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

theorem clear_eval (a : Data) (src : Fin 896) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  Eval.call _ (ListRegisterProgram.clear_run src (0 : Fin 40) 1 a.regs a.stacks)

theorem clearCallback_eval (a : Data) :
    Eval clearCallback (clearCallbackCost a) a (callbackInitial a) :=
  eval_liftCommand_from_state clearCallbackLocal 149 149 localRegister lowStack a
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)
    (clearMany_eval callbackScratch (projectState localRegister lowStack a))

theorem callbackInitial_low (a : Data) (i : Fin 768) :
    (callbackInitial a).stacks (lowStack i) =
      if i ∈ callbackScratch then [] else a.stacks (lowStack i) := by
  exact (embedState_stack localRegister lowStack a
    (clearManyState callbackScratch (projectState localRegister lowStack a))
    (Fin.castAdd_injective _ _) i).trans
    (clearMany_stacks callbackScratch (projectState localRegister lowStack a) i)

theorem callbackInitial_frame (a : Data) (i : Fin 896)
    (hi : i ∉ callbackScratch.map lowStack) :
    (callbackInitial a).stacks i = a.stacks i := by
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val, hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    have hn : j ∉ callbackScratch := by
      intro hm
      exact hi (List.mem_map.mpr ⟨j, hm, hj⟩)
    rw [← hj, callbackInitial_low, ite_eq_right hn]
  · apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

theorem returnToRecords_eval (a : Data) : Eval returnToRecords 3 a (returned a) := by
  let b : Data := ⟨Function.update a.regs 13 false, a.stacks⟩
  let c : Data := ⟨Function.update b.regs 14 true, a.stacks⟩
  have h1 : Eval (.base (.atom (.set 13 false))) 1 a b := .base (.atom _ _)
  have h2 : Eval (.base (.atom (.set 14 true))) 1 b c := .base (.atom _ _)
  have h3 : Eval (.base (.atom (.set 15 false))) 1 c (returned a) := .base (.atom _ _)
  exact h1.seq (h2.seq h3)

theorem callbackFinish_eval (a : Data) :
    Eval (.seq (clear 149) returnToRecords) (2 * (a.stacks 149).length + 6)
      a (callbackFinished a) := by
  convert (clear_eval a 149).seq (returnToRecords_eval (cleared a 149)) using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
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

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Space for one actual ambient-coordinate table construction. Its unary
traversal has only n iterations, so its polynomial local time bounds every
source prefix. No outer signature or finite-difference iteration count occurs
in this estimate. The concrete literal and staging traces are instantiated by
the factor-table producer, rather than supplied to a final counting endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace

open SqrtLog

open BitProgram StructuredCalls FactorTableProgram

/-- The protected caller regions include every low node port except the
export62, all eight layout masters, and high ports outside the private bank. -/
theorem caller_port_not_written (i : Fin 896)
    (hi : (i.val < 340 ∧ i ≠ 62) ∨ i ∈ protectedPorts ∨
      (768 ≤ i.val ∧ i ≠ 881 ∧ i ≠ 882 ∧ (i.val < 885 ∨ 892 < i.val))) :
    i ∉ writtenPorts := by
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp hm
    rcases hi with hi | hi | hi
    · have hw := (LeafProgram.Incidence.mem_workerPorts j).mp hj
      have hb : 340 ≤ (basePort j).val := by
        simp only [basePort]
        split_ifs <;> simp_all only [Fin.coe_ofNat_eq_mod, Fin.val_castAdd] <;> omega
      have hv := congrArg Fin.val hji
      omega
    · exact basePort_outside i (Or.inl hi) ⟨j, hji⟩
    · exact basePort_outside i (Or.inr ⟨hi.1, hi.2.2.2⟩) ⟨j, hji⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [protectedPorts, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

/-- Actual retained words discharge the source's per-entry size requirements.
The metadata bound follows from physical lookup serialization, and the
incidence count follows from the actual addressed plan stream. -/
theorem Ready.of_masters {r Q d u J n f B S : ℕ}
    {p : SourceBank.Parameters r Q d} {ps : List (ℕ × ℕ)}
    {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {theta : Coeff (baseWidth 3 p.t) d} {a : FactorTableProgram.OuterData}
    (hu : 0 < u) (hJ : 0 < J)
    (hscalar : ScalarMasters p.t p.model p.modulus p.cache J p.R theta
      (projectState id FactorTableProgram.basePort a) n)
    (hmasters : SourceMasters p ps P (projectState id FactorTableProgram.basePort a))
    (hselected : a.stacks 556 = List.replicate f true)
    (hmask : (a.stacks 857).length = n)
    (hincoming : ∀ i, (a.stacks i).length ≤ B)
    (hsize : 1029*B+99+n+n*FactorTableProgram.literalRecordBound n
      (specializedPayloadBound n u J (baseWidth 3 p.t) d)+1 ≤ S)
    (hRQ : p.R+1 ≤ Q) : Ready p ps P u J n f B S theta a := by
  have hBS : B ≤ S := by omega
  have hcap (i : Fin 768) :
      ((projectState id FactorTableProgram.basePort a).stacks i).length ≤ B :=
    hincoming (FactorTableProgram.basePort i)
  have hrow := hcap 716
  rw [hmasters.rowWidth,p.hrowWidth,p.hringWidth] at hrow
  have hnodes := hcap 131
  rw [hmasters.nodes,List.length_replicate] at hnodes
  have hmetadata := hcap 135
  rw [hmasters.metadata] at hmetadata
  have hplans := hcap 136
  rw [hmasters.plans] at hplans
  have hincidence : ps.length ≤ B := by
    have hlength := LayoutOwnerFiberProgram.stream_length ps
    omega
  have hn := hincoming 857
  rw [hmask] at hn
  have hf := hincoming 556
  rw [hselected,List.length_replicate] at hf
  refine ⟨hu,hJ,hscalar,hmasters,hselected,hmask,hincoming,hsize,
    ((Nat.mul_le_mul_right _ hRQ).trans hrow).trans hBS,
    (hRQ.trans hnodes).trans hBS,?_,hincidence.trans hBS,hn.trans hBS,
    hf.trans hBS,hplans.trans hBS⟩
  intro x
  have hinj : Function.Injective (fun v : Fin ps.length => List.replicate v.val true) := by
    intro v w he
    apply Fin.ext
    simpa only [List.length_replicate] using congrArg List.length he
  have hl := PackingMetadata.lookup_eq P (fun v => List.replicate v.val true)
    CollisionProgram.encodeType hinj x
  have hp := ((GlobalBasisMetadata.payload_length_le _ _ _ hl).trans hmetadata).trans hBS
  have hb (m : GlobalBasisMetadata.Metadata) :
      m.block.length ≤ m.encode.length ∧ m.typeCode.length ≤ m.encode.length ∧
        m.rank.length ≤ m.encode.length := by
    cases m <;> simp [GlobalBasisMetadata.Metadata.block,GlobalBasisMetadata.Metadata.typeCode,
      GlobalBasisMetadata.Metadata.rank,GlobalBasisMetadata.Metadata.encode,Encoding.length_frame] <;> omega
  exact ⟨(hb _).1.trans hp,(hb _).2.1.trans hp,(hb _).2.2.trans hp⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact bytes and coefficient meaning at the raw-row/interpreter boundary.
The full extension dimension is D; the assembler parameter is D-1. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Expansion
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open HashCircuitProgram.Native
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem original_source_bytes {n : ℕ} (source : List (List (SAT.Literal (Fin n)))) :
    Encoding.encodeList id (encodedClauses source)=ExecQuantitativeSparsify.encodeRawFormula source := by
  rw [encodedClauses,ExecSparsifyEncoding.encodeList_map]
  rw [ExecQuantitativeSparsify.encodeRawFormula,ExecSparsifyEncoding.encodeList_map]
  congr 1
  funext ls
  exact clausePayload_codes ls

end SubexponentialSAT.SqrtLog.HashInputProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual ordinary and marked factor branches. The physical factor ID is
converted to the unary source counter, then the specialized table is produced
before the original finite-ring arithmetic is run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

theorem identified_stacks (a : FactorAssignmentProgram.Data) (factor : ℕ) :
    (identified a factor).stacks = Function.update a.stacks 556 (List.replicate factor true) := by
  funext i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val, hi⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj, identified, embedState_stack id lowStack a _ (Fin.castAdd_injective _ _) j]
    by_cases h556 : j = 556
    · rw [h556]
      rfl
    · have hne : lowStack j ≠ (556 : Fin 896) := by
        intro he
        apply h556
        apply Fin.ext
        have hv := congrArg (fun k : Fin 896 => k.val) he
        exact hv
      simp [FactorID.output, Function.update_of_ne h556,
        Function.update_of_ne hne, projectState]
  · have h556 : i ≠ 556 := by
      intro he
      have hv := congrArg (fun k : Fin 896 => k.val) he
      change i.val = 556 at hv
      omega
    rw [identified, embedState_stack_frame _ _ _ _ i, Function.update_of_ne h556]
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual specialized callback dispatches one stored original factor ID.
The general dispatch theorem fixes its physical payload, flags and exact frame;
hash and marked branch correctness is supplied by their concrete native proofs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

open OAI BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafProgram MomentsProgram FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The paid clear preserves an already established callback boundary. -/
theorem callbackInitial_stacks (a : FactorAssignmentProgram.Data)
    (hclean : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []) :
    (callbackInitial a).stacks = a.stacks := by
  funext i
  by_cases hi : i ∈ callbackScratch.map lowStack
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [callbackInitial_low, ite_eq_left hj, hclean j hj]
  · exact callbackInitial_frame a i hi

private theorem dispatchInput_frame (a : FactorAssignmentProgram.Data) (i : Fin 768)
    (hi : i ∉ callbackScratch) :
    (dispatchInput a).stacks i = a.stacks (lowStack i) :=
  (callbackInitial_low a i).trans (ite_eq_right hi)

private theorem dispatchInput_work (a : FactorAssignmentProgram.Data) :
    ∀ i ∈ FactorDispatch.scratch, (dispatchInput a).stacks i = [] := by
  intro i hi
  have hmem : i ∈ callbackScratch := by
    simp only [callbackScratch, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hi))
  exact (callbackInitial_low a i).trans (ite_eq_left hmem)

/-- All caller stacks are restored except the actual selected payload154.
This frame applies to hash, marked and neutral IDs, without an early exit. -/
theorem dispatched_stacks (a : FactorAssignmentProgram.Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark) :
    (dispatched a rf rows clauses marked mark factor).stacks =
      Function.update (callbackInitial a).stacks 154
        (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor) := by
  have hr : (dispatchInput a).stacks 701 = Encoding.encodeList id rows :=
    (dispatchInput_frame a 701 (by decide)).trans hrows
  have hc : (dispatchInput a).stacks 700 = Encoding.encodeList id clauses :=
    (dispatchInput_frame a 700 (by decide)).trans hclauses
  have hn : (dispatchInput a).stacks 704 = List.replicate rows.length true :=
    (dispatchInput_frame a 704 (by decide)).trans hcount
  have hm : (dispatchInput a).stacks 705 = Encoding.encodeNat mark :=
    (dispatchInput_frame a 705 (by decide)).trans hmark
  have hlow := FactorDispatch.finished_stacks (dispatchInput a) rf rows clauses
    marked mark factor hr hc hn hm (dispatchInput_work a)
  funext i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val, hi⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj]
    change (embedState id lowStack (callbackInitial a)
      (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor)).stacks
      (lowStack j) = _
    rw [embedState_stack id lowStack _ _ (Fin.castAdd_injective _ _) j, hlow]
    by_cases h154 : j = 154
    · rw [h154]
      simp [lowStack]
    · have hwide : lowStack j ≠ 154 := by
        intro he
        apply h154
        exact Fin.ext (congrArg (fun k : Fin 896 => k.val) he)
      simp only [Function.update_of_ne h154, Function.update_of_ne hwide]
      rfl
  · have h154 : i ≠ 154 := by intro he; subst i; norm_num at hi
    rw [Function.update_of_ne h154]
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

/-- The two conditionals are charged in their actual chosen branch. -/
theorem choose_hash {k : ℕ} {a b : FactorAssignmentProgram.Data}
    (h5 : a.regs 5 = true) (he : Eval hashFactor k a b) :
    Eval choose (k + 1) a b :=
  Eval.ite_true h5 he

theorem choose_marked {k : ℕ} {a b : FactorAssignmentProgram.Data}
    (h5 : a.regs 5 = false) (h6 : a.regs 6 = true)
    (he : Eval markedFactor k a b) : Eval choose (k + 2) a b := by
  simpa only [choose, Nat.add_assoc] using
    (Eval.ite_false h5 (Eval.ite_true h6 he) :
      Eval (.ite 5 hashFactor (.ite 6 markedFactor (.base .skip))) (k + 1 + 1) a b)

/-- Compose the actual clear, dispatcher, chosen branch and record return.
The branch frame is the one supplied by native table/arithmetic execution. -/
theorem callback_chosen_eval {n B d : ℕ}
    (a b : FactorAssignmentProgram.Data) (rf : Fin 8 → Bool) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor kd kc : ℕ) (out : FactorAssignmentLoop.Raw n B d)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hclean : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = [])
    (hd : Eval (liftLow FactorDispatch.command 149 154) kd (callbackInitial a)
      (dispatched a rf rows clauses marked mark factor))
    (hc : Eval choose kc (dispatched a rf rows clauses marked mark factor) b)
    (hb : b.stacks = Function.update
      (Function.update (dispatched a rf rows clauses marked mark factor).stacks 154 [])
      151 (Product.bytes out)) :
    Eval callback (clearCallbackCost a + (kd + (kc + (2 * (a.stacks 149).length + 6))))
      a (callbackFinished b) ∧
    (callbackFinished b).stacks =
      Function.update (Function.update a.stacks 149 []) 151 (Product.bytes out) ∧
    (callbackFinished b).regs 13 = false ∧
    (callbackFinished b).regs 14 = true ∧
    (callbackFinished b).regs 15 = false := by
  have hstart := callbackInitial_stacks a hclean
  have hw := dispatched_stacks a rf rows clauses marked mark factor hrows hclauses hcount hmark
  have h154 : a.stacks 154 = [] := hclean 154 (by decide)
  have hframe : b.stacks = Function.update a.stacks 151 (Product.bytes out) := by
    rw [hb, hw, hstart]
    funext i
    by_cases hi151 : i = 151 <;> by_cases hi154 : i = 154
    all_goals simp [hi151, hi154, h154]
  have h149 : b.stacks 149 = a.stacks 149 := by rw [hframe]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [callback, h149] using
      (clearCallback_eval a).seq (hd.seq (hc.seq (callbackFinish_eval b)))
  · funext i
    by_cases hi149 : i = 149 <;> by_cases hi151 : i = 151
    all_goals simp [callbackFinished, returned, cleared, hframe, hi149, hi151]
  all_goals simp [callbackFinished, returned]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

theorem Input.fetched_stacks (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    (fetched q a f rf).stacks = Function.update a.stacks 154
      (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f) := by
  rw [fetched, dispatched_stacks a rf q.rawRows q.clauses q.marked q.mark f
    h.rows h.clauses h.count h.mark, callbackInitial_stacks a h.blank]

theorem Input.fetched_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 896) (hi : i ≠ 154) : (fetched q a f rf).stacks i = a.stacks i := by
  rw [h.fetched_stacks rf, Function.update_of_ne hi]

theorem Input.fetched_low_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 768) (hi : i ≠ 154) :
    (projectState id lowStack (fetched q a f rf)).stacks i = a.stacks (lowStack i) := by
  apply h.fetched_frame rf
  intro he
  exact hi (Fin.ext (congrArg (fun k : Fin 896 => k.val) he))

/-- A selected record is bounded by the actual serialized master containing
it. This includes the neutral empty payload. -/
theorem Input.payload_length (h : Input q A S one seed a f) :
    (LeafFactorDispatchProgram.selectedPayload q.rawRows q.clauses q.marked q.mark f).length ≤ A := by
  unfold LeafFactorDispatchProgram.selectedPayload
  split_ifs with hh hm
  · rw [List.getD_eq_getElem _ _ hh]
    exact (HashInputProgram.Loop.original_payload_length_le q.rawRows _
      (List.getElem_mem hh)).trans (by rw [← h.rows]; exact h.incoming 701)
  · have hb : q.marked = true := (Bool.and_eq_true_iff.mp hm).1
    have hv : q.mark < q.clauses.length := by
      simpa only [Factor.Spec.clauses, HashInputProgram.Expansion.encodedClauses,
        List.length_map] using q.markValid hb
    rw [List.getD_eq_getElem _ _ hv]
    exact (HashInputProgram.Loop.original_payload_length_le q.clauses _
      (List.getElem_mem hv)).trans (by rw [← h.clauses]; exact h.incoming 700)
  · simp

theorem Input.fetched_wordBound (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    ∀ i, ((fetched q a f rf).stacks i).length ≤ A := by
  intro i
  rw [h.fetched_stacks rf]
  by_cases hi : i = 154
  · subst i
    simpa only [Function.update_self] using h.payload_length
  · simpa only [Function.update_of_ne hi] using h.incoming i

/-- Source master words survive dispatch and the concrete unary factor-ID
conversion; only the selected payload154 and selected-factor word556 change. -/
theorem Input.table_frame (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (i : Fin 768) (hi154 : FactorTableProgram.basePort i ≠ 154)
    (hi556 : FactorTableProgram.basePort i ≠ 556) :
    (projectState id FactorTableProgram.basePort
      (FactorAssignmentBranches.tableInput (fetched q a f rf) f)).stacks i =
      (projectState localRegister FactorTableProgram.basePort a).stacks i := by
  change (FactorAssignmentBranches.identified (fetched q a f rf) f).stacks
    (FactorTableProgram.basePort i) = a.stacks (FactorTableProgram.basePort i)
  rw [FactorAssignmentBranches.identified_stacks, Function.update_of_ne hi556,
    h.fetched_frame rf _ hi154]

theorem Input.table_scalar (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
      q.theta (projectState id FactorTableProgram.basePort
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)) n := by
  have H := h.table_frame rf
  refine ⟨h.scalar.widthPositive, h.scalar.zeroCanonical, h.scalar.zeroBits,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [H 194 (by decide) (by decide)]; exact h.scalar.modulus
  · rw [H 202 (by decide) (by decide)]; exact h.scalar.width
  · rw [H 203 (by decide) (by decide)]; exact h.scalar.zero
  · rw [H 201 (by decide) (by decide)]; exact h.scalar.table
  · rw [H 204 (by decide) (by decide)]; exact h.scalar.degree
  · rw [H 145 (by decide) (by decide)]; exact h.scalar.choicesLength
  · rw [H 280 (by decide) (by decide)]; exact h.scalar.zeroWord
  · rw [H 207 (by decide) (by decide)]; exact h.scalar.oneWord
  · rw [H 78 (by decide) (by decide)]; exact h.scalar.thetaWord
  · rw [H 128 (by decide) (by decide)]; exact h.scalar.ambientCount
  · rw [H 243 (by decide) (by decide)]; exact h.scalar.targetCount
  · rw [H 138 (by decide) (by decide)]; exact h.scalar.radius
  · rw [H 703 (by decide) (by decide)]; exact h.scalar.highLength

theorem Input.table_masters (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.SourceMasters q.p q.ps q.packing
      (projectState id FactorTableProgram.basePort
        (FactorAssignmentBranches.tableInput (fetched q a f rf) f)) := by
  have H := h.table_frame rf
  constructor
  · rw [H 130 (by decide) (by decide)]; exact h.masters.colors
  · rw [H 131 (by decide) (by decide)]; exact h.masters.nodes
  · rw [H 132 (by decide) (by decide)]; exact h.masters.typeWidth
  · rw [H 710 (by decide) (by decide)]; exact h.masters.positive
  · rw [H 711 (by decide) (by decide)]; exact h.masters.negative
  · rw [H 140 (by decide) (by decide)]; exact h.masters.scalarWidth
  · rw [H 712 (by decide) (by decide)]; exact h.masters.power
  · exact h.masters.powerNegative
  · rw [H 138 (by decide) (by decide)]; exact h.masters.radius
  · rw [H 139 (by decide) (by decide)]; exact h.masters.offset
  · rw [H 135 (by decide) (by decide)]; exact h.masters.metadata
  · rw [H 136 (by decide) (by decide)]; exact h.masters.plans
  · rw [H 713 (by decide) (by decide)]; exact h.masters.inverses
  · rw [H 714 (by decide) (by decide)]; exact h.masters.negatives
  · rw [H 715 (by decide) (by decide)]; exact h.masters.differences
  · rw [H 717 (by decide) (by decide)]; exact h.masters.ringWidth
  · rw [H 716 (by decide) (by decide)]; exact h.masters.rowWidth
  · rw [H 280 (by decide) (by decide)]; exact h.masters.zero
  · rw [H 207 (by decide) (by decide)]; exact h.masters.one
  · rw [H 211 (by decide) (by decide)]; exact h.masters.minusOne
  · rw [H 728 (by decide) (by decide)]; exact h.masters.inverseDenominator

/-- The actual source-table readiness is derived from fixed physical masters
and the already stored original ID; it is not provided by a caller service. -/
theorem Input.table_ready (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    FactorTableNative.Ready q.p q.ps q.packing q.u q.J n f A S q.theta
      (FactorAssignmentBranches.tableInput (fetched q a f rf) f) := by
  apply FactorTableNative.Ready.of_masters q.hu q.hJ (h.table_scalar rf) (h.table_masters rf)
  · change (FactorAssignmentBranches.identified (fetched q a f rf) f).stacks 556 = _
    simp only [FactorAssignmentBranches.identified_stacks, Function.update_self]
  · change ((FactorAssignmentBranches.identified (fetched q a f rf) f).stacks 857).length = n
    rw [FactorAssignmentBranches.identified_stacks, Function.update_of_ne (by decide),
      h.fetched_frame rf 857 (by decide)]
    exact h.correction
  · intro i
    change ((FactorAssignmentBranches.identified (fetched q a f rf) f).stacks i).length ≤ A
    rw [FactorAssignmentBranches.identified_stacks]
    by_cases hi : i = 556
    · subst i
      have hf := h.incoming 149
      rw [h.factor, List.length_reverse] at hf
      simp only [Encoding.length_encodeNat] at hf
      simp only [Function.update_self, List.length_replicate]
      omega
    · rw [Function.update_of_ne hi]
      exact h.fetched_wordBound rf i
  · exact h.size
  · exact h.radius

/-- The hash source bytes are the actual row selected by f, in the unchanged
original raw-row order. No arbitrary raw payload is assumed. -/
theorem Input.fetched_hash (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (hf : f < q.rows.length) :
    Factor.HashInput q.ctx q.minus one seed q.source q.rows[f] q.digits q.bitWidth
      (projectState id lowStack (fetched q a f rf)) := by
  have H := h.fetched_low_frame rf
  constructor
  · change (fetched q a f rf).stacks 154 = _
    rw [h.fetched_stacks rf]
    simp [LeafFactorDispatchProgram.selectedPayload, Factor.Spec.rawRows, hf]
  · exact (H 700 (by decide)).trans
      (h.clauses.trans (HashInputProgram.Expansion.original_source_bytes q.source))
  · rw [H 708 (by decide)]; exact h.hashWidth
  · rw [H 707 (by decide)]; exact h.hashModulus
  · rw [H 280 (by decide)]; exact h.ringShape
  · exact (H 64 (by decide)).trans (h.blank 64 (by decide))
  · intro i hi
    have hn : i ≠ 154 := by
      intro he
      subst i
      norm_num [Expansion.scratch, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi
    rw [H i hn]
    apply h.blank i
    simp only [callbackScratch, List.mem_append]
    exact Or.inl (Or.inr hi)
  · exact (H 358 (by decide)).trans (h.blank 358 (by decide))
  · exact (H 359 (by decide)).trans (h.blank 359 (by decide))
  · intro i
    rw [Factor.indicatorStacks_low, H _ (Factor.low_ne i 154 (by decide))]
    exact h.low i
  · exact (H 69 (by decide)).trans h.oneBytes
  · exact (H 76 (by decide)).trans h.minusBytes
  · exact (H 143 (by decide)).trans h.tape
  · rw [H 88 (by decide)]; exact h.shape
  · intro i hi
    have hn : Factor.indicatorStacks i ≠ 154 :=
      (by decide : ∀ i ∈ FactorServices.indicatorScratch,
        Factor.indicatorStacks i ≠ (154 : Fin 768)) i hi
    rw [H _ hn]
    apply h.blank
    simp only [callbackScratch, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨i, hi, rfl⟩))))
  · exact (H 151 (by decide)).trans h.seedBytes
  · exact (H 159 (by decide)).trans (h.blank 159 (by decide))

/-- Actual marked-clause bytes retain literal polarity and original variable
IDs; this is the source's clause-violation expression, not its complement. -/
theorem Input.fetched_marked (h : Input q A S one seed a f) (rf : Fin 8 → Bool)
    (hm : q.marked = true) (hf : f = q.rows.length) :
    let state := projectState id lowStack (fetched q a f rf)
    state.stacks 154 = Encoding.encodeList id (q.markedClause.map Clause.literalBits) ∧
      state.stacks 63 = [] ∧
      (∀ i, state.stacks (Clause.callerStacks (Memory.lowPort i)) = IdempotentApplyProgram.Steps.low q.ctx i) ∧
      state.stacks 69 = Product.bytes one ∧ state.stacks 76 = RingProgram.flat q.minus ∧
      (∀ i ∈ FactorServices.clauseScratch, state.stacks (Clause.callerStacks i) = []) ∧
      state.stacks 151 = Product.bytes seed ∧ state.stacks 159 = [] := by
  dsimp only
  have H := h.fetched_low_frame rf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he : f = q.rawRows.length := by simpa [Factor.Spec.rawRows] using hf
    have hv := q.markValid hm
    have hp : q.markedClause = q.source[q.mark] := by
      simp [Factor.Spec.markedClause, List.getElem?_eq_getElem hv]
    change (fetched q a f rf).stacks 154 = _
    rw [h.fetched_stacks rf]
    have payload (ls : List (SAT.Literal (Fin n))) :
        HashInputProgram.clausePayload ls = Encoding.encodeList id (ls.map Clause.literalBits) := by
      induction ls with
      | nil => rfl
      | cons l ls ih =>
          change true :: (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++
            HashInputProgram.clausePayload ls) = _
          simp only [List.map_cons, Encoding.encodeList, Clause.literalBits, ih, id_eq]
    simp [LeafFactorDispatchProgram.selectedPayload, he, hm, Factor.Spec.clauses,
      HashInputProgram.Expansion.encodedClauses, hp, List.getElem?_eq_getElem hv, payload]
  · exact (H 63 (by decide)).trans h.clauseOutput
  · intro i
    change (projectState id lowStack (fetched q a f rf)).stacks
      (Factor.nativeStacks (Memory.lowPort i)) = _
    rw [H _ (Factor.low_ne i 154 (by decide))]
    exact h.low i
  · exact (H 69 (by decide)).trans h.oneBytes
  · exact (H 76 (by decide)).trans h.minusBytes
  · intro i hi
    have hn : Clause.callerStacks i ≠ 154 :=
      (by decide : ∀ i ∈ FactorServices.clauseScratch,
        Clause.callerStacks i ≠ (154 : Fin 768)) i hi
    rw [H _ hn]
    exact h.clauseWork i hi
  · exact (H 151 (by decide)).trans h.seedBytes
  · exact (H 159 (by decide)).trans (h.blank 159 (by decide))

/-- The table-private boundary is unaffected by the selected payload port. -/
theorem Input.table_private (h : Input q A S one seed a f) (rf : Fin 8 → Bool) :
    ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 →
      (fetched q a f rf).stacks i = [] := by
  intro i hi h62 h556
  have hn : i ≠ 154 := by
    intro he
    subst i
    exact FactorTableSpace.caller_port_not_written 154 (Or.inl (by decide)) hi
  rw [h.fetched_frame rf i hn]
  exact h.tableBlank i hi h62 h556

/-- Actual ordinary dispatch, table production, expansion, indicator,
accumulator multiplication and record return, specialized to q.ctx. -/
theorem hash_callback_eval (h : Input q A S one seed a f)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (hf : f < q.rows.length) (width : ℕ)
    (hwidth : ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
      w.literals.length ≤ width) :
    ∃ (rf : Fin 8 → Bool)
      (incidence : Fin n → FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
      (steps : ℕ) (z : FactorAssignmentProgram.Data),
      (∀ v, TruncatedRingProgram.Good ∅ q.u q.J (incidence v)) ∧
      (∀ v, TruncatedRingProgram.rawDenote q.p.ops.decode (incidence v) =
        FactorTableDenotation.specializedJet q.u q.J (a.stacks 857)
          (Factor.factorJet q.p q.ps q.packing n f v.val q.theta (a.stacks ∘ lowStack))) ∧
      let result := Product.run 3 q.p.t q.ctx.modulus q.ctx.cache q.ctx.table q.u q.J seed
        (Indicator.result q.ctx q.minus one incidence
          (HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f]) q.digits) []
      NativeSemantics.Good ∅ q.u q.J result ∧
      steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 14 +
        LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f +
        hashBranchBudget q A S width a f hf rf ∧
      Eval FactorAssignmentProgram.callback steps a z ∧
      z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes result) ∧
      z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false := by
  have hvalid : q.marked = true → q.mark < q.clauses.length := by
    simpa only [Factor.Spec.clauses, HashInputProgram.Expansion.encodedClauses, List.length_map]
      using q.markValid
  obtain ⟨kd,rf,hkd,hd,h5,_⟩ := dispatch_eval a q.rawRows q.clauses q.marked q.mark f
    h.rows h.clauses h.count h.mark h.flag h.factor hvalid
  have hn : f < q.rawRows.length := by simpa only [Factor.Spec.rawRows, List.length_map] using hf
  have hrole : (fetched q a f rf).regs 5 = true := by simpa [fetched, hn] using h5
  have hid : (fetched q a f rf).stacks 149 = (Encoding.encodeNat f).reverse :=
    (h.fetched_frame rf 149 (by decide)).trans h.factor
  have h556 : (fetched q a f rf).stacks 556 = [] :=
    (h.fetched_frame rf 556 (by decide)).trans (h.blank 556 (by decide))
  have h62 : (fetched q a f rf).stacks 62 = [] :=
    (h.fetched_frame rf 62 (by decide)).trans (h.blank 62 (by decide))
  obtain ⟨incidence,kb,b,hgood,hmeaning,hkb,hresult,heb,hstore⟩ :=
    FactorAssignmentBranches.hashFactor_eval q.p q.ps q.packing q.ctx f A S q.theta q.minus
      one seed hone hseed q.source q.rows[f] q.digits q.bitWidth width q.bitWidthPositive
      q.sourceBound hwidth (fetched q a f rf) hid h556 h62 (h.table_ready rf)
      (h.table_private rf) (h.fetched_hash rf hf)
  have he := callback_chosen_eval a b rf q.rawRows q.clauses q.marked q.mark f kd (kb+1) _
    h.rows h.clauses h.count h.mark h.blank hd (choose_hash hrole heb) hstore
  refine ⟨rf,incidence,_,callbackFinished b,hgood,?_,hresult,?_,he.1,
    he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2⟩
  · intro v
    exact (h.payload_correct rf v (incidence v) (hmeaning v)).2
  · change kb ≤ hashBranchBudget q A S width a f hf rf at hkb
    omega

/-- Actual marked dispatch and clause violation arithmetic, retaining the
very specialized incidence entries returned by the table run. -/
theorem marked_callback_eval (h : Input q A S one seed a f)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (hm : q.marked = true) (hf : f = q.rows.length) :
    ∃ (rf : Fin 8 → Bool)
      (incidence : Fin n → FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
      (steps : ℕ) (z : FactorAssignmentProgram.Data),
      (∀ v, TruncatedRingProgram.Good ∅ q.u q.J (incidence v)) ∧
      (∀ v, TruncatedRingProgram.rawDenote q.p.ops.decode (incidence v) =
        FactorTableDenotation.specializedJet q.u q.J (a.stacks 857)
          (Factor.factorJet q.p q.ps q.packing n f v.val q.theta (a.stacks ∘ lowStack))) ∧
      let result := Product.run 3 q.p.t q.ctx.modulus q.ctx.cache q.ctx.table q.u q.J seed
        (FactorServices.clauseResult q.ctx q.minus one incidence q.markedClause) []
      NativeSemantics.Good ∅ q.u q.J result ∧
      steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
        LeafFactorDispatchProgram.budget q.rawRows q.clauses q.mark f +
        markedBranchBudget q A S a f rf ∧
      Eval FactorAssignmentProgram.callback steps a z ∧
      z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes result) ∧
      z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false := by
  have hvalid : q.marked = true → q.mark < q.clauses.length := by
    simpa only [Factor.Spec.clauses, HashInputProgram.Expansion.encodedClauses, List.length_map]
      using q.markValid
  obtain ⟨kd,rf,hkd,hd,h5,h6⟩ := dispatch_eval a q.rawRows q.clauses q.marked q.mark f
    h.rows h.clauses h.count h.mark h.flag h.factor hvalid
  have hn : f = q.rawRows.length := by simpa only [Factor.Spec.rawRows, List.length_map] using hf
  have hrole5 : (fetched q a f rf).regs 5 = false := by simpa [fetched, hn] using h5
  have hrole6 : (fetched q a f rf).regs 6 = true := by simpa [fetched, hm, hn] using h6
  have hid : (fetched q a f rf).stacks 149 = (Encoding.encodeNat f).reverse :=
    (h.fetched_frame rf 149 (by decide)).trans h.factor
  have h556 : (fetched q a f rf).stacks 556 = [] :=
    (h.fetched_frame rf 556 (by decide)).trans (h.blank 556 (by decide))
  have h359 : (fetched q a f rf).stacks 359 = [] :=
    (h.fetched_frame rf 359 (by decide)).trans (h.blank 359 (by decide))
  have h62 : (fetched q a f rf).stacks 62 = [] :=
    (h.fetched_frame rf 62 (by decide)).trans (h.blank 62 (by decide))
  obtain ⟨hraw, houtput, hlow, honeBytes, hminus, hwork, hseedBytes, htemporary⟩ :=
    h.fetched_marked rf hm hf
  obtain ⟨incidence,kb,b,hgood,hmeaning,hkb,hresult,heb,hstore⟩ :=
    FactorAssignmentBranches.markedFactor_eval q.p q.ps q.packing q.ctx f A S q.theta q.minus
      one seed hone hseed q.markedClause (fetched q a f rf) hid h556 h359 h62
      (h.table_ready rf) (h.table_private rf) hraw houtput hlow honeBytes hminus
      hwork hseedBytes htemporary
  have he := callback_chosen_eval a b rf q.rawRows q.clauses q.marked q.mark f kd (kb+2) _
    h.rows h.clauses h.count h.mark h.blank hd (choose_marked hrole5 hrole6 heb) hstore
  refine ⟨rf,incidence,_,callbackFinished b,hgood,?_,hresult,?_,he.1,
    he.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2⟩
  · intro v
    exact (h.payload_correct rf v (incidence v) (hmeaning v)).2
  · change kb ≤ markedBranchBudget q A S a f rf at hkb
    omega

/-- The concrete callback produces the exact specialized original factor
value. Its whole raw output, physical frame, paid execution, and arithmetic
meaning refer to one and the same actual execution. -/
theorem callback_eval_correct_oai (h : Input q A S one seed a f)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (honeval : NativeSemantics.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (width : ℕ)
    (hwidth : ∀ hf : f < q.rows.length,
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width) :
    ∃ (out : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
      (rf : Fin 8 → Bool) (steps : ℕ) (z : FactorAssignmentProgram.Data),
      NativeSemantics.Good ∅ q.u q.J out ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
        TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
          QueryEvaluation.specializeDense q.u q.J
            (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
            (q.value (a.stacks ∘ lowStack) f) ∧
      steps ≤ callbackBudget q A S width a f rf ∧
      Eval FactorAssignmentProgram.callback steps a z ∧
      z.stacks = Function.update (Function.update a.stacks 149 []) 151 (Product.bytes out) ∧
      z.regs 13 = false ∧ z.regs 14 = true ∧ z.regs 15 = false := by
  by_cases hf : f < q.rows.length
  · obtain ⟨rf,incidence,k,z,hi,hinc,hout,hk,he,hz,h13,h14,h15⟩ :=
      hash_callback_eval h hone hseed hf width (hwidth hf)
    refine ⟨_,rf,k,z,hout,hash_step_value _ _ incidence hone hseed honeval hi hinc hf,
      ?_,he,hz,h13,h14,h15⟩
    simp only [callbackBudget, dite_eq_left hf]
    omega
  · by_cases hm : (q.marked && decide (f = q.rows.length)) = true
    · have hb : q.marked = true := (Bool.and_eq_true_iff.mp hm).1
      have hid : f = q.rows.length := of_decide_eq_true (Bool.and_eq_true_iff.mp hm).2
      obtain ⟨rf,incidence,k,z,hi,hinc,hout,hk,he,hz,h13,h14,h15⟩ :=
        marked_callback_eval h hone hseed hb hid
      refine ⟨_,rf,k,z,hout,marked_step_value _ _ incidence hone hseed honeval hi hinc hb hid,
        ?_,he,hz,h13,h14,h15⟩
      simpa only [callbackBudget, dite_eq_right hf, hm, ite_true, if_true] using hk
    · have hb : (q.marked && decide (f = q.rows.length)) = false :=
        Bool.eq_false_iff.mpr hm
      obtain ⟨k,z,hout,hk,he,hz,h13,h14,h15⟩ := neutral_callback_eval h hseed hf hb
      refine ⟨seed,(fun _ => false),k,z,hout,?_,?_,he,hz,h13,h14,h15⟩
      · simp only [Factor.Spec.value, dite_eq_right hf, hb, Bool.false_eq_true, ite_false,
          map_one, mul_one]
      · simpa only [callbackBudget, dite_eq_right hf, hb, Bool.false_eq_true, ite_false,
          Nat.add_zero] using hk

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.callback_eval_correct_oai
