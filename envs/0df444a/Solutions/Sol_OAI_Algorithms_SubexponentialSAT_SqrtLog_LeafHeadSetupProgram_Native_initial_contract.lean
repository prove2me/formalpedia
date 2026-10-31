-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.initial_contract
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:29:01.471673+00:00
-- url     : https://prove2.me/submissions/441cced1-c3fb-4bc8-bf78-2aeaf2d6d5ac

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutFiberSumProgram_nativeEntryContract
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_Native_start_cache
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_Native_start_size
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_matrixBase_fiberReady

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

/-- Exact list-order specification, without reindexing the original owners. -/
theorem fiberIndices_eq_filter (query index : ℕ) (ps : List (ℕ × ℕ)) :
    fiberIndices query index ps =
      (((ps.zipIdx index).filter fun x => decide (x.1.1=query)).map Prod.snd) := by
  induction ps generalizing index with
  | nil => rfl
  | cons p ps ih =>
      by_cases h : p.1=query <;> simp [fiberIndices,h,ih]

theorem fiberIndices_length_le (query index : ℕ) (ps : List (ℕ × ℕ)) :
    (fiberIndices query index ps).length ≤ ps.length := by
  rw [fiberIndices_eq_filter]
  simpa using List.length_filter_le (fun x : (ℕ × ℕ) × ℕ => decide (x.1.1=query)) (ps.zipIdx index)

theorem encodeIndices_length_le (query index : ℕ) (ps : List (ℕ × ℕ)) :
    (encodeIndices (fiberIndices query index ps)).length ≤ ps.length*(index+ps.length+1) := by
  induction ps generalizing index with
  | nil => simp [fiberIndices,encodeIndices]
  | cons p ps ih =>
      have hh := ih (index+1)
      by_cases h : p.1=query <;>
        simp [fiberIndices,h,encodeIndices,Encoding.encodeNat] at * <;> nlinarith

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

theorem scanCost_le (query index : ℕ) (ps : List (ℕ × ℕ)) :
    scanCost query index ps ≤
      1+71*mass ps+ps.length*(9*query+7*index+7*ps.length+210) := by
  induction ps generalizing index with
  | nil => simp [scanCost,mass]
  | cons p ps ih =>
      have hh := ih (index+1)
      simp only [scanCost,callbackCost,pairPayload_length]
      simp only [mass,List.map_cons,List.sum_cons,List.length_cons]
      unfold mass at hh
      nlinarith

/-- Polynomial in the actual encoded source length and unary query size.
No list expansion or unit-cost arithmetic appears in the execution theorem. -/
theorem budget_polynomial (query : ℕ) (ps : List (ℕ × ℕ)) :
    budget query ps ≤ 1000*((stream ps).length+query+1)^2 := by
  have hL := stream_length ps
  have hD : ps.length ≤ (stream ps).length := by omega
  have hM : mass ps ≤ (stream ps).length := by omega
  have hs := scanCost_le query 0 ps
  have he := encodeIndices_length_le query 0 ps
  have hm := Nat.mul_le_mul hD
    (show 9*query+10*ps.length+215 ≤ 9*query+10*(stream ps).length+215 by omega)
  unfold budget
  nlinarith

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramMagnitudeOffset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact unsigned-pair budget accepted by the offset/signature pipeline. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

theorem denominator_le_scalarBound (Q R : ℕ) (hQ : 1 ≤ Q) :
    2^(R-1) ≤ (8*Q)^(2*R) := by
  calc
    _ ≤ 2^(2*R) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (8*Q)^(2*R) := Nat.pow_le_pow_left (by omega) _

theorem constraintMassBound_le (Q R : ℕ) (hQ : 1 ≤ Q) :
    constraintMassBound Q R ≤ 2*(8*Q)^(2*R) := by
  have h := denominator_le_scalarBound Q R hQ
  unfold constraintMassBound
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime source facts for the closed head setup. No cache output, matrix,
entry evaluator, or running-time witness is supplied in this interface. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

theorem Inputs.metadata_bound (s : Inputs) (v : Fin s.D) :
    LayoutProgram.EntryBank.MetadataBound (PackingMetadata.value s.packing CollisionProgram.encodeType v) s.size := by
  have hinj : Function.Injective (fun v : Fin s.D=>List.replicate v.val true) := by
    intro x y h; apply Fin.ext; simpa using congrArg List.length h
  have hlookup := PackingMetadata.lookup_eq s.packing (fun v=>List.replicate v.val true)
    CollisionProgram.encodeType hinj v
  have hp := GlobalBasisMetadata.payload_length_le _ _ _ hlookup
  change (PackingMetadata.value s.packing CollisionProgram.encodeType v).encode.length ≤ s.metadata.length at hp
  have hs : s.metadata.length ≤ s.size := by unfold Inputs.size; omega
  have hf : ∀ m : GlobalBasisMetadata.Metadata,
      m.block.length ≤ m.encode.length ∧ m.typeCode.length ≤ m.encode.length ∧ m.rank.length ≤ m.encode.length := by
    intro m; cases m <;>
      simp [GlobalBasisMetadata.Metadata.block,GlobalBasisMetadata.Metadata.typeCode,
        GlobalBasisMetadata.Metadata.rank,GlobalBasisMetadata.Metadata.encode,SubexponentialSAT.Encoding.length_frame] <;> omega
  exact ⟨(hf _).1.trans (hp.trans hs),(hf _).2.1.trans (hp.trans hs),(hf _).2.2.trans (hp.trans hs)⟩

theorem Inputs.lookup_bound (s : Inputs) (row col : Fin s.D) :
    LayoutProgram.EntryBank.lookupBudget s.packing row col ≤ s.lookupTime := by
  have hr : row.val ≤ s.D := row.isLt.le
  have hc : col.val ≤ s.D := col.isLt.le
  unfold LayoutProgram.EntryBank.lookupBudget GlobalBasisMetadata.volume Inputs.lookupTime
  change 400*(s.metadata.length+(List.replicate row.val true).length+1)^2+
    400*(s.metadata.length+(List.replicate col.val true).length+1)^2+1 ≤ _
  simp only [List.length_replicate]
  have h1 := Nat.pow_le_pow_left (show s.metadata.length+row.val+1 ≤ s.metadata.length+s.D+1 by omega) 2
  have h2 := Nat.pow_le_pow_left (show s.metadata.length+col.val+1 ≤ s.metadata.length+s.D+1 by omega) 2
  omega

theorem Inputs.column_time_bound (s : Inputs) (v : ℕ) (hv : v < s.n) :
    LayoutFiberSumProgram.budget s.entryTime s.entryLength s.plans.length v s.plans ≤ s.columnTime := by
  have hf := LayoutOwnerFiberProgram.fiberIndices_length_le v 0 s.plans
  rw [s.plans_length] at hf
  have hq := LayoutOwnerFiberProgram.budget_polynomial v s.plans
  have hv' : v ≤ s.n := hv.le
  unfold LayoutFiberSumProgram.budget Inputs.columnTime
  dsimp only
  rw [s.plans_length]
  calc
    _ ≤ 1000*((LayoutOwnerFiberProgram.stream s.plans).length+v+1)^2+18*v+2*s.D+39+
        s.D*(s.entryTime+5*s.D+12+25000*((s.D+1)*(s.entryLength+2)+3)^2+9*(s.entryLength+2)) := by gcongr
    _ ≤ _ := by gcongr

theorem Inputs.column_length_bound (s : Inputs) (v : ℕ) :
    (LayoutOwnerFiberProgram.fiberIndices v 0 s.plans).length*(s.entryLength+2) ≤ s.columnLength := by
  unfold Inputs.columnLength
  apply Nat.mul_le_mul_right
  simpa only [s.plans_length] using LayoutOwnerFiberProgram.fiberIndices_length_le v 0 s.plans

theorem Inputs.column_mass_bound (s : Inputs) (v : ℕ) (hv : v < s.n) :
    (LayoutOwnerFiberProgram.fiberIndices v 0 s.plans).length*
      LayoutProgram.constraintMassBound s.Q s.R ≤ s.offset := by
  have hQ : 1 ≤ s.Q := by have := s.node.isLt; omega
  calc
    _ ≤ s.occurrence*(2*(8*s.Q)^(2*s.R)) :=
      Nat.mul_le_mul (s.fiber_degree v hv) (LayoutProgram.constraintMassBound_le _ _ hQ)
    _ = _ := by unfold Inputs.offset; ring

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeContract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Close the only service premise of the head loop using the actual entry
machine and the bootstrap's produced caches. All budgets are explicit. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem initial_contract_oai (s : Inputs) (a : LeafHeadSetupProgram.Data) (ha : Ready s a)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hw : CacheCorrect s.height (unary s.R) s.width words) :
    LayoutMatrixProgram.EntryContract entry (matrixBase (start s a ra rd rc words))
      s.valid s.relation s.columnTime s.columnLength := by
  apply LayoutFiberSumProgram.nativeEntryContract s.packing words s.width s.power
    s.height s.R s.node (matrixBase (start s a ra rd rc words)) s.plans s.valid
    s.size s.lookupTime s.offset s.columnTime s.columnLength
  · simpa [unary] using hw.1
  · exact hw.2.1
  · simpa [unary] using hw.2.2
  · exact s.power_signed
  · exact s.power_total
  · exact s.power_value
  · exact s.width_node
  · exact s.height_le
  · have := s.node.isLt; omega
  · exact start_cache s a ha ra rd rc words
  · intro j v hv
    exact matrixBase_fiberReady (start s a ra rd rc words) (fun _=>false)
      (LayoutFiberSumProgram.unary j) []
  · simpa [matrixBase,LayoutMatrixProgram.bankPort,Inputs.metadata] using
      (start_low s a ra rd rc words 135 (by decide)).trans ha.metadata
  · simpa [matrixBase,LayoutMatrixProgram.bankPort] using
      (start_low s a ra rd rc words 136 (by decide)).trans ha.plans
  · exact start_size s a ha ra rd rc words hw
  · exact s.plans_length
  · unfold Inputs.size; omega
  · exact fun j v hv=>hv.1
  · exact s.metadata_bound
  · exact s.lookup_bound
  · exact fun j v hv=>s.column_time_bound v hv.2
  · exact fun j v hv=>s.column_length_bound v
  · exact fun j v hv=>s.column_mass_bound v hv.2

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.initial_contract_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.initial_contract_oai
