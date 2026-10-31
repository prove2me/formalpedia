-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:23:10.842734+00:00
-- url     : https://prove2.me/submissions/ad9eb503-fe1e-4d04-a759-34362dec2891

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181
import Definitions.Def_OAIQ081S185
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_prepare_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_prepared_words

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

theorem finish_value {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hdup : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ outputs) (hport : p.2 ∉ ports) :
    (finishState ports outputs a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ outputs, (clearManyState (outputs.map Prod.snd) a).stacks q.2 = [] := by
    intro q hq
    rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
  have hs : p.1 ∉ outputs.map Prod.snd := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    exact hsep p hp q hq he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hport,
    copyMany_value _ _ hdup hc hsep p hp, clearMany_stacks, ite_eq_right hs]

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

theorem workPort_injective {s : ℕ} (hs : s ≤ 288) : Function.Injective (workPort hs) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [workPort] at this
  omega

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

theorem returned_word {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (ho : ∀ q ∈ outs,Protected q.2)
    (hd : (outs.map Prod.snd).Nodup) (p : Fin s × Fin 768) (hp : p ∈ outs) :
    (returned reg hs ins outs a b).stacks p.2=b.stacks p.1 := by
  have hd' : ((outputCopies hs outs).map Prod.snd).Nodup := by
    simpa only [outputCopies,List.map_map,Function.comp_def] using hd
  have hsep : ∀ q ∈ outputCopies hs outs,∀ z ∈ outputCopies hs outs,q.1≠z.2 := by
    intro q hq z hz
    obtain ⟨q',hq',rfl⟩ := List.mem_map.mp hq
    obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
    exact (protected_ne_work hs (ho z' hz') q'.1).symm
  exact (finish_value (workPorts hs) (outputCopies hs outs) _ hd' hsep
    (workPort hs p.1,p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)
    (protected_not_workPorts hs (ho p hp))).trans
      (embedState_stack reg (workPort hs) _ b (workPort_injective hs) p.1)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem addressOutputs_protected : ∀ p∈addressOutputs,Protected p.2 := by simp [addressOutputs,Protected,temporary]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

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

theorem countedState_frame (a : Data) (regs : Fin 8 → Bool) (records : List (List Bool))
    (i : Fin 768) (hi : Protected i) (h647 : i≠647) :
    (countedState a regs records).stacks i=a.stacks i := by
  apply returned_frame rowCountRegs (by decide) rowCountInputs rowCountOutputs a _ i hi
  intro p hp
  simp only [rowCountOutputs,List.mem_singleton] at hp
  subst p
  exact h647

theorem bootState_address (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (bootState a ra rd rc r t records height R width words).stacks 649=List.replicate (t*r) true := by
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ 649 (by decide),
    countedState_frame _ _ _ _ (by decide) (by decide)]
  · exact returned_word addressRegs (by decide) addressInputs addressOutputs a _
      addressOutputs_protected (by decide) (4,649) (by simp [addressOutputs])
  · simp [cacheOutputs]

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid node-start loading of the parked source bank. Only the original
layout copy program is called; no head enumeration is imported or executed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open LeafProgram LeafHeadSetupProgram

theorem result_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound B (result a) := by
  intro i
  by_cases he : ∃ j : Fin 14,stackMap (LayoutMasters.low j)=i
  · obtain ⟨j,rfl⟩ := he
    rw [result_low]
    exact ha _
  by_cases hc : i ∈ clearPorts
  · rcases List.mem_append.mp hc with hc|hc
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl
      · change ((result a).stacks (stackMap 684)).length ≤ B
        rw [result_empty a 684 (by decide)]
        exact Nat.zero_le B
      · change ((result a).stacks (stackMap 660)).length ≤ B
        rw [result_empty a 660 (by decide)]
        exact Nat.zero_le B
      · change ((result a).stacks (stackMap 665)).length ≤ B
        rw [result_empty a 665 (by decide)]
        exact Nat.zero_le B
    · obtain ⟨j,hj,hij⟩ := List.mem_map.mp hc
      obtain ⟨k,_,hk⟩ := List.mem_map.mp hj
      exact False.elim (he ⟨k,hk ▸ hij⟩)
  · rw [result_frame a i hc]
    exact ha i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/
section NativeValidity

namespace Good

variable {n B d u J : ℕ} {vars : Finset (Fin n)}

 theorem nil : Good (B := B) (d := d) vars u J [] :=
  ⟨by simp, by simp [Squarefree.Sparse.keys]⟩

end Good


end NativeValidity

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAssembler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/
namespace Nodes



theorem installed_at (a : Data) (b : LowData) (i : Fin 896) (hi : i.val<768) :
    (installed a b).stacks i=b.stacks ⟨i.val,hi⟩ := by
  have hh : lowPort ⟨i.val,hi⟩=i := Fin.ext rfl
  simpa only [hh] using installed_low a b ⟨i.val,hi⟩

theorem readLow_stacks (a : Data) (bits : List Bool) (tail : List (List Bool)) (i : Fin 768) :
    (readLow a bits tail).stacks i=
      if i=301 then Encoding.encodeList id tail else if i=302 then [] else
        if i=78 then bits else (low (clearedNode a)).stacks i := by
  by_cases h301 : i=301
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  by_cases h302 : i=302
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  by_cases h78 : i=78
  · subst i
    simp [readLow,RingNodeSetup.nodeRead,OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes]
  simp only [h301,h302,h78,ite_false]
  exact readLow_frame a bits tail i h301 h302 h78

theorem begunNode_stacks (a : Data) (bits : List Bool) (tail : List (List Bool)) (i : Fin 896) :
    (begunNode a bits tail).stacks i=
      if i=301 then Encoding.encodeList id tail else if i=78 then bits else
        if i∈nodeResetPorts then [] else a.stacks i := by
  by_cases hlo : i.val<768
  · let j : Fin 768 := ⟨i.val,hlo⟩
    have hj : lowPort j=i := Fin.ext rfl
    have h301 : (j=301) ↔ (i=301) := by simp [j,Fin.ext_iff]
    have h302 : (j=302) ↔ (i=302) := by simp [j,Fin.ext_iff]
    have h78 : (j=78) ↔ (i=78) := by simp [j,Fin.ext_iff]
    rw [begunNode,installed_at _ _ i hlo]
    change (readLow a bits tail).stacks j=_
    rw [readLow_stacks]
    simp only [h301,h302,h78]
    change (if i=301 then Encoding.encodeList id tail else if i=302 then [] else
      if i=78 then bits else (clearedNode a).stacks (lowPort j))=_
    rw [hj,clearedNode,NodeReadoutSpace.clearedMany_stack]
    by_cases h : i=302
    · simp [h,nodeResetPorts]
    · simp only [h,ite_false]
  · have hh := installed_high (clearedNode a) (readLow a bits tail) i (by omega)
    rw [begunNode,hh,clearedNode,NodeReadoutSpace.clearedMany_stack]
    have h301 : i≠301 := by intro h; subst i; exact hlo (by decide)
    have h78 : i≠78 := by intro h; subst i; exact hlo (by decide)
    simp [h301,h78]

theorem begunNode_bound (a : Data) (bits : List Bool) (tail : List (List Bool)) (B : ℕ)
    (hb : ∀ i,(a.stacks i).length ≤ B) (hbits : bits.length ≤ B)
    (htail : (Encoding.encodeList id tail).length ≤ B) :
    ∀ i,((begunNode a bits tail).stacks i).length ≤ B := by
  intro i
  rw [begunNode_stacks]
  split_ifs
  · exact htail
  · exact hbits
  · exact Nat.zero_le _
  · exact hb i


end Nodes


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

namespace PairAccumulatorMeaning

theorem zero {r Q n d : ℕ} (q : Factor.Spec r Q n d) (a : Data)
    (hz : a.stacks 851=[]) : PairAccumulatorMeaning q 0 a := by
  refine ⟨[],?_,Good.nil,?_⟩
  · exact hz
  · rw [rawValue_nil,map_zero]

end PairAccumulatorMeaning

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem bootstrapResult_masters (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :
    MasterFrame (Native.start s a ra rd rc words) (bootstrapResult s a ra rd rc words) := by
  constructor
  intro i hi
  have h660 : i≠660 := by
    intro h; subst i
    exact (by decide : (660 : Fin 768)∉masters) hi
  have h665 : i≠665 := by
    intro h; subst i
    exact (by decide : (665 : Fin 768)∉masters) hi
  simp only [Native.start,nodeStart,tupleInitialized,bootstrapResult,
    Function.update_of_ne h660,Function.update_of_ne h665]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceParametersBytes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact byte identities for the pure parameter package. These identify the
native interpolation producer outputs with the source bank cache fields. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters
open SubexponentialSAT BitProgram SubexpLiftRing IntegerRingLiftProgram

variable {r Q d : ℕ}

theorem inverseBytes_eq (p : SourceBank.Parameters r Q d) :
    InterpolationCacheProgram.inverseBytes p.t p.model p.modulus p.cache p.minusOne
      (LeafRingSetupProgram.nodeWords p.t d Q) =
      (List.ofFn (fun i : Fin Q => RingProgram.flat (p.inverse i))).flatten := by
  simp [InterpolationCacheProgram.inverseBytes,LeafRingSetupProgram.nodeWords,
    List.finRange,List.flatMap_def,List.map_ofFn,Function.comp_def,
    inverse,nodeCache,SourceCache.native]

theorem negativeBytes_eq (p : SourceBank.Parameters r Q d) :
    InterpolationCacheProgram.negativeBytes p.t p.model p.modulus p.cache p.minusOne
      (LeafRingSetupProgram.nodeWords p.t d Q) =
      (List.ofFn (fun i : Fin Q => RingProgram.flat (p.negative i))).flatten := by
  simp [InterpolationCacheProgram.negativeBytes,LeafRingSetupProgram.nodeWords,
    List.finRange,List.flatMap_def,List.map_ofFn,Function.comp_def,
    negative,nodeCache,SourceCache.native]

theorem differenceBytes_eq (p : SourceBank.Parameters r Q d) :
    InterpolationCacheProgram.differenceBytes p.t p.model p.modulus p.cache p.minusOne
      (LeafRingSetupProgram.nodeWords p.t d Q) =
      (List.ofFn (fun i : Fin Q =>
        (List.ofFn (fun j : Fin Q => RingProgram.flat (p.difference i j))).flatten)).flatten := by
  simp [InterpolationCacheProgram.differenceBytes,InterpolationCacheProgram.rowBytes,
    LeafRingSetupProgram.nodeWords,List.finRange,List.flatMap_def,List.map_ofFn,
    Function.comp_def,difference,nodeCache,SourceCache.native]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A typed factor specification using the original query's row stream and
marked-clause selector. Finite-index transports do not alter stored bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics MomentsProgram
noncomputable section

theorem castRows_bytes {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m) (b : ℕ) :
    HashScopeProgram.RawTable.inputBits b (castRows h rows)=HashScopeProgram.RawTable.inputBits b rows := by
  subst m'
  simp [castRows]

theorem factorSpec_row_bytes {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : ConstructivePacking.PackingData (Fin ps.length) (UniversalType r Q 1))
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin n)))) (hc : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t)
    (code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)) :
    Encoding.encodeList id (factorSpec p ps P q hv J hJ source hc theta width hw code).rawRows=
      HashScopeProgram.RawTable.inputBits q.width.length q.rows := by
  change Encoding.encodeList id ((castRows (congrArg List.length hc) q.rows).map
    (fun ts => (HashInputProgram.Loop.rawInput q.width.length ts).reverse))=_
  simp only [HashInputProgram.Loop.rawInput,List.reverse_reverse]
  exact castRows_bytes _ _ _

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedFactorFields
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Projection identities are proved before instantiating the numeric query
model, keeping the large generated parameter expression opaque. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

variable (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33)) (half : RingProgram.ScalarCode 3 (m.val 33))
    (e : LeafRingSetupProgram.Data) (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp hfield q hv J hJ source hsource

theorem nativeSpecOfInputs_code : e.stacks 281=RingProgram.flat (spec).code := (generatedCode hp).bytes

theorem nativeSpecOfInputs_rows : Encoding.encodeList id (spec).rawRows=
    HashScopeProgram.RawTable.inputBits q.width.length q.rows :=
  factorSpec_row_bytes _ _ _ _ _ _ _ _ _ _ _ _ _

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReadyConstruction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query-entry facts from the actual arithmetic and native cache
producers. Pair masks are installed by the paid pair-start command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram LeafProgram LeafProgram.PreparedSource
open LeafHeadSetupProgram QueryTupleState
open ProgramTapeReplay
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Assemble the common physical data for the authentic factor specification
from the actual arithmetic output, native layout masters, bootstrap caches
and frontend words. The frame equations refer to concrete producer states. -/
theorem native_common
    (s : Native.Inputs) (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool)) (hc : CacheCorrect s.height (unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
    (hfield : s.Q < 3 ^ (m.val 34)) (hQ : m.val 21 = s.Q)
    (hR : (base.stacks 740).length=s.R) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (hJ : 0 < m.val 42) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (H : Finset (Fin s.n)) (high : H → Bool) (P : ℕ) (a : State 40 896)
    (hnative : Native.Ready s
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hframe : ∀ i∈arithmeticPorts, a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (htheta : a.stacks 78=RingProgram.flat
      (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1)))
    (hpositive : a.stacks 710=(LayoutProgramScalar.FromCounts.unsignedSaved words
      s.width s.power s.R s.height).hp)
    (hnegative : a.stacks 711=(LayoutProgramScalar.FromCounts.unsignedSaved words
      s.width s.power s.R s.height).hn)
    (hpower : a.stacks 712=s.power.1)
    (h700 : a.stacks 700=Encoding.encodeList id q.clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows)
    (h704 : a.stacks 704=List.replicate q.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex q))
    (h706 : a.stacks 706=[q.mark.isSome])
    (h707 : a.stacks 707=q.modulus) (h708 : a.stacks 708=q.width)
    (h702 : a.stacks 702=List.ofFn (fun v : Fin s.n => decide (v∈H)))
    (h703 : a.stacks 703=List.ofFn (fun v : Fin s.n => if h:v∈H then high ⟨v,h⟩ else false))
    (hbound : ∀ i ∈ commonPorts, (a.stacks i).length ≤ P) :
    CommonReady (nativeSpecOfInputs s m ht hd words hc M cache half e ho.produced
      hfield q hv (m.val 42) hJ source hsource) s.node H high P a := by
  let spec := nativeSpecOfInputs s m ht hd words hc M cache half e ho.produced
    hfield q hv (m.val 42) hJ source hsource
  have low (i : Fin 640) (hi : i∈([194,201,202,203,207,211,212,243,280,281] : List (Fin 640))) :
      a.stacks ((LeafRingSetupProgram.wideStacks i).castAdd 128)=e.stacks i := by
    have hm : LeafRingSetupProgram.wideStacks i∈arithmeticPorts := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hl : i.val<340 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (hframe _ hm).trans (ho.low i hl)
  refine {
    lifting := rfl
    generatedTheta := rfl
    sourceMinus := rfl
    ambient := hnative.ambient
    theta := htheta
    modulus := (low 194 (by decide)).trans ho.produced.caches.modulus
    table := (low 201 (by decide)).trans ho.produced.native.table
    width := low 202 (by decide)
    scalarZero := (low 203 (by decide)).trans ho.produced.caches.scalarZero
    degree := (hframe 204 (by decide)).trans hdegree
    one := (low 207 (by decide)).trans ho.produced.caches.fullOne_model
    minus := (low 211 (by decide)).trans
      (ho.produced.caches.fullMinusOne.trans (LeafProgram.Constants.constantCode_flat _ _ _).symm)
    precision := (low 212 (by decide)).trans ho.produced.caches.precision
    order := (low 243 (by decide)).trans ho.produced.jetOrder
    zero := (low 280 (by decide)).trans ho.produced.caches.fullZero_model
    code := (low 281 (by decide)).trans (nativeSpecOfInputs_code s m ht hd words hc M cache
      half e ho.produced hfield q hv (m.val 42) hJ source hsource)
    clauses := ?_
    rows := h701.trans (nativeSpecOfInputs_rows s m ht hd words hc M cache half e
      ho.produced hfield q hv (m.val 42) hJ source hsource).symm
    rowCount := ?_
    markedIndex := h705
    markedFlag := h706
    indexModulus := ?_
    indexWidth := congrArg List.length h708
    highMask := h702
    highBits := h703
    colors := hnative.colors
    nodes := hnative.nodes
    typeWidth := hnative.wordWidth
    positive := hpositive
    negative := hnegative
    sourceWidth := hnative.width
    power := hpower
    powerNegative := rfl
    radius := hnative.order
    offset := hnative.height
    metadata := ?_
    plans := hnative.plans
    inverses := ?_
    negatives := ?_
    differences := ?_
    ringWidth := (hframe 717 (by decide)).trans ho.width
    rowWidth := ?_
    inverseDenominator := ?_
    cacheCaps := ?_
    ambientCap := hbound 128 (by decide)
    oneCap := hbound 207 (by decide) }
  · exact h700.trans (congrArg (Encoding.encodeList id) hsource)
  · change a.stacks 704=List.replicate
      (((castRows (congrArg List.length hsource) q.rows).map
        (fun ts=>(HashInputProgram.Loop.rawInput q.width.length ts).reverse)).length) true
    simpa only [List.length_map,castRows_length] using h704
  · change BinaryArithmetic.toNat (a.stacks 707)=
      (HashInputProgram.Expansion.encodedClauses source).length
    rw [h707,←hsource]
    exact hv.2.2.2.2.2.1
  · change a.stacks 135=OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.rawRecords
      (OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata.records
        (PackingIncidenceInput.reindexPacking s.plans_length.symm s.packing)
        (fun v=>List.replicate v.val true) OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram.encodeType)
    rw [PackingIncidenceInput.reindexPacking_metadataBytes]
    exact hnative.metadata
  · refine (hframe 713 (by decide)).trans ?_
    rw [ho.inverse,hQ]
    exact LayoutProgram.SourceBank.Parameters.inverseBytes_eq spec.p
  · refine (hframe 714 (by decide)).trans ?_
    rw [ho.negative,hQ]
    exact LayoutProgram.SourceBank.Parameters.negativeBytes_eq spec.p
  · refine (hframe 715 (by decide)).trans ?_
    rw [ho.difference,hQ]
    exact LayoutProgram.SourceBank.Parameters.differenceBytes_eq spec.p
  · refine (hframe 716 (by decide)).trans ?_
    rw [ho.nodesLength,hQ]
    rfl
  · refine (hframe 728 (by decide)).trans ?_
    rw [ho.denominator,hR]
    rfl
  · intro p hp
    apply hbound
    simp only [LeafNodeCacheProgram.directCopies, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairCommit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The signed finite-difference term is committed to the actual node word.
The pair product and the node sum use the same stored dictionaries as their
validity and readout witnesses. Marker readout remains additive. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram
open TruncatedRingProgram QueryProgram QueryTupleState

namespace NodeAccumulatorMeaning

theorem zero {r Q n d : ℕ} (q : Factor.Spec r Q n d) (a : Data)
    (hz : a.stacks 850=[]) : NodeAccumulatorMeaning q 0 a := by
  refine ⟨[],hz,Good.nil,?_⟩
  rw [rawValue_nil,map_zero]

end NodeAccumulatorMeaning

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

theorem bootstrapped_low (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (i : Fin 768) :
    (bootstrapped s a ra rd rc words).stacks (QueryAssembler.Nodes.lowPort i)=
      (SignatureHeadLoader.bootstrapResult s
        (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort a) ra rd rc words).stacks i :=
  embedState_stack _ _ _ _ (Fin.castAdd_injective 768 128) i

/-- Every arithmetic word used by the authentic factor constructor is in the
proved frame of this actual prefix. -/
theorem arithmetic_mem_frame (i : Fin 768) (hi : i ∈ QueryReadyConstruction.arithmeticPorts) :
    i.castAdd 128 ∈ framePorts := by
  simp only [QueryReadyConstruction.arithmeticPorts,List.mem_cons,
    List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

theorem sourceSnapshot_bound (a : Data) (bits : List Bool) (tail : List (List Bool)) (B : ℕ)
    (hc : a.stacks 301=Encoding.encodeList id (bits::tail)) (hb : WordBound B a) :
    WordBound B (sourceSnapshot a bits tail) := by
  have hencoded := hb 301
  rw [hc,Encoding.length_encodeList_cons] at hencoded
  have hbits : bits.length ≤ B := by simp only [id_eq] at hencoded; omega
  have htail : (Encoding.encodeList id tail).length ≤ B := by omega
  have hbegun := QueryAssembler.Nodes.begunNode_bound a bits tail B hb hbits htail
  exact fun i => NativeLayoutLoad.result_bound _ B hbegun (QueryAssembler.Nodes.lowPort i)

/-- The actual native cache witness is coupled to its source snapshot and
current head masters, with the real starting address on649. -/
theorem prepared_source (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool))
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) (b : Data)
    (hf : ∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
      b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) :
    SignatureHeadLoader.MasterFrame (Native.start s (sourceSnapshot a bits tail) ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) ∧
      b.stacks 649=unary (s.node.val*s.r) := by
  constructor
  · constructor
    intro i hi
    have hn : QueryAssembler.Nodes.lowPort i ∉ PairNativeSetup.scratch ∧
        QueryAssembler.Nodes.lowPort i ≠ 832 ∧ QueryAssembler.Nodes.lowPort i ≠ 833 ∧
        QueryAssembler.Nodes.lowPort i ≠ 834 ∧ QueryAssembler.Nodes.lowPort i ≠ 835 := by
      simp only [SignatureHeadLoader.masters,List.mem_cons,
        List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    exact (hf _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).trans
      ((bootstrapped_low s _ ra rd rc words i).trans
        ((SignatureHeadLoader.bootstrapResult_masters s _ ra rd rc words).stored i hi))
  · rw [hf 649 (by decide) (by decide) (by decide) (by decide) (by decide)]
    have hlow := bootstrapped_low s (loadedNode a bits tail) ra rd rc words 649
    change (bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks
      (QueryAssembler.Nodes.lowPort 649)=_
    rw [hlow,SignatureHeadLoader.bootstrapResult,
      retainedState_frame _ 649 (by decide) (by decide) (by decide) (by decide)]
    exact bootState_address _ ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

/-- The concrete node prefix constructs its authentic query specification
from the actual arithmetic output and its freshly produced cache witness.
Neither pair mask is assumed on entry; both accumulators are physically empty. -/
theorem prepare_native_run_oai
    (s : Native.Inputs) (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (base out : State 40 768) (ho : Query.ArithmeticOutput base out m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (hQ : m.val 21=s.Q)
    (hR : (base.stacks 740).length=s.R) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (hJ : 0 < m.val 42) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (H : Finset (Fin s.n)) (high : H → Bool) (B : ℕ) (a : Data)
    (hbank : NativeLayoutLoad.SourceBank s a)
    (tail : List (List Bool))
    (hcursor : a.stacks 301=Encoding.encodeList id
      (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))::tail))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (hframe : ∀ i ∈ QueryReadyConstruction.arithmeticPorts,a.stacks (i.castAdd 128)=out.stacks i)
    (hdegree : out.stacks 204=List.replicate (m.val 34) true)
    (h700 : a.stacks 700=Encoding.encodeList id q.clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows)
    (h704 : a.stacks 704=List.replicate q.rows.length true)
    (h705 : a.stacks 705=Encoding.encodeNat (markIndex q))
    (h706 : a.stacks 706=[q.mark.isSome])
    (h707 : a.stacks 707=q.modulus) (h708 : a.stacks 708=q.width)
    (h702 : a.stacks 702=List.ofFn (fun v : Fin s.n => decide (v ∈ H)))
    (h703 : a.stacks 703=List.ofFn (fun v : Fin s.n => if h:v ∈ H then high ⟨v,h⟩ else false))
    (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B) :
    ∃ (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)),
    ∃ hw : CacheCorrect s.height (unary s.R) s.width words, ∃ ticks b,
      let snap := sourceSnapshot a
        (RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (s.node.val+1))) tail
      let spec := nativeSpecOfInputs s m ht hd words hw M cache half e ho.produced
        hfield q hv (m.val 42) hJ source hsource
      Eval prepareNode ticks a b ∧ ticks ≤ 20000*(B+1)^4+300*(B+1) ∧
      WordBound B b ∧ QueryReadyConstruction.CommonReady spec s.node H high B b ∧
      QueryPairCommit.NodeAccumulatorMeaning spec 0 b ∧ PairAccumulatorMeaning spec 0 b ∧
      b.stacks 832=List.replicate (s.n-H.card) true ∧ b.stacks 833=List.replicate spec.J true ∧
      b.stacks 834=[] ∧ b.stacks 835=[] ∧
      b.stacks 301=Encoding.encodeList id tail ∧ b.stacks 307=a.stacks 307 ∧
      b.stacks 863=a.stacks 863 ∧ (∀ i ∈ framePorts,b.stacks i=a.stacks i) ∧
      Native.Ready s snap ∧ WordBound B snap ∧
      SignatureHeadLoader.MasterFrame (Native.start s snap ra rd rc words)
        (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) ∧
      b.stacks 649=unary (s.node.val*s.r) ∧
      Trace (compiled prepareNode 301 832) (ticks+1)
        (a.withPC (some (compiled prepareNode 301 832).entry)) (b.withPC none) ∧
      ∀ k z,k ≤ ticks+1 → Trace (compiled prepareNode 301 832) k
        (a.withPC (some (compiled prepareNode 301 832).entry)) z →
        ∀ i,(z.stacks i).length ≤ 896*B+20000*(B+1)^4+300*(B+1)+1 := by
  have horder : a.stacks 243=List.replicate (m.val 42) true :=
    (hframe 243 (by decide)).trans ((ho.low 243 (by decide)).trans ho.produced.jetOrder)
  obtain ⟨ra,rd,rc,words,ticks,b,hw,he,htime,hB,hnative,h832,h833,h834,h835,h850,h851,
      _hscratch,hf,htrace,hprefix⟩ :=
    prepare_eval s a _ tail H (m.val 42) B hbank hcursor hmask horder hb hcap
  obtain ⟨htheta,hcursor',hframe',hpositive,hnegative,hpower⟩ :=
    prepared_words s a _ tail ra rd rc words b hf
  have harith (i : Fin 768) (hi : i ∈ QueryReadyConstruction.arithmeticPorts) :
      b.stacks (i.castAdd 128)=out.stacks i :=
    (hframe' _ (arithmetic_mem_frame i hi)).trans (hframe i hi)
  have hcommon := QueryReadyConstruction.native_common s m ht hd words hw M cache half e
    base out ho hfield hQ hR q hv hJ source hsource H high B b hnative harith hdegree htheta
    hpositive hnegative hpower
    ((hframe' 700 (by decide)).trans h700) ((hframe' 701 (by decide)).trans h701)
    ((hframe' 704 (by decide)).trans h704) ((hframe' 705 (by decide)).trans h705)
    ((hframe' 706 (by decide)).trans h706) ((hframe' 707 (by decide)).trans h707)
    ((hframe' 708 (by decide)).trans h708) ((hframe' 702 (by decide)).trans h702)
    ((hframe' 703 (by decide)).trans h703) (fun i _ => hB i)
  obtain ⟨hmasters,haddress⟩ := prepared_source s a _ tail ra rd rc words b hf
  refine ⟨ra,rd,rc,words,hw,ticks,b,he,htime,hB,hcommon,
    QueryPairCommit.NodeAccumulatorMeaning.zero _ b h850,
    PairAccumulatorMeaning.zero _ b h851,h832,h833,h834,h835,hcursor',
    hframe' 307 (by decide),hframe' 863 (by decide),hframe',
    sourceSnapshot_ready s a _ tail hbank,sourceSnapshot_bound a _ tail B hcursor hb,
    hmasters,haddress,htrace,hprefix⟩

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run_oai
