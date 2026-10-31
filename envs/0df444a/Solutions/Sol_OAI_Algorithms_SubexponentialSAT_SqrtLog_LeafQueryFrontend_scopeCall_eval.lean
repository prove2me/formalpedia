-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeCall_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:58:06.566535+00:00
-- url     : https://prove2.me/submissions/d1eba012-314b-46c0-b74f-e46d7662b2ff

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S130
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashScopeProgram_Complete_runRows_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashScopeProgram_Marked_optional_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecLiteralDedupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual stable literal deduplication

The fixed program tests each record against the remaining records, retains its
last occurrence, and restores record order. All membership, copy, emission,
and reversal calls are concrete finite programs with measured executions.
-/

namespace SubexponentialSAT.ExecLiteralDedupProgram

open BitProgram StructuredCalls

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  simp [ProgramEncoding.encodeRecords_length, List.map_reverse]

end SubexponentialSAT.ExecLiteralDedupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact scopes of the physically stored sparse raw rows and optional original
marked clause. These definitions are shared by the machine and resource proofs. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
namespace Complete

theorem outputBits_nested (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    outputBits (clauses := clauses) t d codes rows mark=Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (scopes (clauses := clauses) t d codes rows mark) := by
  have h : scopeWords (clauses := clauses) t d codes rows mark=(scopes (clauses := clauses) t d codes rows mark).map (Encoding.encodeList Encoding.encodeNat) := by
    simp [scopeWords,scopes,RawTable.scopeBytes,List.map_map,Function.comp_def]
  unfold outputBits
  rw [h]
  generalize scopes (clauses := clauses) t d codes rows mark=ss
  induction ss with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList,ih]

end Complete
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct table adapter: raw clause-reference rows to deduplicated scope rows.
The original source table and all decoding parameters remain on their tapes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem reverseRegisters_injective : Function.Injective reverseRegisters := by decide
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

private theorem embed_reverse (rf : Fin 11 → Bool) (v p f : Bool)
    (width modulus master shape source output pay oldSource oldOut : List Bool) :
    embedState reverseRegisters reverseStacks (state rf width modulus master shape oldSource [] oldOut)
      (SubexpNormalizeProgram.filterState v p f source [] output pay) =
        state (flags rf v p f) width modulus master shape output pay source := by
  apply embedState_eq_of_ports _ _ _ _ _ reverseRegisters_injective reverseStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i≠8 := fun h => hi ⟨0,h.symm⟩
    have h9 : i≠9 := fun h => hi ⟨1,h.symm⟩
    have h10 : i≠10 := fun h => hi ⟨2,h.symm⟩
    simp [state,data,flags,h8,h9,h10]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h48 : i≠48 := fun h => hi ⟨0,h.symm⟩
    have h46 : i≠46 := fun h => hi ⟨2,h.symm⟩
    have h47 : i≠47 := fun h => hi ⟨3,h.symm⟩
    simp [state,data,h48,h46,h47]

theorem reverse_eval (rf : Fin 11 → Bool) (width modulus master shape : List Bool)
    (records : List (List Bool)) :
    ∃ n ≤ 10*(Encoding.encodeList id records).length,
      Eval reverse n
        (state (flags rf false true false) width modulus master shape [false] [] (Encoding.encodeList id records))
        (state (flags rf false true false) width modulus master shape (Encoding.encodeList id records.reverse) [] []) := by
  let a := state (flags rf false true false) width modulus master shape [false] [] (Encoding.encodeList id records)
  let z := SubexpNormalizeProgram.filterState false true false [] [] (Encoding.encodeList id records.reverse) []
  have ha : restrictState reverseRegisters reverseStacks a=
      SubexpNormalizeProgram.filterState false true false (Encoding.encodeList id records) [] [false] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have h := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] [] false true false
  obtain ⟨n,hn,he⟩ := lifted_call SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reverseStacks
    reverseRegisters_injective reverseStacks_injective a z (10*(Encoding.encodeList id records).length)
    (by simpa [ha, z, Encoding.encodeList] using h)
  exact ⟨n,hn,by simpa [a,z,embed_reverse,flags_idem,reverse] using he⟩

theorem appendScopes_encoded (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : Rows clauses.length) (acc : List (List Bool)) :
    appendScopes (clauses := clauses) t d codes rows (Encoding.encodeList id acc)=
      Encoding.encodeList id ((rows.map (scopeBytes (clauses := clauses) t d codes)).reverse++acc) := by
  induction rows generalizing acc with
  | nil => simp [appendScopes]
  | cons row rows ih =>
      change appendScopes (clauses := clauses) t d codes rows (SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes row)
        (Encoding.encodeList id acc))=_
      change appendScopes (clauses := clauses) t d codes rows (Encoding.encodeList id (scopeBytes (clauses := clauses) t d codes row::acc))=_
      rw [ih]
      simp [List.reverse_cons,List.append_assoc]

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTableCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _

private theorem restrict_data (rf : Fin 11 → Bool) (width modulus master shape source out index flag : List Bool) :
    restrictState id lowStacks (data rf width modulus master shape source out index flag)=
      RawTable.state rf width modulus master shape source [] out := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext j; fin_cases j <;> rfl

private theorem embed_data (rf rr : Fin 11 → Bool)
    (width modulus master shape oldSource oldOut source out index flag : List Bool) :
    embedState id lowStacks (data rf width modulus master shape oldSource oldOut index flag)
      (RawTable.state rr width modulus master shape source [] out)=
        data rr width modulus master shape source out index flag := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id lowStacks_injective
  · intro j; rfl
  · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h46 : j≠46 := fun h => hj ⟨46,h.symm⟩
    have h48 : j≠48 := fun h => hj ⟨48,h.symm⟩
    simp [data,Marked.tapes,h46,h48]

theorem runReverse_eval (rf : Fin 11 → Bool) (width modulus master shape : List Bool)
    (records : List (List Bool))
    (h8 : rf 8=false) (h9 : rf 9=true) (h10 : rf 10=false) :
    ∃ n ≤ 10*(Encoding.encodeList id records).length+1,
      Eval runReverse n
        (data rf width modulus master shape [false] (Encoding.encodeList id records) [] [])
        (data rf width modulus master shape (Encoding.encodeList id records.reverse) [] [] []) := by
  have hf : RawTable.flags rf false true false=rf := by
    funext j
    by_cases h8j : j=8 <;> by_cases h9j : j=9 <;> by_cases h10j : j=10 <;>
      simp_all [RawTable.flags]
  obtain ⟨nr,hnr,hr⟩ := RawTable.reverse_eval rf width modulus master shape records
  rw [hf] at hr
  let a := data rf width modulus master shape [false] (Encoding.encodeList id records) [] []
  let z := RawTable.state rf width modulus master shape (Encoding.encodeList id records.reverse) [] []
  have hrun : RunsIn reverseProgram (10*(Encoding.encodeList id records).length+1)
      ((restrictState id lowStacks a).withPC (some reverseProgram.entry)) (z.withPC none) := by
    rw [restrict_data]
    exact ⟨nr+1,Nat.add_le_add_right hnr 1,compiled_halt_trace hr 46 46⟩
  obtain ⟨n,hn,he⟩ := lifted_call reverseProgram id lowStacks Function.injective_id lowStacks_injective a z
    (10*(Encoding.encodeList id records).length+1) hrun
  exact ⟨n,hn,by simpa [runReverse,a,z,embed_data] using he⟩

theorem initialize_eval (width modulus master shape source index flag : List Bool) :
    Eval initializeCmd 2 (data RawTable.zeroRegs width modulus master shape source [] index flag)
      (data RawTable.zeroRegs width modulus master shape source [false] index flag) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (48 : Fin 80) (8 : Fin 11) false
    (data RawTable.zeroRegs width modulus master shape source [] index flag)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext j; fin_cases j <;> simp [data,RawTable.zeroRegs]
  · funext j; fin_cases j <;> simp [data,Marked.tapes]

theorem seed_eval (rf : Fin 11 → Bool) (width modulus master shape out : List Bool) (h8 : rf 8=false) :
    Eval seed 2 (Marked.data rf width modulus master shape out [] [] [] [] [])
      (data rf width modulus master shape [false] out [] []) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (46 : Fin 80) (8 : Fin 11) false
    (Marked.data rf width modulus master shape out [] [] [] [] [])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext j; by_cases hj : j=8 <;> simp_all [data,Marked.data,SubexponentialSAT.Subexp.TupleProgram.pushedState]
  · funext j; fin_cases j <;> simp [data,Marked.data,Marked.tapes]

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete physical scope stream, including the optional marked factor.
The final row order is all raw hash rows followed by the marked clause if present. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


theorem appended_scopeWords (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    Marked.appended (clauses := clauses) codes mark
      (Encoding.encodeList id (rows.map (RawTable.scopeBytes (clauses := clauses) t d codes)).reverse)=
      Encoding.encodeList id (scopeWords (clauses := clauses) t d codes rows mark).reverse := by
  cases mark <;> simp [Marked.appended,scopeWords,SubexponentialSAT.Subexp.TupleProgram.prependRecord,Encoding.encodeList]

theorem program_runsIn (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (mark : Option (Fin clauses.length)) (index : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (width modulus shape : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, RunsIn program (cost t d b modulus clauses codes rows mark index)
      ((data RawTable.zeroRegs width modulus (Encoding.encodeList id clauses) shape
        (RawTable.inputBits b rows) [] index [mark.isSome]).withPC (some program.entry))
      ((data rf width modulus (Encoding.encodeList id clauses) shape (outputBits (clauses := clauses) t d codes rows mark) [] [] []).withPC none) := by
  have hi := initialize_eval width modulus (Encoding.encodeList id clauses) shape (RawTable.inputBits b rows) index [mark.isSome]
  obtain ⟨nr,hnr,rr,hr⟩ := runRows_eval t d ht b hb clauses codes hc rows hbound width modulus shape [false] index [mark.isSome]
    hw hm hshape
  have ha := RawTable.appendScopes_encoded (clauses := clauses) t d codes rows []
  simp only [Encoding.encodeList,List.append_nil] at ha
  rw [ha] at hr
  obtain ⟨nm,hnm,rm,h8,h9,h10,hmark⟩ := Marked.optional_eval clauses codes hc mark index hindex rr width modulus shape
    (Encoding.encodeList id (rows.map (RawTable.scopeBytes (clauses := clauses) t d codes)).reverse)
  rw [appended_scopeWords] at hmark
  have hs := seed_eval rm width modulus (Encoding.encodeList id clauses) shape
    (Encoding.encodeList id (scopeWords (clauses := clauses) t d codes rows mark).reverse) h8
  obtain ⟨nv,hnv,hv⟩ := runReverse_eval rm width modulus (Encoding.encodeList id clauses) shape
    (scopeWords (clauses := clauses) t d codes rows mark).reverse h8 h9 h10
  simp only [List.reverse_reverse] at hv
  have hlen : (Encoding.encodeList id (scopeWords (clauses := clauses) t d codes rows mark).reverse).length=
      (outputBits (clauses := clauses) t d codes rows mark).length := ExecLiteralDedupProgram.encoded_reverse_length _
  rw [hlen] at hnv
  refine ⟨rm,2+(nr+(nm+(2+nv)))+1,by unfold cost; omega,?_⟩
  exact compiled_halt_trace (hi.seq (hr.seq (hmark.seq (hs.seq hv)))) 46 46

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

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
theorem block_injective (base n : ℕ) (hn : base+n ≤ 768) : Function.Injective (block base n hn) := by
  intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp [block] at this; omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem call_run {r s l : ℕ} (p : Program r s l) (rr : Fin r → Fin 40)
    (ss : Fin s → Fin 768) (hr : Function.Injective rr) (hs : Function.Injective ss)
    (a : Data) (b : State r s) (B : ℕ)
    (h : RunsIn p B ((projectState rr ss a).withPC (some p.entry)) (b.withPC none)) :
    ∃ n ≤ B, Eval (.call (ProgramLinking.liftProgram p rr ss)) n a (embedState rr ss a b) := by
  obtain ⟨n,hn,ht⟩ := h
  exact ⟨n,hn,eval_call_from_state p rr ss a hr hs ht⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendScopeCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scope-only parsing uses a fixed t=1,d=0 dummy scalar shape. It requires
no ring parameter input and retains every hash and optional marked row. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem scopeCall_eval_oai (a : Data) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : HashScopeProgram.RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (mark : Option (Fin clauses.length)) (index width modulus : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hw : width.length=b) (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hp : projectState r11 scopes a = HashScopeProgram.Complete.data
      HashScopeProgram.RawTable.zeroRegs width modulus (Encoding.encodeList id clauses)
      [false,false] (HashScopeProgram.RawTable.inputBits b rows) [] index [mark.isSome]) :
    ∃ n ≤ HashScopeProgram.Complete.cost 1 0 b modulus clauses codes rows mark index, ∃ rf,
      Eval scopeCall n a (embedState r11 scopes a (HashScopeProgram.Complete.data rf
        width modulus (Encoding.encodeList id clauses) [false,false]
        (LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark)) [] [] [])) := by
  obtain ⟨rf,he⟩ := HashScopeProgram.Complete.program_runsIn 1 0 (by decide) b hb
    clauses codes hc rows hbound mark index hindex width modulus [false,false] hw hm
    HashScopeProgram.Complete.scopeOnly_shape
  rw [HashScopeProgram.Complete.outputBits_nested] at he
  rw [←hp] at he
  obtain ⟨n,hn,he⟩ := call_run _ r11 scopes (registers_injective ..) (block_injective ..) a _ _ he
  exact ⟨n,hn,rf,he⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeCall_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeCall_eval_oai
