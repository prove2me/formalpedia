-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:17:59.929493+00:00
-- url     : https://prove2.me/submissions/8bdd3168-e6ea-441a-b967-ff4b33f6d967

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158
import Definitions.Def_OAIQ081S159
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeInputBounds_query_bounds

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF

universe u

variable {α : Type u} [DecidableEq α]

theorem dedupLiterals_length_le (C : Clause α) : (dedupLiterals C).length ≤ C.length := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih.trans (Nat.le_succ _)
    · simpa [dedupLiterals, h] using Nat.succ_le_succ ih

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramSlots
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse local-slot specifications. A row lists at most D original clause
indices, including any zero coefficients; shortening only removes slots whose
actual shifted edge index lies outside the original m coordinates. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

theorem rowPayload_length (b m : ℕ) (ss : List (Fin m × SparseCode.F3)) :
    (rowPayload b m ss).length=ss.length*b := by
  induction ss with
  | nil => simp [rowPayload]
  | cons s ss ih =>
    change ((SubexpLiftRing.fixedBits b (s.1.val+m*s.2.val)) ++ rowPayload b m ss).length = _
    simp only [List.length_append,SubexpLiftRing.fixedBits_length,ih,List.length_cons]
    simp [Nat.add_mul,Nat.add_comm]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed raw-tuple assembler. The machine traverses raw digit bytes, not a
pre-expanded clause table. Each step looks up one ORIGINAL source clause and
emits its lifted coefficient plus unchanged canonical literal bytes. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem flat_length (t d : ℕ) (c : ZMod 3) :
    (RingProgram.flat (constantVector t d c)).length =
      (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t := by
  exact RingProgram.flat_length (constantVector t d c)

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramFlatten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed framed-record fold physically concatenates original literal-code
records after removing each term's coefficient frame. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open Extract (Data data)

theorem cost_le (records : List (List Bool)) :
    cost records ≤ 40*(Encoding.encodeList id records).length := by
  unfold cost
  induction records with
  | nil => simp [RecordPrograms.budget,Encoding.encodeList]
  | cons x xs ih =>
      simp only [RecordPrograms.budget,Encoding.encodeList,List.length_cons,List.length_append,
        Encoding.length_frame,id_eq] at ih ⊢
      omega

end SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeProducer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Construct a clause's local chunk scope from its encoded literals

This fixed program maps actual literal records to chunk records, restores the
record order, and invokes the checked stable deduplicator. Its output order is
the last-occurrence order used by the materializer and incidence-plan producer.
-/

namespace SubexponentialSAT.SubexpScopeProducer

open BitProgram StructuredCalls SubexpChunkRecordMap

theorem scope_length_le (ell : List Bool) (codes : List ℕ) :
    (scope ell codes).length ≤ codes.length := by
  exact (ExecCNF.dedupLiterals_length_le _).trans_eq (List.length_map ..)

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLayoutFactorBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical bounds for the actual clause-factor calls.  All envelopes are
polynomials in a common bound on the represented sizes and word lengths. -/

namespace SubexponentialSAT.SubexpLayoutConstructionBounds

theorem records_budget_le (cost : Word → ℕ) (words : List Word) (S C : ℕ)
    (hsize : ∀ w ∈ words, w.length ≤ S) (hcost : ∀ w ∈ words, cost w ≤ C) :
    RecordPrograms.budget cost words ≤ words.length * (6 * S + C + 7) := by
  induction words with
  | nil => simp [RecordPrograms.budget]
  | cons w words ih =>
      have hw := hsize w (by simp)
      have hc := hcost w (by simp)
      have ht := ih (fun x hx => hsize x (by simp [hx]))
        (fun x hx => hcost x (by simp [hx]))
      simp only [RecordPrograms.budget, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem literal_budget_le (width index S : ℕ) (hw : width ≤ S) (hi : index ≤ S) :
    SubexpLiteralChunkProgram.budget width index ≤ literalBound S := by
  unfold literalBound SubexpLiteralChunkProgram.budget
  gcongr

end SubexponentialSAT.SubexpLayoutConstructionBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bit-size envelopes for the actual per-row scope computation. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
open SubexponentialSAT.SubexpLayoutConstructionBounds

theorem natBits_append_length (xs ys : List ℕ) :
    (natBits (xs++ys)).length+1=(natBits xs).length+(natBits ys).length := by
  induction xs with
  | nil => simp [natBits,Encoding.encodeList,Nat.add_comm]
  | cons x xs ih =>
      simp only [List.cons_append,natBits,Encoding.length_encodeList_cons] at ih ⊢
      omega

theorem natBits_member_le (xs : List ℕ) (c : ℕ) (hc : c ∈ xs) :
    c+1 ≤ (natBits xs).length := by
  induction xs with
  | nil => simp at hc
  | cons x xs ih =>
      simp only [List.mem_cons] at hc
      simp only [natBits,Encoding.length_encodeList_cons,Encoding.length_encodeNat]
      rcases hc with rfl | hc
      · omega
      · have h := ih hc
        simp only [natBits] at h
        omega

theorem mergedCodes_cons (term : Term) (terms : List Term) :
    mergedCodes (term::terms)=mergedCodes terms++term.2 := by
  simp [mergedCodes,List.flatMap_append]

theorem merged_wire_le (terms : List Term) :
    (natBits (mergedCodes terms)).length ≤ (Encoding.encodeList payload terms).length := by
  induction terms with
  | nil => simp [mergedCodes,natBits,Encoding.encodeList]
  | cons term terms ih =>
      rw [mergedCodes_cons]
      have ha := natBits_append_length (mergedCodes terms) term.2
      simp only [natBits] at ih ha ⊢
      simp only [Encoding.length_encodeList_cons,payload,List.length_append,Encoding.length_frame]
      omega

theorem scope_budget_le (codes : List ℕ) (S : ℕ) (hS : 1 ≤ S)
    (hwire : (natBits codes).length ≤ S) :
    SubexpScopeProducer.budget [true] codes ≤ scopeProgramBound S := by
  have hcodes : codes.length ≤ S := (Nat.le_of_succ_le (Encoding.length_encodeList_lower _ codes)).trans hwire
  have hindex : ∀ code ∈ codes, code/2 ≤ S := by
    intro code hc
    have h := (natBits_member_le codes code hc).trans hwire
    exact (Nat.div_le_self _ _).trans (by omega)
  have hchunk : ∀ code ∈ codes, SubexpChunkRecordMap.chunk [true] code ≤ S := by
    intro code hc
    exact (Nat.div_le_self _ _).trans (hindex code hc)
  have hrecord : ∀ w ∈ codes.map Encoding.encodeNat, w.length ≤ 2*S := by
    intro w hw
    obtain ⟨code,hc,rfl⟩ := List.mem_map.mp hw
    have hh := (natBits_member_le codes code hc).trans hwire
    rw [Encoding.length_encodeNat]
    omega
  have hcallback : ∀ w ∈ codes.map Encoding.encodeNat,
      SubexpChunkRecordMap.callbackCost [true] w ≤ scopeCallbackBound S := by
    intro w hw
    obtain ⟨code,hc,rfl⟩ := List.mem_map.mp hw
    have hb := literal_budget_le 1 (code/2) S hS (hindex code hc)
    have hm := hchunk code hc
    simp only [SubexpChunkRecordMap.callbackCost,Encoding.length_encodeNat,Nat.add_sub_cancel,
      SubexpChunkRecordMap.mappedBits_encodeNat,List.length_cons,List.length_nil,Nat.zero_add]
    unfold scopeCallbackBound
    omega
  have hr := records_budget_le (SubexpChunkRecordMap.callbackCost [true])
    (codes.map Encoding.encodeNat) (2*S) (scopeCallbackBound S) hrecord hcallback
  simp only [List.length_map] at hr
  have hr' : RecordPrograms.budget (SubexpChunkRecordMap.callbackCost [true])
      (codes.map Encoding.encodeNat) ≤ S*(12*S+scopeCallbackBound S+7) := by
    rw [show 6*(2*S)=12*S by omega] at hr
    exact hr.trans (Nat.mul_le_mul_right _ hcodes)
  have hm := Encoding.length_encodeList_upper Encoding.encodeNat
    (codes.map (SubexpChunkRecordMap.chunk [true])) (S+1) (by
      intro j hj
      obtain ⟨code,hc,rfl⟩ := List.mem_map.mp hj
      simpa only [Encoding.length_encodeNat] using Nat.add_le_add_right (hchunk code hc) 1)
  simp only [List.length_map] at hm
  have hm' : (Encoding.encodeList Encoding.encodeNat
      (codes.map (SubexpChunkRecordMap.chunk [true]))).length ≤ mappedScopeBytesBound S :=
    hm.trans (by unfold mappedScopeBytesBound; gcongr)
  change 5+RecordPrograms.budget (SubexpChunkRecordMap.callbackCost [true])
    (codes.map Encoding.encodeNat)+10*_+120*(_+1)^2 ≤ _
  unfold scopeProgramBound
  gcongr

theorem single_cost_le (terms : List Term) :
    Single.cost terms ≤ 11+46*(Encoding.encodeList payload terms).length+
      scopeProgramBound (Encoding.encodeList payload terms).length := by
  have hm := merged_wire_le terms
  have hp := Encoding.length_encodeList_lower payload terms
  have hs := scope_budget_le (mergedCodes terms) (Encoding.encodeList payload terms).length (by omega) hm
  have hf := Flatten.cost_le (terms.map payload)
  have he : Encoding.encodeList id (terms.map payload)=Encoding.encodeList payload terms := by
    clear hm hp hs hf
    induction terms with
    | nil => rfl
    | cons t ts ih => simp [Encoding.encodeList,ih]
  rw [he] at hf
  unfold Single.cost
  simp only [natBits] at hm
  omega

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One ordinary polynomial in represented input bytes bounds the complete
scope-table producer, including outer parsing, framing, and final reversal. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
open SubexponentialSAT.SubexpLayoutConstructionBounds

theorem scopeProgramBound_mono {S T : ℕ} (h : S ≤ T) :
    scopeProgramBound S ≤ scopeProgramBound T := by
  unfold scopeProgramBound scopeCallbackBound literalBound mappedScopeBytesBound
    SubexpLiteralChunkProgram.budget
  gcongr

theorem scope_wire_le (terms : List Term) (S : ℕ)
    (h : (Encoding.encodeList payload terms).length ≤ S) :
    (Outer.scopeBytes terms).length ≤ mappedScopeBytesBound S := by
  have hm := (merged_wire_le terms).trans h
  have hl : (scope terms).length ≤ S := (SubexpScopeProducer.scope_length_le _ _).trans
    ((Nat.le_of_succ_le (Encoding.length_encodeList_lower Encoding.encodeNat (mergedCodes terms))).trans hm)
  have hv : ∀ v ∈ scope terms, v+1 ≤ S+1 := by
    intro v hv
    obtain ⟨term,ht,code,hc,rfl⟩ := (mem_scope terms v).mp hv
    have hc' : code∈mergedCodes terms := (mem_mergedCodes terms code).mpr ⟨term,ht,hc⟩
    have hb := (natBits_member_le (mergedCodes terms) code hc').trans hm
    have hd := Nat.div_le_self code 2
    omega
  have hw := Encoding.length_encodeList_upper Encoding.encodeNat (scope terms) (S+1)
    (by intro v hv'; simpa only [Encoding.length_encodeNat] using hv v hv')
  exact hw.trans (by unfold mappedScopeBytesBound; gcongr)

end SubexponentialSAT.SqrtLog.HashScopeProgram

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
namespace FromTuple

theorem interpreted_payload (t d : ℕ) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3)) :
    Encoding.encodeList payload (interpretedTerms (clauses := clauses) t d codes terms)=
      Encoding.encodeList id (terms.map (HashInputProgram.Loop.payload t d clauses)) := by
  induction terms with
  | nil => rfl
  | cons a as ih =>
      simpa [interpretedTerms,Encoding.encodeList,payload,HashInputProgram.Loop.payload,hc] using
        congrArg (fun rest => true :: (Encoding.frame (HashInputProgram.Loop.payload t d clauses a) ++ rest)) ih


end FromTuple
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramNativeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed polynomial envelope for raw references plus the optional original
marked clause. The size parameter bounds stored byte lengths and row/slot counts. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.SubexpLayoutConstructionBounds

theorem clause_wire_le (clauses : List (List Bool)) (i : Fin clauses.length) :
    clauses[i.val].length ≤ (Encoding.encodeList id clauses).length :=
  HashInputProgram.Loop.original_payload_length_le clauses _ (List.getElem_mem i.isLt)

theorem weighted_wire_le (t d : ℕ) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (row : List (Fin clauses.length × ZMod 3)) (S : ℕ)
    (hrow : row.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) :
    (Encoding.encodeList payload (FromTuple.interpretedTerms (clauses := clauses) t d codes row)).length ≤
      weightedBytesBound S := by
  rw [FromTuple.interpreted_payload t d clauses codes hc row]
  have h := Encoding.length_encodeList_upper id (row.map (HashInputProgram.Loop.payload t d clauses)) (3*S+1) (by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    have hclause := (clause_wire_le clauses a.1).trans hmaster
    simp only [id_eq,HashInputProgram.Loop.payload,List.length_append,Encoding.length_frame,
      HashInputProgram.Loop.flat_length]
    omega)
  simp only [List.length_map] at h
  exact h.trans (calc
    _ ≤ 1+(2*(3*S+1)+2)*S := by gcongr
    _ = weightedBytesBound S := by unfold weightedBytesBound; ring)

theorem assembly_cost_le (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (count S : ℕ) (hn : count ≤ S) (hb : b ≤ S) (hm : modulus.length ≤ S)
    (hc : clauses.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) :
    HashInputProgram.Loop.uniformBudget t d b modulus clauses count ≤ assemblyBound S := by
  unfold HashInputProgram.Loop.uniformBudget assemblyBound
  gcongr
  unfold HashInputProgram.Loop.termBudget HashInputProgram.LoopDecode.budget
  gcongr

theorem marked_wire_le (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (i : Fin clauses.length) (S : ℕ) (hS : 1 ≤ S)
    (hmaster : (Encoding.encodeList id clauses).length ≤ S) :
    (Marked.scopeBits (codes i)).length ≤ mappedScopeBytesBound (weightedBytesBound S) := by
  have hw : (Encoding.encodeList Encoding.encodeNat (codes i)).length ≤ S := by
    rw [← hc i]
    exact (clause_wire_le clauses i).trans hmaster
  have hp : (Encoding.encodeList payload [([],codes i)]).length ≤ weightedBytesBound S := by
    simp only [payload,List.length_append,Encoding.length_frame,
      List.length_nil,Encoding.encodeList,List.length_cons]
    have hss : S ≤ S*S := by simpa using Nat.mul_le_mul_left S hS
    unfold weightedBytesBound
    nlinarith
  have hh := scope_wire_le [([],codes i)] (weightedBytesBound S) hp
  simpa [Outer.scopeBytes,scope,mergedCodes,Marked.scopeBits] using hh

theorem row_cost_le (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (row : List (Fin clauses.length × ZMod 3)) (S : ℕ)
    (hrow : row.length ≤ S) (hb : b ≤ S) (hm : modulus.length ≤ S)
    (hclauses : clauses.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) :
    6*(RawTable.rowBits b row).length+RawTable.callbackCost t d b modulus clauses codes row+7 ≤ rowCostBound S := by
  have hw := weighted_wire_le t d clauses codes hc row S hrow hmaster hweight
  have hs := single_cost_le (FromTuple.interpretedTerms (clauses := clauses) t d codes row)
  have hsp := scopeProgramBound_mono hw
  have hsw := scope_wire_le (FromTuple.interpretedTerms (clauses := clauses) t d codes row) (weightedBytesBound S) hw
  have ha := assembly_cost_le t d b modulus clauses row.length S hrow hb hm hclauses hmaster hweight
  have hr : (RawTable.rowBits b row).length ≤ S*S := by
    change (CodeRowsProgram.rowPayload b clauses.length row).length ≤ S*S
    rw [CodeRowsProgram.rowPayload_length]
    exact Nat.mul_le_mul hrow hb
  unfold rowCostBound RawTable.callbackCost FromTuple.cost RawTable.scopeBytes Outer.scopeBytes at *
  simp only [Nat.mul_assoc] at *
  omega

theorem loop_cost_le (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : RawTable.Rows clauses.length) (S : ℕ)
    (hrows : ∀ row∈rows, row.length ≤ S) (hb : b ≤ S) (hm : modulus.length ≤ S)
    (hclauses : clauses.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) :
    RawTable.loopCost t d b modulus clauses codes rows ≤ rows.length*rowCostBound S := by
  induction rows with
  | nil => simp [RawTable.loopCost]
  | cons row rows ih =>
      have hh := row_cost_le t d b modulus clauses codes hc row S (hrows row (by simp)) hb hm hclauses hmaster hweight
      have ht := ih (fun r hr => hrows r (by simp [hr]))
      simp only [RawTable.loopCost,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem optional_cost_le (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (mark : Option (Fin clauses.length)) (index : List Bool) (S : ℕ) (hS : 1 ≤ S)
    (hindex : index.length ≤ S) (hmaster : (Encoding.encodeList id clauses).length ≤ S) :
    Marked.optionalCost clauses codes mark index ≤ optionalCostBound S := by
  cases mark with
  | none => simp [Marked.optionalCost,optionalCostBound]; omega
  | some i =>
      have hwire : (natBits (codes i)).length ≤ S := by
        change (Encoding.encodeList Encoding.encodeNat (codes i)).length ≤ S
        rw [← hc i]
        exact (clause_wire_le clauses i).trans hmaster
      have hb := scope_budget_le (codes i) S hS hwire
      have hw := marked_wire_le clauses codes hc i S hS hmaster
      change 2*index.length+10+Marked.processCost clauses codes i ≤ optionalCostBound S
      unfold Marked.processCost optionalCostBound
      omega

theorem cost_le_polynomial (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) (index : List Bool)
    (S : ℕ) (hS : 1 ≤ S) (hn : rows.length ≤ S) (hrows : ∀ row∈rows, row.length ≤ S)
    (hb : b ≤ S) (hm : modulus.length ≤ S) (hclauses : clauses.length ≤ S)
    (hmaster : (Encoding.encodeList id clauses).length ≤ S)
    (hweight : (d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t ≤ S) (hindex : index.length ≤ S) :
    cost t d b modulus clauses codes rows mark index ≤ polynomialBound S := by
  have hl := (loop_cost_le t d b modulus clauses codes hc rows S hrows hb hm hclauses hmaster hweight).trans
    (Nat.mul_le_mul_right (rowCostBound S) hn)
  have ho := optional_cost_le clauses codes hc mark index S hS hindex hmaster
  have hwords : ∀ w∈scopeWords (clauses := clauses) t d codes rows mark,
      w.length ≤ mappedScopeBytesBound (weightedBytesBound S) := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hw
      exact scope_wire_le (FromTuple.interpretedTerms (clauses := clauses) t d codes row) _
        (weighted_wire_le t d clauses codes hc row S (hrows row hr) hmaster hweight)
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
      exact marked_wire_le clauses codes hc i S hS hmaster
  have hlen : (scopeWords (clauses := clauses) t d codes rows mark).length ≤ S+1 := by
    cases mark <;> simp [scopeWords] <;> omega
  have hout := Encoding.length_encodeList_upper id (scopeWords (clauses := clauses) t d codes rows mark)
    (mappedScopeBytesBound (weightedBytesBound S)) hwords
  have hout' : (outputBits (clauses := clauses) t d codes rows mark).length ≤
      1+(2*mappedScopeBytesBound (weightedBytesBound S)+2)*(S+1) :=
    hout.trans (by gcongr)
  unfold cost polynomialBound
  omega

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeInputBoundsQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform physical-input capacity for the produced per-query frontend data. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafQueryFrontend

/-- The existing fixed scope-producer polynomial receives the same input-only
capacity as the downstream scan and parameter bounds. -/
theorem scope_cost_le_oai (q : Query) (k : ℕ) (hv : q.Valid) :
    HashScopeProgram.Complete.cost 1 0 q.width.length q.modulus q.clauses q.codes q.rows q.mark q.index ≤
      HashScopeProgram.Complete.polynomialBound (capacity q k) := by
  have h := query_bounds q k hv
  have hlog : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have hweight : (0+1)*SubexpLiftRing.baseWidth 3 1 ≤ capacity q k := by
    have hh : (0+1)*SubexpLiftRing.baseWidth 3 1 ≤ 8 := by norm_num [SubexpLiftRing.baseWidth, hlog]
    exact hh.trans h.eight
  exact HashScopeProgram.Complete.cost_le_polynomial 1 0 q.width.length q.modulus q.clauses q.codes
    hv.2.2.1 q.rows q.mark q.index (capacity q k) (by have := h.eight; omega)
    h.rawRowCount h.rawRowSlots h.width h.modulus h.clauseCount h.master hweight h.index

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le_oai
