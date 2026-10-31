-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:17:33.95623+00:00
-- url     : https://prove2.me/submissions/957eec73-c70f-43d3-8fc5-26b49743ee88

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158
import Definitions.Def_OAIQ081S159
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafScopeInputBounds_statistics_bound

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

theorem dedupLiterals_nodup (C : Clause α) : (dedupLiterals C).Nodup := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih
    · simp only [dedupLiterals, ite_eq_right h, List.nodup_cons]
      exact ⟨fun hm => h ((contains_true x xs).mpr ((mem_dedupLiterals x xs).mp hm)), ih⟩

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSunflowerSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite sunflower search, with counted list scans. -/
namespace SubexponentialSAT.ExecSunflowerSearch

open ExecCNF
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

@[simp] theorem dedupLiterals_length (C : Clause α) :
    (dedupLiterals C).length = (clauseSet C).card := by
  have h := List.toFinset_card_of_nodup (dedupLiterals_nodup C)
  change (clauseSet (dedupLiterals C)).card = _ at h
  rw [clauseSet_dedupLiterals] at h
  exact h.symm

end SubexponentialSAT.ExecSunflowerSearch

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

theorem scope_nodup (ell : List Bool) (codes : List ℕ) : (scope ell codes).Nodup :=
  ExecCNF.dedupLiterals_nodup _

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw hash scopes include every referenced literal, irrespective of its
coefficient. The physical materializer preserves these exact original codes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

theorem scope_nodup (terms : List Term) : (scope terms).Nodup :=
  SubexpScopeProducer.scope_nodup _ _

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
namespace Complete

theorem scopes_length (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    (scopes (clauses := clauses) t d codes rows mark).length=rows.length+mark.isSome.toNat := by
  cases mark <;> simp [scopes]

end Complete
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Resource bounds for the exact physical scope stream, including zero
coefficients, repeated raw slots, empty hash rows, and the optional mark. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashScopeProgram

theorem slots_le {α : Type*} (rows : List (List α)) (D : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ D) : slots rows ≤ rows.length * D := by
  induction rows with
  | nil => simp [slots]
  | cons row rows ih =>
    have hr := h row (by simp)
    have hs := ih (fun r hr => h r (by simp [hr]))
    simp only [slots, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

theorem scopes_nodup (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : RawTable.Rows clauses.length)
    (mark : Option (Fin clauses.length)) :
    ∀ row ∈ Complete.scopes t d codes rows mark, row.Nodup := by
  intro row hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr
    exact scope_nodup _
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact SubexpScopeProducer.scope_nodup _ _

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-size bounds for explicit scopes. These bounds use actual duplicate-free
original-coordinate scope rows, with no value-only replacement for their bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafStatisticsProgram LeafStatisticsSemantics

/-- A field occupies no more bytes than its containing framed list. -/
theorem encoded_member_length {α : Type*} (encode : α → List Bool)
    (rows : List α) (a : α) (ha : a ∈ rows) :
    (encode a).length ≤ (Encoding.encodeList encode rows).length := by
  induction rows with
  | nil => simp at ha
  | cons b bs ih =>
    rw [Encoding.length_encodeList_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have h := ih ha
      omega

theorem finite_scope_length (row : List ℕ) (n : ℕ) (hd : row.Nodup)
    (hi : ∀ v ∈ row, v < n) : row.length ≤ n := by
  classical
  rw [← List.toFinset_card_of_nodup hd]
  calc
    row.toFinset.card ≤ (Finset.range n).card := Finset.card_le_card (by
      intro v hv
      exact Finset.mem_range.mpr (hi v (List.mem_toFinset.mp hv)))
    _ = n := Finset.card_range n

/-- Unary original IDs are explicitly charged in each serialized scope row. -/
theorem scope_row_wire (row : List ℕ) (n S : ℕ) (hS : 1 ≤ S) (hn : n ≤ S)
    (hd : row.Nodup) (hi : ∀ v ∈ row, v < n) :
    (Encoding.encodeList Encoding.encodeNat row).length ≤ 5*S^2 := by
  have hl := (finite_scope_length row n hd hi).trans hn
  have hw := Encoding.length_encodeList_upper Encoding.encodeNat row S (by
    intro v hv
    rw [Encoding.length_encodeNat]
    exact (Nat.succ_le_of_lt (hi v hv)).trans hn)
  calc
    _ ≤ 1+(2*S+2)*S := hw.trans (by gcongr)
    _ ≤ 5*S^2 := by nlinarith

theorem scope_wire (scopes : List (List ℕ)) (n S : ℕ) (hS : 1 ≤ S)
    (hn : n ≤ S) (hc : scopes.length ≤ S)
    (hd : ∀ row ∈ scopes, row.Nodup) (hi : ∀ row ∈ scopes, ∀ v ∈ row, v < n) :
    (scopeBits scopes).length ≤ 16*S^3 := by
  have hw := Encoding.length_encodeList_upper (Encoding.encodeList Encoding.encodeNat) scopes
    (5*S^2) (fun row hr => scope_row_wire row n S hS hn (hd row hr) (hi row hr))
  have hp : 1 ≤ S^2 := Nat.one_le_pow _ _ hS
  have hcube : S ≤ S^3 := by
    simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left S hp
  calc
    _ ≤ 1+(2*(5*S^2)+2)*S := hw.trans (by gcongr)
    _ ≤ 16*S^3 := by nlinarith only [hcube,hS]

theorem scope_mass (scopes : List (List ℕ)) (n S : ℕ)
    (hn : n ≤ S) (hc : scopes.length ≤ S)
    (hd : ∀ row ∈ scopes, row.Nodup) (hi : ∀ row ∈ scopes, ∀ v ∈ row, v < n) :
    LeafScopeResourceBounds.slots scopes ≤ S^2 := by
  have h := LeafScopeResourceBounds.slots_le scopes n
    (fun row hr => finite_scope_length row n (hd row hr) (hi row hr))
  exact h.trans (by simpa [pow_two] using Nat.mul_le_mul hc hn)

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

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

theorem scope_count_le_rows (q : Query) :
    q.scopeRows.length ≤ (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length := by
  have h := Encoding.length_encodeList_lower id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))
  have hm : q.mark.isSome.toNat ≤ 1 := by cases q.mark <;> simp
  change (HashScopeProgram.Complete.scopes 1 0 q.codes q.rows q.mark).length ≤ _
  rw [HashScopeProgram.Complete.scopes_length]
  simpa only [HashScopeProgram.RawTable.inputBits, List.length_map] using
    (show q.rows.length+q.mark.isSome.toNat ≤
      (Encoding.encodeList id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))).length by
      simp only [List.length_map] at h
      omega)

theorem raw_row_slots_le_rows (q : Query) (hwidth : 0 < q.width.length)
    (row : List (Fin q.clauses.length × ZMod 3)) (hr : row ∈ q.rows) :
    row.length ≤ (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length := by
  have hh := encoded_member_length id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))
    (HashScopeProgram.RawTable.rowBits q.width.length row) (List.mem_map.mpr ⟨row,hr,rfl⟩)
  have hl : row.length ≤ row.length*q.width.length := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left row.length (Nat.succ_le_of_lt hwidth)
  have he : (HashScopeProgram.RawTable.rowBits q.width.length row).length = row.length*q.width.length :=
    CodeRowsProgram.rowPayload_length q.width.length q.clauses.length row
  exact (hl.trans_eq he.symm).trans hh

theorem query_bounds_oai (q : Query) (k : ℕ) (hv : q.Valid) : QueryBounds q k := by
  rcases hv with ⟨hw,hn,hcodes,hlarge,hindex,hmod,hids⟩
  have h8 : 8 ≤ capacity q k := by unfold capacity; omega
  have hS : 1 ≤ capacity q k := by omega
  have hamb : BinaryArithmetic.toNat q.ambient ≤ capacity q k := by unfold capacity; omega
  have hmaster : (Encoding.encodeList id q.clauses).length ≤ capacity q k := by unfold capacity; omega
  have hrows : (HashScopeProgram.RawTable.inputBits q.width.length q.rows).length ≤ capacity q k := by unfold capacity; omega
  have hclause : q.clauses.length ≤ capacity q k :=
    (Nat.le_of_succ_le (Encoding.length_encodeList_lower id q.clauses)).trans hmaster
  have hraw : q.rows.length ≤ capacity q k := by
    have h := Encoding.length_encodeList_lower id (q.rows.map (HashScopeProgram.RawTable.rowBits q.width.length))
    simp only [List.length_map] at h
    exact (Nat.le_of_succ_le h).trans hrows
  have hscope : q.scopeRows.length ≤ capacity q k := (scope_count_le_rows q).trans hrows
  have hd : ∀ row ∈ q.scopeRows, row.Nodup := LeafScopeResourceBounds.scopes_nodup 1 0 q.codes q.rows q.mark
  have hforward : q.forward.length = BinaryArithmetic.toNat q.ambient := by simp [Query.forward, highMask]
  have hs := statistics_bound q.scopeRows q.forward (BinaryArithmetic.toNat q.ambient) (capacity q k)
    hS hamb (hforward.le.trans hamb) hscope hd hids
  refine ⟨h8,hamb,hmaster,hrows,?_,?_,?_,?_,?_,hclause,hraw,?_,hscope,?_,?_,?_,
    hforward.le.trans hamb,hs.free,hs.occurrence,hs.incidences,hs.uncovered,hs.arity,hs.factors⟩
  · unfold capacity; omega
  · unfold capacity; omega
  · unfold capacity; omega
  · unfold capacity; omega
  · unfold capacity; omega
  · intro row hr
    exact (raw_row_slots_le_rows q hw row hr).trans hrows
  · intro row hr
    exact (finite_scope_length row _ (hd row hr) (hids row hr)).trans hamb
  · exact scope_mass q.scopeRows _ _ hamb hscope hd hids
  · exact scope_wire q.scopeRows _ _ hS hamb hscope hd hids

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds_oai
