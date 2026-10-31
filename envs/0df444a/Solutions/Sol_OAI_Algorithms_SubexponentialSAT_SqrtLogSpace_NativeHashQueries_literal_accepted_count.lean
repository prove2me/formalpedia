-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_accepted_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:17:53.704167+00:00
-- url     : https://prove2.me/submissions/9a023bf8-2592-4789-bc24-3d93763465a0

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamily
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

theorem row_dot {m d : ℕ} (h : Candidate m d) (v : Fin m → ZMod 3) :
    (∑ i, row h i * v i) = eval h v := by
  simp only [row, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [ite_mul ]

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete streamed selector uses the original ternary row semantics.
Its exact scores and normalized reference coverage discharge the greedy
contraction hypotheses. These statements concern the deterministic history
refined by the native run; native query and resource closure remain separate. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF

open SqrtLog
open scoped BigOperators

noncomputable section

theorem accepts_decode {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) (x : SAT.Assignment (Fin n)) :
    HashSelect.accepts (rowAccept clauses) rows x =
      HashSelect.accepts (HashSelect.cnfRowAccept clauses) (rows.map (decode m)) x := by
  simp [HashSelect.accepts, rowAccept, List.all_map, Function.comp_def]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramOrigin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

theorem rowValue_eq_sum {V C R : Type*} [CommRing R]
    (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (ringAlgebra R) decode value terms =
      (terms.map fun term => decode term.1 * clauseValue (ringAlgebra R) value term.2).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rcases term with ⟨c,ls⟩
      change decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value terms = _
      simp only [List.map_cons,List.sum_cons]
      rw [ih]

theorem rawRow_value {V R : Type*} [CommRing R] {m depth : ℕ}
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth)
    (decode : ZMod 3 → R) (value : V → R) :
    rowValue (ringAlgebra R) decode value (rawRow source h) =
      ∑ j, decode (h.2 j) * clauseValue (ringAlgebra R) value (source (h.1 j)) := by
  simp [rowValue_eq_sum,rawRow,List.sum_ofFn]

theorem clauseValue_original {V R : Type*} [DecidableEq V] [CommRing R]
    (ls : List (SAT.Literal V)) (x : SAT.Assignment V) :
    clauseValue (ringAlgebra R) (fun v => HashInput.boolValue (R := R) (x v)) ls =
      HashInput.clauseValue ls.toFinset x := by
  induction ls with
  | nil => simp [clauseValue,ringAlgebra,HashInput.clauseValue]
  | cons l ls ih =>
      have hl : literalValue (ringAlgebra R)
          (fun v => HashInput.boolValue (R := R) (x v)) l =
          if l.eval x then (0:R) else 1 := by
        rcases l with ⟨v,p⟩
        cases p <;> cases hx : x v <;>
          simp [literalValue,ringAlgebra,HashInput.boolValue,SAT.Literal.eval,hx]
      change literalValue (ringAlgebra R) _ l * clauseValue (ringAlgebra R) _ ls = _
      rw [hl,ih]
      cases h1 : l.eval x <;> cases h2 : SAT.Clause.eval x ls.toFinset <;>
        simp [HashInput.clauseValue,SAT.Clause.eval_insert,h1,h2]

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramInitial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual serializer's payloads satisfy the initial-code hypothesis of
the actual generated-order selector. Repeated and zero raw slots are retained;
their finite-field coefficients are combined only in the semantic decoder. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open scoped BigOperators
open LeafScopeResourceBounds

theorem listCandidate_row {m : ℕ} (slots : List (Fin m × ZMod 3)) :
    HashFamily.row (listCandidate slots) = CodeRowsProgram.coefficient slots := by
  funext i
  have h := congrArg (fun xs : List (Fin m × ZMod 3) =>
    (xs.map (fun z => if z.1=i then z.2 else 0)).sum) (List.ofFn_get slots)
  change (∑ x, if (slots.get x).1 = i then (slots.get x).2 else 0) =
    (slots.map (fun z => if z.1 = i then z.2 else 0)).sum
  rw [← List.sum_ofFn]
  change (List.ofFn ((fun z => if z.1 = i then z.2 else 0) ∘ slots.get)).sum = _
  rw [← List.map_ofFn]
  exact h

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_OuterQueryCountCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw tuple rows and decoded selector rows have identical acceptance,
including repeated clause IDs and zero coefficients. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.OuterQuery.Count
open LeafProgram
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {n m : ℕ}

theorem rawRow_eq (source : Fin m → List (SAT.Literal (Fin n)))
    (row : List (Fin m × ZMod 3)) :
    row.map (fun term => (term.2,source term.1)) =
      HashInputProgram.rawRow source (LeafScopeResourceBounds.listCandidate row) := by
  have h := congrArg (List.map (fun term : Fin m × ZMod 3 => (term.2,source term.1)))
    (List.ofFn_get row)
  simpa only [HashInputProgram.rawRow, LeafScopeResourceBounds.listCandidate,
    List.map_ofFn, Function.comp_def] using h.symm

theorem rawRow_value (source : Fin m → List (SAT.Literal (Fin n)))
    (row : List (Fin m × ZMod 3)) (x : Fin n → Bool) :
    rowValue (ringAlgebra (ZMod 3)) id (fun v => HashInput.boolValue (x v))
      (row.map (fun term => (term.2,source term.1))) =
    ∑ i,HashFamily.row (LeafScopeResourceBounds.listCandidate row) i *
      HashInput.violationVector (fun i => (source i).toFinset) x i := by
  rw [rawRow_eq,HashInputProgram.rawRow_value,HashFamily.row_dot]
  unfold HashFamily.eval
  apply Finset.sum_congr rfl
  intro i _
  rw [HashInputProgram.clauseValue_original]
  rfl

theorem raw_accepts (source : Fin m → List (SAT.Literal (Fin n)))
    (rows : List (List (Fin m × ZMod 3))) (x : Fin n → Bool) :
    (∀ row ∈ rawHashes source rows,
      rowValue (ringAlgebra (ZMod 3)) id (fun v => HashInput.boolValue (x v)) row=0) ↔
    HashSelect.accepts (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
      (rows.map (fun row => HashFamily.row (LeafScopeResourceBounds.listCandidate row))) x=true := by
  simp only [rawHashes,HashSelect.accepts,List.all_map,List.all_eq_true,List.mem_map,
    forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,Function.comp_apply,
    HashSelect.cnfRowAccept,decide_eq_true_eq,rawRow_value]

theorem violates_eq (clause : List (SAT.Literal (Fin n))) (x : Fin n → Bool) :
    NodeSemantics.violates clause x= !(SAT.Clause.eval x clause.toFinset) := by
  induction clause with
  | nil => simp [NodeSemantics.violates,SAT.Clause.eval]
  | cons l ls ih => simp [NodeSemantics.violates,List.all_cons,SAT.Clause.eval_insert,
      ← ih,NodeSemantics.violates]

theorem fullCount_raw_none (source : Fin m → List (SAT.Literal (Fin n)))
    (rows : List (List (Fin m × ZMod 3))) (clause : List (SAT.Literal (Fin n))) :
    PreparedBranchCount.fullCount (rawHashes source rows) false clause =
      HashSelect.acceptedCount (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
        (rows.map (fun row => HashFamily.row (LeafScopeResourceBounds.listCandidate row))) := by
  unfold PreparedBranchCount.fullCount HashSelect.acceptedCount NodeSemantics.ternaryAccepted
  apply Finset.sum_congr rfl
  intro x _
  simp only [Bool.false_eq_true,IsEmpty.forall_iff,and_true,raw_accepts]

theorem fullCount_raw_marked (source : Fin m → List (SAT.Literal (Fin n)))
    (rows : List (List (Fin m × ZMod 3))) (i : Fin m) :
    PreparedBranchCount.fullCount (rawHashes source rows) true (source i) =
      markedCount (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
        (rows.map (fun row => HashFamily.row (LeafScopeResourceBounds.listCandidate row)))
        (fun i x => !(SAT.Clause.eval x (source i).toFinset)) i := by
  unfold PreparedBranchCount.fullCount markedCount NodeSemantics.ternaryAccepted
  apply Finset.sum_congr rfl
  intro x _
  simp only [true_implies,raw_accepts,violates_eq,Bool.and_eq_true]

theorem decode_raw (width : ℕ) (hm : 0 < m) (payload : List Bool) :
    HashFamily.row (LeafScopeResourceBounds.listCandidate
      (LeafScopeResourceBounds.rawDecode m width hm payload)) =
      HashFamilyPayload.decodeVariableRow m width payload := by
  rw [LeafOuterProgram.listCandidate_row]
  unfold HashFamilyPayload.decodeVariableRow HashFamilyPayload.decodeRow
  rw [dite_eq_left hm]
  funext i
  simp only [LeafScopeResourceBounds.rawDecode,HashInputProgram.candidateTerms,
    CodeRowsProgram.coefficient,List.map_ofFn,List.sum_ofFn,HashFamily.row,Function.comp_def]

theorem fullCount_payload_none (source : Fin m → List (SAT.Literal (Fin n)))
    (width : ℕ) (hm : 0 < m) (payloads : List (List Bool))
    (clause : List (SAT.Literal (Fin n))) :
    PreparedBranchCount.fullCount
      (rawHashes source (payloads.map (LeafScopeResourceBounds.rawDecode m width hm))) false clause =
      HashSelect.acceptedCount (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
        (payloads.map (HashFamilyPayload.decodeVariableRow m width)) := by
  rw [fullCount_raw_none]
  simp only [List.map_map,Function.comp_def,decode_raw]

theorem fullCount_payload_marked (source : Fin m → List (SAT.Literal (Fin n)))
    (width : ℕ) (hm : 0 < m) (payloads : List (List Bool)) (i : Fin m) :
    PreparedBranchCount.fullCount
      (rawHashes source (payloads.map (LeafScopeResourceBounds.rawDecode m width hm))) true (source i) =
      markedCount (HashSelect.cnfRowAccept (fun i => (source i).toFinset))
        (payloads.map (HashFamilyPayload.decodeVariableRow m width))
        (fun i x => !(SAT.Clause.eval x (source i).toFinset)) i := by
  rw [fullCount_raw_marked]
  simp only [List.map_map,Function.comp_def,decode_raw]

end SubexponentialSAT.SqrtLog.OuterQuery.Count

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual query's ternary count is the selector's exact natural score.
Literal source occurrences and the entire ambient assignment type are retained. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryCount

open SqrtLog DisjointReuse HighFrontendSources HashGreedyCode HashQueryEntry
open LeafProgram OuterQuery.Count

/-- Decoding changes only the row representation, not the marked natural count. -/
theorem payload_marked_count {n : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (payloads : List (List Bool)) (e : Fin F.length) :
    PreparedBranchCount.fullCount (rawHashes F.get (payloads.map (raw F.length hm)))
      true (F.get e) =
      markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads
        (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e := by
  rw [fullCount_payload_marked]
  unfold markedCount
  apply Finset.sum_congr rfl
  intro x _
  rw [HashGreedyCNF.accepts_decode]
  rfl

/-- The unmarked count keeps all ambient assignments, including unused bits. -/
theorem payload_accepted_count {n : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (payloads : List (List Bool)) (clause : List (SAT.Literal (Fin n))) :
    PreparedBranchCount.fullCount (rawHashes F.get (payloads.map (raw F.length hm)))
      false clause =
      HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads := by
  rw [fullCount_payload_none]
  unfold HashSelect.acceptedCount
  apply Finset.sum_congr rfl
  intro x _
  rw [HashGreedyCNF.accepts_decode]
  rfl


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryCount
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeHashQueries
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Literal marked and accepted query continuations for the actual prepared
leaf. Shadow execution preserves unrestricted caller words for time; the
same replay counts those words separately in maximum prefix storage. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries

open BitProgram StructuredCalls SqrtLog DisjointReuse
open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram
open HashGreedyProgram.NativeRound

/-- The exact raw expression returned by the actual high iterator is the
same full ambient count as the literal query. Index casts retain every slot. -/
theorem raw_query_fullCount {n N : ℕ} (F : RawCNF n) (h : n = N)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool)
    (hsource : (rawQueryFromRows F rows mark index width modulus ambient).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F)) :
    PreparedBranchCount.fullCount
      ((PreparedSource.castRows (congrArg List.length hsource)
        (rawQueryFromRows F rows mark index width modulus ambient).rows).map
          (fun terms => terms.map (fun term =>
            (term.2, HashInputProgram.Expansion.originalClause
              (Eq.mp (congrArg RawCNF h) F) term.1))))
      (rawQueryFromRows F rows mark index width modulus ambient).mark.isSome
      ((Eq.mp (congrArg RawCNF h) F)[PreparedSource.markIndex
        (rawQueryFromRows F rows mark index width modulus ambient)]?.getD []) =
      PreparedBranchCount.fullCount (OuterQuery.Count.rawHashes F.get rows) mark.isSome
        (F[(mark.map Fin.val).getD 0]?.getD []) := by
  cases h
  simp [PreparedSource.castRows, rawQueryFromRows, rawQuery, recordRows,
    HighFrontendSources.castRows, recordMark, OuterQuery.Count.rawHashes,
    List.map_map, Function.comp_def, HashInputProgram.Expansion.originalClause,
    List.get_eq_getElem, PreparedSource.markIndex]
  congr 1

/-- Marked and unmarked payloads have exactly the selector accessor count,
using the very same full-count expression produced by the high iterator. -/
theorem raw_query_payload_count {n N : ℕ} (F : RawCNF n) (h : n = N)
    (hm : 0 < F.length) (payloads : List (List Bool)) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool)
    (hsource : (rawQueryFromRows F (payloads.map (raw F.length hm)) mark
      index width modulus ambient).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F)) :
    PreparedBranchCount.fullCount
      ((PreparedSource.castRows (congrArg List.length hsource)
        (rawQueryFromRows F (payloads.map (raw F.length hm)) mark
          index width modulus ambient).rows).map
          (fun terms => terms.map (fun term =>
            (term.2, HashInputProgram.Expansion.originalClause
              (Eq.mp (congrArg RawCNF h) F) term.1))))
      (rawQueryFromRows F (payloads.map (raw F.length hm)) mark
        index width modulus ambient).mark.isSome
      ((Eq.mp (congrArg RawCNF h) F)[PreparedSource.markIndex
        (rawQueryFromRows F (payloads.map (raw F.length hm)) mark
          index width modulus ambient)]?.getD []) =
      match mark with
      | none => HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads
      | some e => markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F)) payloads
          (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e := by
  rw [raw_query_fullCount F h _ mark index width modulus ambient hsource]
  cases mark with
  | none => exact HashQueryCount.payload_accepted_count F hm payloads _
  | some e =>
      simpa [List.get_eq_getElem] using HashQueryCount.payload_marked_count F hm payloads e


open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources

/-- Final history-only queries have precisely the selector's accepted
count; no trial row or marked-clause filter remains. -/
theorem literal_accepted_count_oai {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (d : State 40 896)
    (h : n = BinaryArithmetic.toNat (acceptedQuery F hm shifts Q rounds d).ambient)
    (hsource : (acceptedQuery F hm shifts Q rounds d).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F)) :
    literalCount (acceptedQuery F hm shifts Q rounds d)
      (Eq.mp (congrArg RawCNF h) F) hsource =
      HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) := by
  exact raw_query_payload_count F h hm _ none [false]
    (d.stacks 783) (d.stacks 782) (d.stacks 785) hsource


open NativeQueryInputBounds Statement

attribute [local irreducible] Execute.guardedModel

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_accepted_count_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_accepted_count_oai
