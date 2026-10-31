-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.headBounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:47:36.707243+00:00
-- url     : https://prove2.me/submissions/f04022d8-e1ad-43d7-9f03-6d2280953fc9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets_headBounds

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

theorem nativeSpecOfInputs_rows : Encoding.encodeList id (spec).rawRows=
    HashScopeProgram.RawTable.inputBits q.width.length q.rows :=
  factorSpec_row_bytes _ _ _ _ _ _ _ _ _ _ _ _ _

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

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

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryWordBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The authentic factor specification inherits its row and clause bounds
from the actual physical formula, row-stream and width words. These are
length bounds, so they remain valid with leading zeros and repeated entries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryWordBounds

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing
open LeafProgram LeafProgram.PreparedSource LeafParametersProgram

/-- Each stored selector term occupies exactly the fixed positive bit width. -/
theorem rowBits_length {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) :
    (HashScopeProgram.RawTable.rowBits b terms).length = b * terms.length := by
  induction terms with
  | nil => simp [HashScopeProgram.RawTable.rowBits]
  | cons a terms ih =>
    simp only [HashScopeProgram.RawTable.rowBits, List.map_cons, List.flatten_cons,
      List.length_append, HashInputProgram.Loop.word, fixedBits_length,
      List.length_cons] at *
    rw [Nat.mul_add, Nat.mul_one, ih, Nat.add_comm]

/-- An actual row, including repetitions and zero coefficients, is paid for
by its physical framed input stream. -/
theorem row_length_le_stream {m : ℕ} (b : ℕ) (hb : 0 < b)
    (rows : HashScopeProgram.RawTable.Rows m) (f : ℕ) (hf : f < rows.length) :
    rows[f].length ≤ (HashScopeProgram.RawTable.inputBits b rows).length := by
  have h := LeafScopeInputBounds.encoded_member_length id
    (rows.map (HashScopeProgram.RawTable.rowBits b))
    (HashScopeProgram.RawTable.rowBits b rows[f])
    (List.mem_map.mpr ⟨rows[f], List.getElem_mem hf, rfl⟩)
  have hmul : rows[f].length ≤ b * rows[f].length := by
    have hb' : 1 ≤ b := by omega
    simpa only [one_mul] using Nat.mul_le_mul_right rows[f].length hb'
  simp only [id_eq, rowBits_length] at h
  exact hmul.trans h

/-- Every original clause is bounded by its actual two-level formula bytes. -/
theorem source_clause_length {n : ℕ} (source : List (List (SAT.Literal (Fin n))))
    (ls : List (SAT.Literal (Fin n))) (hls : ls ∈ source) :
    ls.length ≤ (Encoding.encodeList id
      (HashInputProgram.Expansion.encodedClauses source)).length := by
  have h := Encoding.length_encodeList_lower
    (fun l => Encoding.encodeNat (Encoding.literalCode l)) ls
  have hm := LeafScopeInputBounds.encoded_member_length id
    (HashInputProgram.Expansion.encodedClauses source)
    (HashInputProgram.clausePayload ls) (List.mem_map.mpr ⟨ls,hls,rfl⟩)
  change ls.length+1 ≤ (HashInputProgram.clausePayload ls).length at h
  exact (by omega : ls.length ≤ (HashInputProgram.clausePayload ls).length).trans hm

/-- The optional marked clause has the same bound even for an absent mark. -/
theorem marked_clause_length {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hsource : ∀ ls ∈ q.source, ls.length ≤ A) : q.markedClause.length ≤ A := by
  unfold Factor.Spec.markedClause
  by_cases h : q.mark < q.source.length
  · simpa only [List.getElem?_eq_getElem h, Option.getD_some] using
      hsource q.source[q.mark] (List.getElem_mem h)
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt h)]

/-- Integer lifting assigns a weight to each original clause without
changing its literal list. -/
theorem weighted_width {n : ℕ} (t d A : ℕ)
    (source : List (List (SAT.Literal (Fin n))))
    (hsource : ∀ ls ∈ source, ls.length ≤ A)
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3)) :
    ∀ w ∈ HashInputProgram.Expansion.weightedRow t d source terms,
      w.literals.length ≤ A := by
  intro w hw
  obtain ⟨a,_ha,rfl⟩ := List.mem_map.mp hw
  exact hsource _ (List.getElem_mem _)

/-- The only physical premises are the three immutable source words. -/
theorem spec_words {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (a : StructuredProgram.State 40 768) (A : ℕ)
    (hformula : a.stacks 700 = Encoding.encodeList id q.clauses)
    (hrows : a.stacks 701 = Encoding.encodeList id q.rawRows)
    (hwidth : (a.stacks 708).length = q.bitWidth)
    (h700 : (a.stacks 700).length ≤ A)
    (h701 : (a.stacks 701).length ≤ A)
    (h708 : (a.stacks 708).length ≤ A) :
    q.bitWidth ≤ A ∧
    (∀ f (hf : f < q.rows.length), q.rows[f].length ≤ A) ∧
    q.markedClause.length ≤ A ∧
    (∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ A) := by
  have hs : ∀ ls ∈ q.source, ls.length ≤ A := by
    intro ls hls
    apply (source_clause_length q.source ls hls).trans
    simpa only [hformula, Factor.Spec.clauses] using h700
  refine ⟨hwidth ▸ h708, ?_, marked_clause_length q A hs, ?_⟩
  · intro f hf
    apply (row_length_le_stream q.bitWidth q.bitWidthPositive q.rows f hf).trans
    have hraw : q.rawRows = q.rows.map (HashScopeProgram.RawTable.rowBits q.bitWidth) := by
      unfold Factor.Spec.rawRows HashScopeProgram.RawTable.rowBits
        HashInputProgram.Loop.rawInput
      simp only [List.reverse_reverse]
    change (Encoding.encodeList id
      (q.rows.map (HashScopeProgram.RawTable.rowBits q.bitWidth))).length ≤ A
    rw [← hraw, ← hrows]
    exact h701
  · intro f hf
    exact weighted_width q.p.t d A q.source hs q.rows[f]

section Produced
variable (s : LeafHeadSetupProgram.Native.Inputs)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect s.height
      (LeafHeadSetupProgram.unary s.R) s.width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : s.Q < 3^(m.val 34)) (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin s.n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)

local notation "spec" => nativeSpecOfInputs s m ht hd words hc M cache half e hp
  hfield q hv J hJ source hsource

/-- These are the row, marked-clause and width bounds for the genuine
produced ring and addressed native-input factor, with no new source service. -/
theorem produced_words (a : StructuredProgram.State 40 768) (A : ℕ)
    (ha : LeafProgram.Query.Sources q a)
    (h700 : (a.stacks 700).length ≤ A)
    (h701 : (a.stacks 701).length ≤ A)
    (h708 : (a.stacks 708).length ≤ A) :
    (spec).bitWidth ≤ A ∧
    (∀ f (hf : f < (spec).rows.length), (spec).rows[f].length ≤ A) ∧
    (spec).markedClause.length ≤ A ∧
    (∀ f (hf : f < (spec).rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow (spec).p.t (m.val 34)
        (spec).source (spec).rows[f], w.literals.length ≤ A) := by
  apply spec_words (spec) a A _ _ _ h700 h701 h708
  · exact ha.formula.trans (congrArg (Encoding.encodeList id) hsource)
  · exact ha.rows.trans (nativeSpecOfInputs_rows s m ht hd words hc M cache half e hp
      hfield q hv J hJ source hsource).symm
  · exact congrArg List.length ha.width

end Produced
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryWordBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeSourceBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete capacities for the actual addressed node source. Its reference
snapshot is bounded only by retained query words, independently of caller
scratch, node index and the actual bootstrap cache witness. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram LeafParametersProgram LeafProgram
open QueryNodeEvaluation


variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
variable (a : QueryNodeEvaluation.Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)


local notation "src" => nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc

/-- The guard actually executed by the query supplies the row-radius bound. -/
theorem radius : (src).input.R+1 ≤ (src).input.Q := by
  change (produce (query.input k)).R+1 ≤ (produce (query.input k)).Q
  have hQ := hg.2.2.2.2.2.2.1
  have hR := hg.2.2.2.2.2.2.2.1
  omega

section Factor
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3^(m.val 34))
    (hv : query.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
    (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
  hfield query hv hJ source hsource

/-- The actual frontend words and actual produced scalar bank discharge
all one-head numeric fields for this SAME restricted node source. Width A
bounds literal storage only; the traversal still uses the selected-head size. -/
theorem headBounds_oai
    (hvalues : ∀ i, m.val i ≤ A)
    (hsources : LeafProgram.Query.Sources query
      (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a))
    (h700 : (a.stacks 700).length ≤ A)
    (h701 : (a.stacks 701).length ≤ A)
    (h708 : (a.stacks 708).length ≤ A) :
    QueryVisitorHead.HeadBounds (src).input spec A (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) (src).bound A := by
  obtain ⟨hbit,hrows,hmark,hwidth⟩ := NativeQueryWordBounds.produced_words
    (src).input m ht hd (src).cacheWords (src).cache M cache half e hp
    hfield query hv (m.val 42) hJ source hsource
    (projectState (id : Fin 40 → Fin 40) QueryAssembler.Nodes.lowPort a) A
    hsources h700 h701 h708
  exact QueryHeadBudgets.headBounds (src).input spec (src).source A (src).bound A A
    (src).ready (src).bounded (Nat.le_refl A) (Nat.le_refl A)
    (hvalues 34) (hvalues 33) (hvalues 33) (hvalues 42) hbit (Nat.le_refl A)
    hrows hmark rfl rfl rfl (src).input.plans_length
    (radius query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc) hwidth

end Factor

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.headBounds_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.headBounds_oai
