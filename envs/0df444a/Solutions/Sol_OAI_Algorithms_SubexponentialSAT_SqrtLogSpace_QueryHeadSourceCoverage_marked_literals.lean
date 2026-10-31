-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.marked_literals
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:14:49.239791+00:00
-- url     : https://prove2.me/submissions/cf4964b1-e013-40b2-ba8e-63fd95349449

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S188

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem encodeList_injective {α : Type*} {enc : α → List Bool}
    (hinj : Function.Injective enc) : Function.Injective (encodeList enc) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs <;> simp_all [encodeList]
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [encodeList] at h
      | cons b bs =>
          have ht : frame (enc a) ++ encodeList enc as =
              frame (enc b) ++ encodeList enc bs := by
            simpa only [encodeList, List.cons.injEq, true_and] using h
          obtain ⟨hab, htail⟩ := frame_append_injective ht
          exact congrArg₂ List.cons (hinj hab) (ih htail)

end SubexponentialSAT.Encoding

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime outer record fold computing the maximum masked scope length and
factor count, including empty scope records. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
@[simp] theorem decoded_encode (scope : List ℕ) :
    decoded (Encoding.encodeList Encoding.encodeNat scope) = scope := by
  classical
  unfold decoded
  split
  · rename_i h
    exact Encoding.encodeList_injective Encoding.encodeNat_injective (Classical.choose_spec h)
  · rename_i h
    exact (h ⟨scope,rfl⟩).elim

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Arity

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLeafSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Typed sparse-leaf semantics at the actual finalizer boundary

The byte test below is a finite reference computation used only in the
correctness statement. The fast callback obtains its answer from the actual
moment, reconstruction, and finalizer programs. No execution or fast bound
for this reference decoder/search is asserted.
-/

namespace SubexponentialSAT.SubexpLeafSemantics

open StructuredCalls SubexpQuarticRing

theorem literalCode_div_two {n : ℕ} (l : SAT.Literal (Fin n)) :
    Encoding.literalCode l / 2 = l.variable.val := by
  rcases l with ⟨v, sign⟩
  cases sign <;> simp [Encoding.literalCode] ; omega

end SubexponentialSAT.SubexpLeafSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Every queried low literal is in the physical raw-scope incidence list.
Zero coefficients and repeated literal occurrences are retained. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT
open HashInputProgram HashScopeProgram

variable {n : ℕ}

theorem encoded_clause_codes (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i,clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (source : List (List (SAT.Literal (Fin n))))
    (hs : clauses=Expansion.encodedClauses source) (i : Fin clauses.length) :
    codes i=(Expansion.originalClause source (Fin.cast (congrArg List.length hs) i)).map Encoding.literalCode := by
  subst clauses
  apply Encoding.encodeList_injective Encoding.encodeNat_injective
  rw [←hc,←HashInputProgram.clausePayload_codes]
  simp only [Expansion.originalClause,Expansion.encodedClauses,List.getElem_map]
  rfl

theorem literal_mem_marked_scope (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (source : List (List (SAT.Literal (Fin n))))
    (hs : clauses=Expansion.encodedClauses source)
    (hc : ∀ i,clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (i : Fin clauses.length) (l : SAT.Literal (Fin n))
    (hl : l∈Expansion.originalClause source (Fin.cast (congrArg List.length hs) i)) :
    l.variable.val∈Marked.markedScope (codes i) := by
  rw [SubexpScopeProducer.mem_scope]
  refine ⟨Encoding.literalCode l,?_,?_⟩
  · rw [encoded_clause_codes clauses codes hc source hs]
    exact List.mem_map.mpr ⟨l,hl,rfl⟩
  · simpa [BinaryArithmetic.toNat] using SubexpLeafSemantics.literalCode_div_two l

theorem addressed_original_present (scopes : List (List ℕ)) (mask : List Bool)
    (ambient owner factor : ℕ) (ho : owner∈LeafStatisticsSemantics.lowOwners 0 mask)
    (hf : factor < scopes.length) (hs : owner∈scopes[factor]) :
    (owner,ambient+factor)∈PackingIncidenceInput.addressedEntries scopes ambient mask := by
  apply List.mem_map.mpr
  refine ⟨(owner,factor),?_,rfl⟩
  apply (LeafStatisticsSemantics.native_original_mem scopes mask 0 scopes.length owner factor le_rfl hf).mpr
  refine ⟨ho,?_⟩
  change factor∈Subexp.IncidencePlanSpec.incidentIndices scopes owner
  exact (Subexp.IncidencePlanSpec.mem_incidentIndices scopes owner ⟨factor,hf⟩).mpr hs

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteQueryScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Query-level incidence coverage follows from the native raw scope parser.
A fixed high literal needs no incidence; every low queried literal has one. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT HashInputProgram HashScopeProgram

variable (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))))
    (hs : q.clauses=Expansion.encodedClauses source)

theorem query_lowOwner (v : Fin (BinaryArithmetic.toNat q.ambient))
    (hlow : q.forward.getD v.val false=false) :
    v.val∈LeafStatisticsSemantics.lowOwners 0 q.forward := by
  have hlen : q.forward.length=BinaryArithmetic.toNat q.ambient := by
    simp [LeafQueryFrontend.Query.forward,LeafQueryFrontend.highMask]
  have hb : v.val < q.forward.length := by omega
  apply (LeafStatisticsSemantics.lowOwners_mem 0 v.val q.forward).mpr
  refine ⟨⟨v.val,hb⟩,by simp,?_⟩
  simpa only [List.getD_eq_getElem _ _ hb,List.get_eq_getElem] using hlow

include hv in
theorem query_marked_literal_present (i : Fin q.clauses.length) (hm : q.mark=some i)
    (l : SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))
    (hl : l∈Expansion.originalClause source (Fin.cast (congrArg List.length hs) i))
    (hlow : q.forward.getD l.variable.val false=false) :
    (l.variable.val,BinaryArithmetic.toNat q.ambient+q.rows.length)∈
      PackingIncidenceInput.addressedEntries q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward := by
  have hfl : q.rows.length < q.scopeRows.length := by
    simp only [LeafQueryFrontend.Query.scopeRows,Complete.scopes_length,hm,Option.isSome_some,Bool.toNat_true]
    omega
  apply addressed_original_present q.scopeRows q.forward _ _ _ (query_lowOwner q l.variable hlow) hfl
  have he : q.scopeRows[q.rows.length]=Marked.markedScope (q.codes i) := by
    simp only [LeafQueryFrontend.Query.scopeRows,Complete.scopes,hm,Option.toList_some,List.map_cons,List.map_nil]
    rw [List.getElem_append_right (by simp)]
    simp
  rw [he]
  exact literal_mem_marked_scope q.clauses q.codes source hs hv.2.2.1 i l hl

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteQueryLiterals
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact weighted clauses supplied to the native factor interpreter
inherit their low-literal incidence entries from the original query. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT HashInputProgram
open HashCircuitProgram HashCircuitProgram.Native

variable (q : LeafQueryFrontend.Query) (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))))
    (hs : q.clauses=Expansion.encodedClauses source)

include hv hs in
 theorem query_marked_clause_present (hm : q.mark.isSome=true)
    (l : SAT.Literal (Fin (BinaryArithmetic.toNat q.ambient)))
    (hl : l∈source[PreparedSource.markIndex q]?.getD [])
    (hlow : q.forward.getD l.variable.val false=false) :
    (l.variable.val,BinaryArithmetic.toNat q.ambient+q.rows.length)∈
      PackingIncidenceInput.addressedEntries q.scopeRows (BinaryArithmetic.toNat q.ambient) q.forward := by
  cases hq : q.mark with
  | none => simp [hq] at hm
  | some i =>
    have hi : i.val < source.length := by simpa only [hs,Expansion.encodedClauses,List.length_map] using i.isLt
    have hmidx : PreparedSource.markIndex q=i.val := by simp [PreparedSource.markIndex,hq]
    rw [hmidx] at hl
    have hli : l∈Expansion.originalClause source (Fin.cast (congrArg List.length hs) i) := by
      simpa [List.getElem?_eq_getElem hi,Expansion.originalClause] using hl
    exact query_marked_literal_present q hv source hs i hq l hli hlow

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadSourceCoverage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Every actual hash and marked factor is retained, and every low literal
in its interpreted source has its real ambient-address incidence. This uses
the same sourceSpec and complete factor inventory as the native visitor. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram LeafProgram
open SignatureTupleSourceAlignment
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
variable (physical : Data)
  (ready : Native.Ready (Native.queryInputsAddressed q k hg first tail node) physical)
  (bound : ℕ) (bounded : OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound bound physical)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed q k hg first tail node).height
    (unary (Native.queryInputsAddressed q k hg first tail node).R)
    (Native.queryInputsAddressed q k hg first tail node).width words)

local notation "src" => QueryHeadSourceFacts.addressedSource q k hg first tail node physical ready bound bounded ra rd rc words hc
section Factor
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed q k hg first tail node).Q < 3^(m.val 34))
    (hv : q.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
  hfield q hv hJ source hsource
local notation "H" => HighMarkedFrontend.highSet q



/-- The source factory retains every original hash row exactly once. -/
theorem weighted_rows_length :
    (AssignmentConcrete.weightedHashes spec).length = q.rows.length := by
  change ((PreparedSource.castRows (congrArg List.length hsource) q.rows).map
    (HashInputProgram.Expansion.weightedRow (m.val 33) (m.val 34) source)).length = q.rows.length
  simp only [List.length_map,PreparedSource.castRows_length]

/-- The physical forward mask recognizes precisely the actual free variables. -/
theorem low_word (v : Fin (s).n) (hvH : v ∉ H) : q.forward.getD v.val false = false := by
  have hv : v.val < BinaryArithmetic.toNat q.ambient := v.isLt
  let v' : Fin (BinaryArithmetic.toNat q.ambient) := ⟨v.val,hv⟩
  have hv' : v' = v := Fin.ext rfl
  rw [forward_bits q]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hv),
    List.getElem_ofFn]
  have hnot : v' ∉ H := hv'.symm ▸ hvH
  exact decide_eq_false hnot

/-- The actual optional marked clause has the same saved low-literal
incidences, at the index immediately following all original hashes. -/
theorem marked_literals_oai :
    (spec).marked = true → (AssignmentConcrete.weightedHashes spec).length ∈ List.range (s).N →
      ∀ l ∈ (spec).markedClause, l.variable ∉ H →
        (l.variable.val,(s).n+(AssignmentConcrete.weightedHashes spec).length) ∈ (spec).ps := by
  intro hm _ l hl hlow
  rw [weighted_rows_length]
  exact LeafProgram.NodeConcrete.query_marked_clause_present q hv source hsource hm l hl
    (low_word q k hg first tail node l.variable hlow)

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.marked_literals_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage.marked_literals_oai
