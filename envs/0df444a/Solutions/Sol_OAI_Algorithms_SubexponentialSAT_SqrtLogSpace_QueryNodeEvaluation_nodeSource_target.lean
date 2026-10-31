-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_target
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:37:27.592185+00:00
-- url     : https://prove2.me/submissions/feb1cb8c-51d6-4057-bd2d-e301ee60f142

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryEmittedSourceTarget_signed_target
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryHeadSourceCoverage_hash_literals
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryHeadSourceCoverage_marked_literals
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryHeadSourceSlots_inventory_slots

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_BooleanDifferences
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Boolean finite differences (ETH, Lemma `boolean-differences`).
The finite sets in this module specify sums; they are not operational enumerators. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences

open scoped BigOperators

/-- A coordinate equivalence transports the iterator's pairs exactly. This is
an internal indexing change, not a change of the ambient assignment universe. -/
theorem pairFamily_map_equiv {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} (e : Fin n ≃ V) (J : ℕ) :
    (pairFamily n J).map (Equiv.prodCongr e.finsetCongr e.finsetCongr).toEmbedding =
      Finset.univ.filter (fun p : Finset V × Finset V => p.1.card < J ∧ p.2 ⊆ p.1) := by
  ext p
  rcases p with ⟨E, U⟩
  simp [Finset.mem_map_equiv, Equiv.prodCongr, Equiv.finsetCongr]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical radix generator emits precisely the coefficient encoding of
nodes in the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open RingProgram

theorem nodeCode_value (t d n : ℕ) (ht : 0 < t) (j : Fin d) :
    BinaryArithmetic.toNat (nodeCode t d n j).val = n / 3^j.val % 3 := by
  apply toNat_fixedBits_of_lt
  have hc : 2^2 ≤ 2^(2*t) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [ternary_baseWidth]
  have hm := Nat.mod_lt (n / 3^j.val) (by decide : 0 < 3)
  norm_num at hc
  omega

theorem residueNode_coordinate {d : ℕ} (a : RingModel.Data d) (Q : ℕ)
    (hQ : Q < 3^d) (i : Fin Q) (j : Fin d) :
    (a.fieldCoordinates (a.residueNode Q hQ i) j).val = (i.val+1) / 3^j.val % 3 := by
  let index : Fin (3^d) := ⟨i.val+1, by omega⟩
  let v : Fin d → ZMod 3 := fun j =>
    ZMod.finEquiv 3 ((finFunctionFinEquiv.symm index) j)
  change (a.fieldCoordinates (a.fieldCoordinates.symm v) j).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The physical words decode to the same nodes used by interpolation. -/
theorem nodeCode_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (Q : ℕ) (hQ : Q < 3^d) (i : Fin Q) :
    (modelRing t ht hd a M cache).decode (nodeCode t d (i.val+1)) =
      a.node t Q ht hQ i := by
  rw [modelRing_decode]
  unfold RingModel.Data.node RingModel.Data.sectionValue
  congr 1
  funext j
  unfold wordValue
  rw [nodeCode_value t d (i.val+1) ht j, residueNode_coordinate]

end SubexponentialSAT.SqrtLog.RingNodeProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The rank certificate refers to the packing and word table actually
produced by the native packing caller, with its original incidence order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram

theorem packing_head (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (i : Fin p.incidences) (t : Fin p.Q) :
    ((packing p a tail).label i).head t=words p a tail (.inl (owner p i)) t := rfl

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

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

theorem nativeSpecOfInputs_theta : (spec).p.ops.decode (spec).theta =
    (IrreducibleSearch.data hd).node (m.val 33) s.Q ht hfield s.node := by
  exact RingNodeProgram.nodeCode_decode _ ht hd _ M cache _ hfield s.node

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSourceAlignment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The frontend's actual mask, the produced head rows and the authentic
source factory use the same ambient variables and the same full integer keys.
No selected-coordinate or factory-alignment witness is supplied by the caller. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment

open scoped BigOperators
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram
open BucketTupleProgram.Concrete

section Query
attribute [local instance] Classical.propDecidable
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
local notation "head" => (fun t v => ProducedQueryRank.words p first tail (Sum.inl v) t)
local notation "owner" => ProducedQueryRank.owner p
include q k hg first tail node

/-- Factor rows follow all ambient head rows in the actual produced table. -/
theorem factor_row (f : Fin (p).factors) :
    (s).rows.getD ((p).n+f.val) [] =
      Subexp.ReadPlan.encodeWord (ProducedQueryRank.words p first tail (.inr f)) := by
  have hf : (p).n+f.val < ((p).words first tail).length := by
    rw [(p).words_length]
    omega
  change (((p).words first tail).map Subexp.ReadPlan.encodeWord).getD ((p).n+f.val) [] = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hf), List.getElem_map]
  rfl

theorem factor_predicate (g : Fin (p).r) (f : Fin (p).factors) :
    LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val) f.val =
      decide (ProducedQueryRank.words p first tail (.inr f) node = g) := by
  change ((s).rows.getD ((p).n+f.val) []).getD (node.val*(p).r+g.val) false = _
  rw [factor_row, HeadIdentifierProgram.encodeWord_getD]

/-- The physical factor stream is the complete increasing filter by its
produced color, including every neutral factor for an unused low variable. -/
theorem factor_ids (g : Fin (p).r) :
    LeafHeadFactorsProgram.chosenIds
      (LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val)) (s).N =
      (List.range (p).factors).filter (fun f =>
        if hf : f < (p).factors then
          decide (ProducedQueryRank.words p first tail (.inr ⟨f,hf⟩) node = g)
        else false) := by
  apply List.filter_congr
  intro f hf
  have hlt : f < (p).factors := List.mem_range.mp hf
  simpa only [dite_eq_left hlt] using
    factor_predicate q k hg first tail node g ⟨f,hlt⟩

/-- The owner and head are read from the original produced packing. -/
theorem owner_head (i : Fin (s).D) (t : Fin (s).Q) :
    ((s).packing.label i).head t = head t (owner i) :=
  ProducedQueryRank.packing_head p first tail i t


section Produced
open SubexpLiftRing SubexpQuarticRing
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : CacheCorrect (Native.queryInputsAddressed q k hg first tail node).height (unary (Native.queryInputsAddressed q k hg first tail node).R) (Native.queryInputsAddressed q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed q k hg first tail node).Q < 3^(m.val 34)) (hv : q.Valid) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => LeafProgram.PreparedSource.nativeSpecOfInputs s m ht hd words hc
  M cache half e hp hfield q hv J hJ source hsource
local notation "sourceOwner" => owner ∘ Fin.cast (Native.Inputs.plans_length s)
include m ht hd words hc M cache half e hp hfield hv J hJ source hsource

theorem produced_owner_head (i : Fin (spec).ps.length) (t : Fin (p).Q) :
    ((spec).packing.label i).head t = head t (sourceOwner i) := by
  have hps : (spec).ps.length=(s).plans.length := rfl
  let i' : Fin (s).plans.length := Fin.cast hps i
  change ((PackingIncidenceInput.reindexPacking (s).plans_length.symm
    (s).packing).label i').head t = _
  rw [PackingIncidenceInput.reindexPacking_label]
  have ho : owner (Fin.cast (s).plans_length i') = sourceOwner i := Fin.ext rfl
  exact (owner_head q k hg first tail node (Fin.cast (s).plans_length i') t).trans
    (congrArg (head t) ho)

end Produced
end Query
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadSourceSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual addressed factor lookup and reindexed source packing have the
same factor slot. The physical selected factor lists are complete color
filters, including neutral factors for unused low variables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open MulticolorTypes Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram LeafProgram
open SignatureTupleSourceAlignment
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
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

/-- The actual671 factor records, copied once to175, are exactly the original
semantic color filter of the complete ambient factor inventory. -/
theorem factorIds_eq_color (g : Fin (p).r) :
    QueryVisitorHead.factorIds s g =
      (List.range (s).N).filter (fun f => LeafProgram.NodeConcrete.planColor p first tail node f = g) := by
  change LeafHeadFactorsProgram.chosenIds
    (LeafHeadFactorsProgram.predicate (s).rows (s).n (node.val*(p).r+g.val)) (s).N = _
  rw [factor_ids q k hg first tail node g]
  apply List.filter_congr
  intro f hf
  have hlt : f < (p).factors := List.mem_range.mp hf
  simp only [LeafProgram.NodeConcrete.planColor,dite_eq_left hlt]

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots
end
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
local notation "p" => LeafProgram.Query.packingProblem q k hg
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



/-- The source factory retains every original hash row exactly once. -/
theorem weighted_rows_length :
    (AssignmentConcrete.weightedHashes spec).length = q.rows.length := by
  change ((PreparedSource.castRows (congrArg List.length hsource) q.rows).map
    (HashInputProgram.Expansion.weightedRow (m.val 33) (m.val 34) source)).length = q.rows.length
  simp only [List.length_map,PreparedSource.castRows_length]

/-- The actual scope counter includes all original hashes and every neutral
factor appended for low variables. -/
theorem inventory_hashes :
    ∀ id < (AssignmentConcrete.weightedHashes spec).length, id ∈ List.range (s).N := by
  intro id hid
  rw [weighted_rows_length] at hid
  have hs := PackingIncidenceInput.Semantics.counter_mono q.scopeRows q.forward 0 q.scopeRows.length
  change q.scopeRows.length ≤ (p).factors at hs
  rw [LeafQueryFrontend.Query.scopeRows,HashScopeProgram.Complete.scopes_length] at hs
  apply List.mem_range.mpr
  change id < (p).factors
  omega

/-- A present marked factor occupies its actual index after the hash rows. -/
theorem inventory_marked :
    (spec).marked = true → (AssignmentConcrete.weightedHashes spec).length ∈ List.range (s).N := by
  intro hm
  change q.mark.isSome = true at hm
  rw [weighted_rows_length]
  have hs := PackingIncidenceInput.Semantics.counter_mono q.scopeRows q.forward 0 q.scopeRows.length
  change q.scopeRows.length ≤ (p).factors at hs
  rw [LeafQueryFrontend.Query.scopeRows,HashScopeProgram.Complete.scopes_length,hm] at hs
  simp only [Bool.toNat_true] at hs
  apply List.mem_range.mpr
  change q.rows.length < (p).factors
  omega

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual finite-difference callback uses the physical pair masks and
one semantic node accumulator. The reference support decoding below is used
only in the proof; the executed controller retains its four finite words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction
open SignatureTupleSource
open scoped BigOperators
open SqrtLog.ProgramTapeReplay

/-- Reindex the actual finite-coordinate pair sum by the chosen free-variable
equivalence. The ambient assignment universe is not changed. -/
theorem sum_pairs_transport {V R : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid R] {N : ℕ} (e : Fin N ≃ V) (J : ℕ)
    (f : Finset V → Finset V → R) :
    (∑ pair ∈ BooleanDifferences.pairFamily N J,
      f (e.finsetCongr pair.1) (e.finsetCongr pair.2)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card<J),
        ∑ U ∈ E.powerset,f E U := by
  classical
  let S := Finset.univ.filter (fun E : Finset V => E.card<J)
  have hset : (Finset.univ.filter (fun p : Finset V × Finset V => p.1.card<J ∧ p.2⊆p.1))=
      S.biUnion (fun E => E.powerset.image (fun U => (E,U))) := by
    ext p
    rcases p with ⟨E,U⟩
    simp [S,Finset.mem_biUnion,Finset.mem_image]
  have hd : (S : Set (Finset V)).PairwiseDisjoint
      (fun E => E.powerset.image (fun U => (E,U))) := by
    intro E _ F _ hEF
    apply Finset.disjoint_left.mpr
    intro pair hp hq
    obtain ⟨U,_,hU⟩ := Finset.mem_image.mp hp
    obtain ⟨W,_,hW⟩ := Finset.mem_image.mp hq
    exact hEF (congrArg Prod.fst (hU.trans hW.symm))
  calc
    _=∑ pair ∈ (BooleanDifferences.pairFamily N J).map
        (Equiv.prodCongr e.finsetCongr e.finsetCongr).toEmbedding,f pair.1 pair.2 := by
      rw [Finset.sum_map]
      rfl
    _=∑ pair ∈ S.biUnion (fun E => E.powerset.image (fun U => (E,U))),f pair.1 pair.2 := by
      rw [BooleanDifferences.pairFamily_map_equiv,hset]
    _=_ := by
      rw [Finset.sum_biUnion hd]
      apply Finset.sum_congr rfl
      intro E _
      rw [Finset.sum_image]
      intro U _ W _ heq
      exact (Prod.mk.inj heq).2

/-- The native finite-index sum is the exact free-coordinate sum consumed by
the source-target identity. Both masks retain their ambient-coordinate images. -/
theorem signed_sum_free (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head) :
    (∑ pair ∈ BooleanDifferences.pairFamily (s.input.n-H.card) q.J,
      (-1)^(pair.1.card-pair.2.card)*pairValue s q H high owner head facts pair.1 pair.2) =
    ∑ E ∈ Finset.univ.filter (fun E : Finset (ResidualEmbedding.Free H) => E.card<q.J),
      ∑ U ∈ E.powerset,(-1)^(E.card-U.card)*
        SignatureTupleRun.tupleTotal s.key s.input.r
          (SignatureTupleRun.emittedValue s q H (E.image Subtype.val) (U.image Subtype.val)
            high owner head facts) := by
  classical
  have ht := sum_pairs_transport (HighIncidenceProgram.freeOrder H) q.J
    (fun E U => (-1)^(E.card-U.card)*SignatureTupleRun.tupleTotal s.key s.input.r
      (SignatureTupleRun.emittedValue s q H (E.image Subtype.val) (U.image Subtype.val)
        high owner head facts))
  simp only [Equiv.finsetCongr_apply,Finset.card_map] at ht
  simpa only [pairValue,Finset.map_eq_image,Finset.image_image,Function.comp_def,
    Equiv.toEmbedding_apply] using ht

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAddressedTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual addressed source, generated ring and complete native factor
inventory instantiate the signed pair target. There is no independently
supplied label kernel, slot assignment, source coverage or evaluator. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAddressedTarget
open scoped BigOperators
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog Polynomial
open MulticolorTypes Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram LeafProgram
open SignatureTupleSourceAlignment
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
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
local notation "owner" => ProducedQueryRank.owner p
local notation "sourceOwner" => owner ∘ Fin.cast (Native.Inputs.plans_length s)
local notation "head" => (fun t v => ProducedQueryRank.words p first tail (Sum.inl v) t)
local notation "H" => HighMarkedFrontend.highSet q



local notation "facts" => QueryHeadSourceFacts.sourceFacts q k hg first tail node physical ready
  bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource

/-- The pair loop's actual value is the Taylor jet of the original source
target at the actual generated node, including every neutral factor. -/
theorem signed_pair_target (high : H → Bool) :
    (∑ pair ∈ BooleanDifferences.pairFamily ((s).n - (H).card) (spec).J,
      (-1)^(pair.1.card - pair.2.card) *
        QueryPairEvaluation.pairValue src spec H high sourceOwner head facts pair.1 pair.2) =
      Truncated.ofPolynomial (spec).J ((NodeConcrete.specTarget spec H high).comp
        (X + C ((spec).p.ops.decode (spec).theta))) := by
  refine (QueryPairEvaluation.signed_sum_free src spec H high sourceOwner head facts).trans ?_
  apply QueryEmittedSourceTarget.signed_target src spec H high sourceOwner head facts rfl
    (plans_owner q k hg first tail node)
    (produced_owner_head q k hg first tail node m ht hd words hc M cache half e hp
      hfield hv (m.val 42) hJ source hsource)
    (PreparedSource.nativeSpecOfInputs_theta s m ht hd words hc M cache half e hp
      hfield q hv (m.val 42) hJ source hsource)
    (List.range (s).N) List.nodup_range
    (QueryHeadSourceCoverage.inventory_hashes q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)
    (QueryHeadSourceCoverage.inventory_marked q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)
    (NodeConcrete.planColor p first tail node)
    (QueryHeadSourceSlots.factorIds_eq_color q k hg first tail node)
    (QueryHeadSourceSlots.inventory_slots q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)
    (QueryHeadSourceCoverage.hash_literals q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)
    (QueryHeadSourceCoverage.marked_literals q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAddressedTarget
end
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

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

section AddressedSource
variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
local notation "native" => Native.queryInputsAddressed query k hg first tail node
variable (a : Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length ≤ A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)

local notation "src" => nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc

section FactorRun
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
  (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
  (cache : RingProgram.ScalarCache 3 (m.val 33))
  (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
  (produced : LeafRingSetupProgram.Produced m hd M cache half e)
  (hfield : (Native.queryInputsAddressed query k hg first tail node).Q < 3^(m.val 34)) (hv : query.Valid) (hJ : 0 < m.val 42)
  (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed query k hg first tail node).n))))
  (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e produced
  hfield query hv hJ source hsource
local notation "H" => HighMarkedFrontend.highSet query
local notation "sourceOwner" => ProducedQueryRank.owner (LeafProgram.Query.packingProblem query k hg) ∘
  Fin.cast (Native.Inputs.plans_length native)
local notation "sourceHead" => (fun t v => ProducedQueryRank.words
  (LeafProgram.Query.packingProblem query k hg) first tail (Sum.inl v) t)
local notation "sourceFacts" => nodeSource_facts query k hg first tail node a bits remaining A
  hbank hparked ra rd rc words hc m ht hd M cache half e produced hfield hv hJ source hsource

include hfield source hsource in
/-- The very addressed source and cache produced for this node instantiate
all source-target correspondence conditions of the completed pair run. -/
theorem nodeSource_target_oai (high : H → Bool) :
    (∑ pair ∈ BooleanDifferences.pairFamily ((native).n-(H).card) (spec).J,
      (-1)^(pair.1.card-pair.2.card)*
        QueryPairEvaluation.pairValue src spec H high sourceOwner sourceHead sourceFacts
          pair.1 pair.2) =
      Truncated.ofPolynomial (spec).J ((NodeConcrete.specTarget spec H high).comp
        (Polynomial.X+Polynomial.C ((spec).p.ops.decode (spec).theta))) :=
  QueryAddressedTarget.signed_pair_target query k hg first tail node
    (QuerySourceSnapshot.snapshot (sourceSnapshot a bits remaining))
    (QuerySourceSnapshot.snapshot_ready (sourceSnapshot_ready native a bits remaining hbank))
    A (QuerySourceSnapshot.snapshot_bound _ A
      (sourceSnapshot_bank_bound native a bits remaining A hbank hparked))
    ra rd rc words hc m ht hd M cache half e produced hfield hv hJ source hsource high


end FactorRun

end AddressedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_target_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_target_oai
