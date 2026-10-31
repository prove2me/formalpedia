-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots.inventory_slots
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:15:13.479781+00:00
-- url     : https://prove2.me/submissions/49f323a8-8b78-4e0d-bc25-b9055e497c30

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S188

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcretePlan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The original-address source lookup is exactly the owner pullback used by
integer-bucket locality, including repeated owner incidences. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly LayoutPullback

variable {r Q d n : ℕ}

theorem planIndex_get (ps : List (ℕ × ℕ)) (n f j : ℕ) (h : (j,n+f)∈ps) :
    ps.get (planIndex ps n f j h)=(j,n+f) := by
  simpa only [planIndex,List.idxOf,beq_eq_decide] using
    List.idxOf_get (List.idxOf_lt_length_iff.mpr h)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputAddressedProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lookup and label provenance for the actual ambient-offset plan records.
The lemmas apply to any exact list lookup, including the first matching plan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes PackingCallerProgram

 theorem addressed_raw_of_get (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (i : Fin (addressedEntries scopes n mask).length) (j f : ℕ)
    (hget : (addressedEntries scopes n mask).get i = (j,n+f)) :
    (Semantics.nativeEntries scopes mask).get (addressedIndex scopes n mask i) = (j,f) := by
  rw [addressedEntries_get] at hget
  have h1 := congrArg Prod.fst hget
  have h2 := congrArg Prod.snd hget
  apply Prod.ext
  · exact h1
  · exact Nat.add_left_cancel h2

 theorem addressed_factor_of_get (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hm : mask.length ≤ n) (i : Fin (addressedEntries scopes n mask).length) (j f : ℕ)
    (hget : (addressedEntries scopes n mask).get i = (j,n+f)) :
    (Semantics.factor scopes n mask hm (addressedIndex scopes n mask i)).val = f :=
  congrArg Prod.snd (addressed_raw_of_get scopes n mask i j f hget)

 theorem addressedPacking_slot_of_get (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (i : Fin (addressedEntries p.scopes p.n p.mask).length)
    (j : ℕ) (f : Fin p.factors)
    (hget : (addressedEntries p.scopes p.n p.mask).get i = (j,p.n+f.val)) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label i).slot 0 =
      ProducedQueryRank.words p a tail (.inr f) := by
  rw [addressedPacking_slot]
  have he : ProducedQueryRank.factor p (addressedIndex p.scopes p.n p.mask i) = f :=
    Fin.ext (addressed_factor_of_get p.scopes p.n p.mask p.mask_le i j f.val hget)
  rw [he]

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteQueryPlan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Head coherence, low-owner support, and factor colors for the exact
addressed query plan stream. No semantic plan relation is supplied. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram PackingIncidenceInput

variable (p : Problem)

theorem addressedPlan_slot (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (t : Fin p.Q) (f j : ℕ) (hp : (j,p.n+f)∈addressedEntries p.scopes p.n p.mask) :
    ((addressedPacking p.scopes p.n p.mask (ProducedQueryRank.packing p a tail)).label
      (planIndex (addressedEntries p.scopes p.n p.mask) p.n f j hp)).slot 0 t=planColor p a tail t f := by
  let i := planIndex (addressedEntries p.scopes p.n p.mask) p.n f j hp
  have he := planIndex_get (addressedEntries p.scopes p.n p.mask) p.n f j hp
  have hf' := addressed_factor_of_get p.scopes p.n p.mask p.mask_le i j f he
  have hf : f < p.factors := by
    rw [←hf']
    exact (ProducedQueryRank.factor p (addressedIndex p.scopes p.n p.mask i)).isLt
  have hs := addressedPacking_slot_of_get p a tail i j ⟨f,hf⟩ he
  simp only [planColor,dite_eq_left hf]
  exact congrArg (fun w=>w t) hs

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadSourceSlots
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

/-- The original semantic factor-color map agrees with every actual source
lookup. The addressed plan stream itself proves the factor index is in range. -/
theorem source_color (f j : ℕ) (hj : (j,(s).n+f) ∈ (spec).ps) :
    ((spec).packing.label (LeafProgram.NodeConcrete.planIndex (spec).ps (s).n f j hj)).slot 0 node =
      LeafProgram.NodeConcrete.planColor p first tail node f := by
  exact LeafProgram.NodeConcrete.addressedPlan_slot p first tail node f j hj

/-- Exactly the premise used by signed_source_target for the complete actual
factor inventory; no slot/color hypothesis is supplied by its caller. -/
theorem inventory_slots_oai :
    ∀ f ∈ List.range (s).N, ∀ j (hj : (j,(s).n+f) ∈ (spec).ps),
      ((spec).packing.label (LeafProgram.NodeConcrete.planIndex (spec).ps (s).n f j hj)).slot 0 node =
        LeafProgram.NodeConcrete.planColor p first tail node f := by
  intro f _ j hj
  exact source_color q k hg first tail node physical ready bound bounded ra rd rc words hc
    m ht hd M cache half e hp hfield hv hJ source hsource f j hj

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots.inventory_slots_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceSlots.inventory_slots_oai
