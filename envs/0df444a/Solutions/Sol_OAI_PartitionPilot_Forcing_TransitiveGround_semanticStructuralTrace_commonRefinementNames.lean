-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonRefinementNames
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:36:54.485033+00:00
-- url     : https://prove2.me/submissions/19bad6d2-8c73-4c8a-aa58-278011559b19

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P011
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralCrossStagePower_hs
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefixMembershipName_eval
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefixRefinementNormalization
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralTrace_commonPowerAntichains

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_EvaluatedDomains
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace Name

open SetRealization
universe u v
variable {P : Type u} {s : Presentation P}

theorem mem_eval_assemble (H : Set P) {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) (x : ZFSet.{u}) :
    x ∈ eval H (assemble names conditions) ↔
      ∃ i, conditions i ∈ H ∧ eval H (names i) = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨i, rfl, rfl⟩ := (entry_assemble names conditions σ p).1 entry
    exact ⟨i, hp, eq⟩
  · rintro ⟨i, hp, eq⟩
    exact ⟨names i, conditions i,
      (entry_assemble names conditions _ _).2 ⟨i, rfl, rfl⟩, hp, eq⟩

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem eval_singleton (H : Set P) (one : P) (hone : one ∈ H) (σ : Name s) :
    eval H (singleton one σ) = {eval H σ} := by
  apply ZFSet.ext
  intro x
  rw [singleton, mem_eval_assemble, ZFSet.mem_singleton]
  constructor
  · rintro ⟨_, _, eq⟩
    exact eq.symm
  · intro eq
    exact ⟨(), hone, eq.symm⟩

theorem eval_unorderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (unorderedPair one σ τ) = {eval H σ, eval H τ} := by
  apply ZFSet.ext
  intro x
  rw [unorderedPair, mem_eval_assemble, ZFSet.mem_pair]
  constructor
  · rintro ⟨b, _, eq⟩
    cases b with
    | false => exact Or.inr eq.symm
    | true => exact Or.inl eq.symm
  · rintro (eq | eq)
    · exact ⟨true, hone, eq.symm⟩
    · exact ⟨false, hone, eq.symm⟩

theorem eval_orderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (orderedPair one σ τ) = ZFSet.pair (eval H σ) (eval H τ) := by
  rw [orderedPair, eval_unorderedPair H one hone,
    eval_singleton H one hone, eval_unorderedPair H one hone]
  rfl

end Name



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_PairFamilyEvaluation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem eval_familySet_orderedPairNameFamily (H : Set P) (one : P) (hone : one ∈ H)
    (X Y : ZFSet.{u}) (validX : ∀ z ∈ X, IsName s z)
    (validY : ∀ z ∈ Y, IsName s z)
    (validPair : ∀ z ∈ orderedPairNameFamily (s.encode one) X Y, IsName s z) :
    eval H (familySet one (orderedPairNameFamily (s.encode one) X Y) validPair) =
      ZFSet.prod (eval H (familySet one X validX)) (eval H (familySet one Y validY)) := by
  apply ZFSet.ext
  intro z
  rw [mem_eval_familySet H one hone, ZFSet.mem_prod]
  constructor
  · rintro ⟨tau, member, value⟩
    obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y tau.val).1 member
    let sigma : Name s := ⟨x, validX x hx⟩
    let nu : Name s := ⟨y, validY y hy⟩
    have same : tau = orderedPair one sigma nu :=
      Subtype.ext (equal.trans (orderedPair_code one sigma nu).symm)
    refine ⟨eval H sigma, (mem_eval_familySet H one hone X validX _).2 ⟨sigma, hx, rfl⟩,
      eval H nu, (mem_eval_familySet H one hone Y validY _).2 ⟨nu, hy, rfl⟩, ?_⟩
    rw [same, eval_orderedPair H one hone] at value
    exact value.symm
  · rintro ⟨x, hx, y, hy, equal⟩
    obtain ⟨sigma, memberX, valueX⟩ := (mem_eval_familySet H one hone X validX x).1 hx
    obtain ⟨nu, memberY, valueY⟩ := (mem_eval_familySet H one hone Y validY y).1 hy
    refine ⟨orderedPair one sigma nu, ?_, ?_⟩
    · exact (mem_orderedPairNameFamily _ X Y _).2
        ⟨sigma.val, memberX, nu.val, memberY, orderedPair_code one sigma nu⟩
    · rw [eval_orderedPair H one hone, valueX, valueY]
      exact equal.symm

theorem refinementValidity_familySet_power_bounds (H : Set P) (one : P) (hone : one ∈ H)
    (oneCode T : ZFSet.{u}) (sameCode : oneCode = s.encode one)
    (valid : ∀ z ∈ T, IsName s z)
    (validPower : ∀ i : Fin 3, ∀ z ∈ iteratedPairNameFamily oneCode T (![0, 1, 1] i),
      IsName s z)
    (values : Fin 3 → ZFSet.{u})
    (raw : RefinementValidityCode (eval H (familySet one T valid))
      (values 0) (values 1) (values 2)) :
    ∀ i : Fin 3, values i ⊆
      eval H (familySet one (iteratedPairNameFamily oneCode T (![0, 1, 1] i)) (validPower i)) := by
  subst oneCode
  have relationBound (R : ZFSet.{u}) (shape : R ⊆ ZFSet.prod (values 0) (values 0)) :
      R ⊆ eval H (familySet one (orderedPairNameFamily (s.encode one) T T)
        (orderedPairNameFamily_valid one valid valid)) := by
    rw [eval_familySet_orderedPairNameFamily H one hone T T valid valid]
    intro z member
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 (shape member)
    exact ZFSet.mem_prod.2 ⟨x, raw.1 hx, y, raw.1 hy, equal⟩
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))
  · exact raw.1
  · exact relationBound (values 1) raw.2.1.shape
  · exact relationBound (values 2) raw.2.2.1.shape

end PartitionPilot.Forcing.Name

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralFinalRefinements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

theorem semanticStructuralTrace_commonEarlierPowerNames :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    ∀ count (degrees : Fin count → Nat)
      (tau : Fin count → (M.nameDomain (SetMembers.presentation Q)).names),
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ i,
      let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := (M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation carrier hT valid1 topMem (And.left (And.left standard)) trace (degrees i)).2 beta cutOrdinal subset
      let N := Name.crossStageMembershipName (SetMembers.presentation Q) lower inc J valid (tau i).val
      N.val ∈ M.sets ∧
      (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
        C ≤ (upperAct).stabilizer (SetMembers.presentation Q) (tau i).val →
        NiceNameCode lowerAct lower J C N.val ∧
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed) N) ∧
      ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (formulaFamily (M.nameDomain (SetMembers.presentation Q))) →
        (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
        Name.eval {p | (projection.projectedFilter H).mem p} N =
          Name.eval {p | H.mem p} (tau i).val ∩
            Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ J valid) ∧
        (Name.eval {p | H.mem p} (tau i).val ⊆
          Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ J valid) →
          Name.eval {p | (projection.projectedFilter H).mem p} N = Name.eval {p | H.mem p} (tau i).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  intro count degrees tau
  obtain ⟨beta, hBeta, f, family⟩ := M.semanticStructuralTrace_commonPowerAntichains
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT count degrees tau
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  refine ⟨beta, hBeta, ?_⟩
  dsimp only
  intro i
  have evaluation := M.semanticStructuralPrefixMembershipName_eval c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset infinite choice (degrees i) (tau i) (f i) (family i).2.1
    (fun sigma A entry => ⟨((family i).2.2.1 sigma A entry).1.1, (family i).2.2.2 sigma A entry⟩)
  refine ⟨evaluation.1, ?_, ?_⟩
  · intro C member supported
    obtain ⟨_, _, nice, symmetric⟩ := M.semanticStructuralCrossStagePower_hs
      c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset infinite choice (degrees i) C member (tau i).val supported
    exact ⟨nice, symmetric⟩
  · intro H upperGeneric lowerGeneric
    have equal := evaluation.2 H upperGeneric lowerGeneric
    refine ⟨equal, ?_⟩
    intro valueSubset
    rw [equal]
    apply ZFSet.ext
    intro x
    exact ⟨fun member => (ZFSet.mem_inter.1 member).1,
      fun member => ZFSet.mem_inter.2 ⟨member, valueSubset member⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_commonRefinementNames_oai (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ T validT))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          ∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  intro tau
  let degrees : Fin 3 → Nat := ![0, 1, 1]
  obtain ⟨beta, hBeta, representations⟩ := M.semanticStructuralTrace_commonEarlierPowerNames
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT 3 degrees tau
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
  let validT := (termData 0).2 beta cutOrdinal subset
  let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
  let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
  let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
    beta hAlpha cutOrdinal subset infinite choice
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported, unchanged⟩ :=
    M.semanticStructuralPrefixRefinementNormalization c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset infinite choice
      small degrees tau
  refine ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported, ?_⟩
  intro H upperGeneric lowerCoded lowerGeneric originalValid i
  have topCode : lower.encode ⊤ = ZFSet.pair rowTop ∅ :=
    M.refinementHistoryDecodedTop_eq c.conditionOrder_code T beta (graphRestriction beta packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  have bounds : ∀ j : Fin 3, Name.eval {p | H.mem p} (tau j).val ⊆
      Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ (J j) (valid j)) := by
    exact Name.refinementValidity_familySet_power_bounds
      {p | (projection.projectedFilter H).mem p} ⊤ (projection.projectedFilter H).top_mem
      (ZFSet.pair rowTop ∅) T topCode.symm validT valid
      (fun j => Name.eval {p | H.mem p} (tau j).val) originalValid
  have oldEqual (j : Fin 3) :
      Name.eval {p | (projection.projectedFilter H).mem p} (env j.castSucc).val =
        Name.eval {p | H.mem p} (tau j).val := by
    rw [names j]
    exact ((representations j).2.2 H upperGeneric lowerCoded).2 (bounds j)
  have oldValid : RefinementValidityCode
      (Name.eval {p | (projection.projectedFilter H).mem p} (env 3).val)
      (Name.eval {p | (projection.projectedFilter H).mem p} (env 0).val)
      (Name.eval {p | (projection.projectedFilter H).mem p} (env 1).val)
      (Name.eval {p | (projection.projectedFilter H).mem p} (env 2).val) := by
    have zero := oldEqual 0
    have one := oldEqual 1
    have two := oldEqual 2
    change Name.eval _ (env 0).val = _ at zero
    change Name.eval _ (env 1).val = _ at one
    change Name.eval _ (env 2).val = _ at two
    rw [last, zero, one, two]
    exact originalValid
  exact (unchanged (projection.projectedFilter H) lowerGeneric oldValid i).trans (oldEqual i)

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonRefinementNames_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_commonRefinementNames_oai.{u}
