-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_injection_package
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:31:37.741042+00:00
-- url     : https://prove2.me/submissions/0be60334-2b88-43b9-a15b-a5b4dcf8396b

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralAssignmentLabel_ground_supported_hs
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralAssignmentLabel_pair_eq_iff
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralAssignmentLabel_subset_quotients

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameOrbitBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mem_symmetric_values (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (H : Set P) (x : ZFSet.{u}) :
    x ∈ (a.symmetricDomain s D F).values H ↔
      ∃ τ ∈ D.names, HereditarilySymmetric a s F τ ∧ Name.eval H τ = x := by
  rw [Name.NameDomain.mem_values]
  constructor
  · rintro ⟨τ, ⟨hτ, hs⟩, eq⟩
    exact ⟨τ, hτ, hs, eq⟩
  · rintro ⟨τ, hτ, hs, eq⟩
    exact ⟨τ, ⟨hτ, hs⟩, eq⟩

end PartitionPilot.Forcing.PosetAction


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProjectedRowChooserWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable (s : Presentation P) {G : Type v} [Group G]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

theorem mem_symmetricExtension (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ (M.symmetricExtension s a F H).sets ↔
      ∃ τ ∈ (M.nameDomain s).names, HereditarilySymmetric a s F τ ∧
        Name.eval {q | H.mem q} τ = x :=
  a.mem_symmetric_values s (M.nameDomain s) F {q | H.mem q} x

end PartitionPilot.Forcing.TransitiveGround


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAssignmentLabelInjectionPackages
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

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace member
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "inc" => RecursiveRefinementOrderHistory.inclusionFunction run ordinal cutOrdinal subset
  pairing unions powers separation infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono

theorem semanticStructuralAssignmentLabel_injection_package_oai :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      (run).carriers ordinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let upper := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices lowerAct lower b d alpha T T2 valid →
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
      let label := Name.refinementAssignmentLabel upper inc ⊤ T valid
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) Rf Rc
      let J := Name.eval {p | H.mem p} label
      let B := Name.eval {q | H.mem (inc q)} (Name.refinementQuotient T valid U.val Rc.val)
      let A := Name.eval {q | H.mem (inc q)} (Name.refinementQuotient T valid U.val Rf.val)
      (∀ x ∈ B, ∃ y, ZFSet.pair x y ∈ J) →
      InjectionCode B A J ∧
        J ∈ (M.symmetricExtension upper upperAct (d.principalSupportFamily base directed) H).sets := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  let upper := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  dsimp only
  intro C E U Rf Rc index H ordinary total
  have shape := M.semanticStructuralAssignmentLabel_subset_quotients c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice C E U Rf Rc index H
  have equal := M.semanticStructuralAssignmentLabel_pair_eq_iff c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice C E U Rf Rc index H ordinary
  have nameFacts := M.semanticStructuralAssignmentLabel_ground_supported_hs c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice C E U Rf Rc index
  refine ⟨⟨⟨shape, ?_⟩, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, entry⟩ := total x hx
    refine ⟨y, entry, ?_⟩
    intro z other
    exact (equal x z x y other entry).1 rfl
  · intro x y z first second
    exact (equal x z y z first second).2 rfl
  · exact (M.mem_symmetricExtension upper upperAct (d.principalSupportFamily base directed) H _).2
      ⟨_, nameFacts.1, nameFacts.2.2, rfl⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_injection_package_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_injection_package_oai.{u}
