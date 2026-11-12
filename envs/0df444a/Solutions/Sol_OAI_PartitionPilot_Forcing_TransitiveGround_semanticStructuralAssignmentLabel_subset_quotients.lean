-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_subset_quotients
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:33:08.600497+00:00
-- url     : https://prove2.me/submissions/84b81b07-4053-41a3-9a33-fa4fa4315299

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_assignment_tests

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u v
variable {P Q R : Type u} {s : Presentation P}

theorem eval_rename (t : Presentation Q) (f : P → Q) (H : Set Q) (τ : Name s) :
    eval H (rename t f τ) = eval {p | f p ∈ H} τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ZFSet.ext
    intro x
    rw [mem_eval, mem_eval]
    constructor
    · rintro ⟨ν, q, h, hq, eq⟩
      obtain ⟨σ, p, hp, rfl, rfl⟩ := (entry_rename t f τ ν q).1 h
      exact ⟨σ, p, hp, hq, (ih σ p hp).symm.trans eq⟩
    · rintro ⟨σ, p, hp, hq, eq⟩
      exact ⟨rename t f σ, f p,
        (entry_rename t f τ _ _).2 ⟨σ, p, hp, rfl, rfl⟩,
        hq, (ih σ p hp).trans eq⟩

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompleteProjectionPredensity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section
universe u v
variable {Upper : Type u} {Lower : Type v} [PartialOrder Upper] [PartialOrder Lower]

namespace CompleteProjection
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
include projection

theorem projectedFilter_mem_iff (H : ConditionFilter Upper) (q : Lower) :
    (projection.projectedFilter H).mem q ↔
      ∃ p : Upper, H.mem p ∧ restriction p = q := by
  constructor
  · intro member
    exact ⟨inclusion q, member, projection.retract q⟩
  · rintro ⟨p, member, rfl⟩
    exact H.upward member (projection.le_include_restriction p)

end CompleteProjection
end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementAssignmentLabelNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} [PartialOrder P] [OrderTop P]
variable {s : Presentation P} (upper : Presentation Q) (incl : P → Q) (one : Q)

theorem entry_refinementAssignmentLabel (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (Rf Rc : Name s)
    (sigma : Name upper) (p : Q) :
    Entry sigma (refinementAssignmentLabel upper incl one T valid idx Rf Rc) p ↔
      ∃ v w : Name s, v.val ∈ T ∧ w.val ∈ T ∧
        (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A) ∧
        orderedPair one (rename upper incl (refinementClass T valid Rc v))
          (rename upper incl (refinementClass T valid Rf w)) = sigma := by
  rw [refinementAssignmentLabel, entry_assemble]
  constructor
  · rintro ⟨a, equal, condition⟩
    refine ⟨⟨a.val.1.1.val, valid _ a.val.1.1.property⟩,
      ⟨a.val.1.2.val, valid _ a.val.1.2.property⟩,
      a.val.1.1.property, a.val.1.2.property, ?_, equal⟩
    exact condition ▸ a.property
  · rintro ⟨v, w, hv, hw, literal, equal⟩
    exact ⟨⟨((⟨v.val, hv⟩, ⟨w.val, hw⟩), p), literal⟩, equal, rfl⟩

theorem mem_eval_refinementAssignmentLabel (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (Rf Rc : Name s)
    (H : Set Q) (hone : one ∈ H) (z : ZFSet.{u}) :
    z ∈ eval H (refinementAssignmentLabel upper incl one T valid idx Rf Rc) ↔
      ∃ (p : Q) (v w : Name s), p ∈ H ∧ v.val ∈ T ∧ w.val ∈ T ∧
        (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A) ∧
        ZFSet.pair (eval {q | incl q ∈ H} (refinementClass T valid Rc v))
          (eval {q | incl q ∈ H} (refinementClass T valid Rf w)) = z := by
  rw [mem_eval]
  constructor
  · rintro ⟨sigma, p, entry, hp, equal⟩
    obtain ⟨v, w, hv, hw, literal, rfl⟩ :=
      (entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc sigma p).1 entry
    refine ⟨p, v, w, hp, hv, hw, literal, ?_⟩
    simpa only [eval_orderedPair H one hone, eval_rename] using equal
  · rintro ⟨p, v, w, hp, hv, hw, literal, equal⟩
    refine ⟨_, p, (entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc _ p).2
      ⟨v, w, hv, hw, literal, rfl⟩, hp, ?_⟩
    simpa only [eval_orderedPair H one hone, eval_rename] using equal

end PartitionPilot.Forcing.Name

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAssignmentLabelCanonicalSuccessors
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

theorem semanticStructuralAssignmentLabel_subset_quotients_oai :
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
      let label := Name.refinementAssignmentLabel upper inc ⊤ T valid
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) Rf Rc
      Name.eval {p | H.mem p} label ⊆ ZFSet.prod
        (Name.eval {q | H.mem (inc q)} (Name.refinementQuotient T valid U.val Rc.val))
        (Name.eval {q | H.mem (inc q)} (Name.refinementQuotient T valid U.val Rf.val)) := by
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
  let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice
  dsimp only
  intro C E U Rf Rc index H z memberLabel
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  obtain ⟨p, v, w, hp, hv, hw, ⟨row, A, code, entry⟩, equal⟩ :=
    (Name.mem_eval_refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val
      {p | H.mem p} H.top_mem z).1 memberLabel
  let gv : (M.nameDomain lower).names := ⟨v, M.transitive hT hv⟩
  let gw : (M.nameDomain lower).names := ⟨w, M.transitive hT hw⟩
  have tests := M.semanticStructuralPrefix_assignment_tests c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member p row A code
  have active := ((tests C E U Rf Rc index).1 gv gw hv hw entry).1
  have projectedMember : (projection.projectedFilter H).mem
      ((run).restriction ordinal cutOrdinal subset c.conditionOrder_code p) :=
    (projection.projectedFilter_mem_iff H _).2 ⟨p, hp, rfl⟩
  rw [← equal]
  apply ZFSet.pair_mem_prod.2
  constructor
  · exact (Name.mem_eval _ _ _).2 ⟨_,
      (run).restriction ordinal cutOrdinal subset c.conditionOrder_code p,
      (Name.entry_refinementQuotient T valid U.val Rc.val _ _).2 ⟨v, hv, active.1, rfl⟩,
      projectedMember, rfl⟩
  · exact (Name.mem_eval _ _ _).2 ⟨_,
      (run).restriction ordinal cutOrdinal subset c.conditionOrder_code p,
      (Name.entry_refinementQuotient T valid U.val Rf.val _ _).2 ⟨w, hw, active.2, rfl⟩,
      projectedMember, rfl⟩

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_subset_quotients_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_subset_quotients_oai.{u}
