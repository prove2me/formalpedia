-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundStoredPreparedStrengthening
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:32:58.598001+00:00
-- url     : https://prove2.me/submissions/b904d53b-861d-4661-8d21-550b97202348

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_exists_groundFairPreparationOrbit

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_DecodedFunctionGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u}) {A B : Type u}

theorem decoded_function_graph_mem (s : Presentation A) (t : Presentation B) {f : ZFSet.{u}}
    (hf : f ∈ M.sets) (h : ZFSet.IsFunc s.carrier t.carrier f) :
    s.graph t (s.decodeFunction t f h) ∈ M.sets := by
  rw [s.graph_decodeFunction]
  exact hf

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundContainmentOrders
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem decoded_order_mem {Q R : ZFSet.{u}} (h : PartialOrderCode Q R) (hR : R ∈ M.sets) :
    letI _decodedOrder := h.toPartialOrder
    (SetMembers.presentation Q).conditionOrder ∈ M.sets := by
  let decodedOrder := h.toPartialOrder
  rw [h.conditionOrder_eq]
  exact hR

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRepresentedDomainConditions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order

theorem stageOneRawForces_condition_mono {n : Nat} (phi : SetFormula n)
    (names : Assignment (M.nameDomain s) n) {p q : P} (qp : q ≤ p)
    (forced : stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi
      (fun j => (names j).val.val)) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi
      (fun j => (names j).val.val) := by
  apply (M.stageOneRawForces_iff s pairing unions powers separation collection
    carrier order phi q names).2
  exact forces_mono (M.nameDomain s) phi names
    ((M.stageOneRawForces_iff s pairing unions powers separation collection
      carrier order phi p names).1 forced) qp

private theorem rawForces_pair_condition_mono
    (phi : SetFormula 2) (z tau : (M.nameDomain s).names) {p q : P} (qp : q ≤ p)
    (forced : stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi
      ![z.val.val, tau.val.val]) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi
      ![z.val.val, tau.val.val] := by
  have fields : (fun j : Fin 2 => (![z, tau] j).val.val) =
      ![z.val.val, tau.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  have moved := M.stageOneRawForces_condition_mono s pairing unions powers separation
    collection carrier order phi ![z, tau] qp
  rw [fields] at moved
  exact moved forced

theorem preparationForcingCode_condition_mono
    (nodes N visibility : ZFSet.{u})
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes → IsName s V)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F f : ZFSet.{u})
    (range : f ⊆ ZFSet.prod nodes N) {p q : P} (qp : q ≤ p)
    (code : PreparationForcingCode M s.carrier s.conditionOrder (s.encode p)
      nodes visibility z.val.val F f) :
    PreparationForcingCode M s.carrier s.conditionOrder (s.encode q)
      nodes visibility z.val.val F f := by
  constructor
  · intro v V entry member
    let name : (M.nameDomain s).names :=
      ⟨⟨V, graphNames v V entry member⟩, M.pair_right (M.transitive graphGround entry)⟩
    have decisions := code.1 v V entry member
    exact ⟨fun yes => rawForces_pair_condition_mono M s pairing unions powers separation
      collection carrier order (.mem 0 1) z name qp (decisions.1 yes),
      fun no => rawForces_pair_condition_mono M s pairing unions powers separation
        collection carrier order (.neg (.mem 0 1)) z name qp (decisions.2 no)⟩
  · intro v tau entry
    have htau := (ZFSet.pair_mem_prod.1 (range entry)).2
    let name : (M.nameDomain s).names :=
      ⟨⟨tau, validN tau htau⟩, M.transitive namesGround htau⟩
    exact rawForces_pair_condition_mono M s pairing unions powers separation collection
      carrier order (.equal 0 1) z name qp (code.2 v tau entry)

end PartitionPilot.Forcing.TransitiveGround

end



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem mem_assignmentOnIndices (B T A z : ZFSet.{u}) :
    z ∈ assignmentOnIndices B T A ↔ z ∈ A ∧ z ∈ stageOneAssignments B T :=
  ZFSet.mem_sep

theorem assignmentOnIndices_entry (B T A t u w : ZFSet.{u}) :
    stageOneAssignment t u w ∈ assignmentOnIndices B T A ↔
      stageOneAssignment t u w ∈ A ∧ t ∈ B ∧ u ∈ T ∧ w ∈ T := by
  rw [mem_assignmentOnIndices, stageOneAssignment_mem_assignments]

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem storedPreparationRequests_mem {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (fields : Fin 15 → ZFSet.{u}) (members : ∀ j, fields j ∈ M.sets) :
    M.storedPreparationRequests A fields ∈ M.sets :=
  (M.definable_storedPreparationRequests pairing unions powers separation).closed
    (extend A fields) (Fin.cases hA members)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_FiniteFlatHistoryCoherence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
universe u

theorem mem_finiteStageHistory (values : Nat → ZFSet.{u}) (n : Nat) (z : ZFSet.{u}) :
    z ∈ finiteStageHistory values n ↔ ∃ i < n, z = ZFSet.pair (natSetCode i) (values i) := by
  induction n with
  | zero => simp [finiteStageHistory]
  | succ n ih =>
    rw [finiteStageHistory, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (equal | ⟨i, hi, equal⟩)
      · exact ⟨n, Nat.lt_succ_self n, equal⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, equal⟩
    · rintro ⟨i, hi, equal⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact Or.inr ⟨i, hi, equal⟩
      · exact Or.inl equal

theorem pair_mem_finiteStageHistory (values : Nat → ZFSet.{u}) (n i : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode i) y ∈ finiteStageHistory values n ↔ i < n ∧ y = values i := by
  rw [mem_finiteStageHistory]
  constructor
  · rintro ⟨j, hj, equal⟩
    obtain ⟨index, value⟩ := ZFSet.pair_inj.1 equal
    obtain rfl := natSetCode_injective index
    exact ⟨hj, value⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundVisibilitySupportIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem mem_visibilitySupportIncidence
    (nodes names visibility top z : ZFSet.{u}) :
    z ∈ visibilitySupportIncidence nodes names visibility top ↔
      ∃ v ∈ nodes, ∃ tau ∈ names, z = ZFSet.pair v tau ∧
        ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V := by
  rw [visibilitySupportIncidence, ZFSet.mem_sep]
  constructor
  · rintro ⟨bound, v, tau, rfl, V, entry, member⟩
    exact ⟨v, (ZFSet.pair_mem_prod.1 bound).1,
      tau, (ZFSet.pair_mem_prod.1 bound).2, rfl, V, entry, member⟩
  · rintro ⟨v, hv, tau, htau, rfl, V, entry, member⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, htau⟩, v, tau, rfl, V, entry, member⟩

theorem pair_mem_visibilitySupportIncidence
    (nodes names visibility top v tau : ZFSet.{u}) :
    ZFSet.pair v tau ∈ visibilitySupportIncidence nodes names visibility top ↔
      v ∈ nodes ∧ tau ∈ names ∧
        ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V := by
  rw [mem_visibilitySupportIncidence]
  constructor
  · rintro ⟨v', hv, tau', htau, equal, witness⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hv, htau, witness⟩
  · rintro ⟨hv, htau, witness⟩
    exact ⟨v, hv, tau, htau, rfl, witness⟩

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem supportedEqualityCertificateBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.supportedEqualityCertificateBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation (M.groundPower_mem powers hNodes)
    (M.prod_mem pairing unions powers separation
      (M.groundSmallSubsets_mem powers separation hNodes omega)
      (M.groundRelations_mem pairing unions powers separation hNodes hN))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem synchronizedEnumerationBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) : M.synchronizedEnumerationBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation
    (M.groundRelations_mem pairing unions powers separation omega hNodes)
    (M.groundRelations_mem pairing unions powers separation omega hN)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNicePreparationWitnessBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_preparationWitnessBound (nodes T Q r k enumerations : ZFSet.{u}) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q ↔
      r ∈ Q ∧ k ∈ M.groundRelations (M.groundRelations T Q)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q)) ∧
      enumerations ∈ M.groundRelations (M.groundRelations T Q)
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) := by
  simp only [preparationWitnessBound, ZFSet.pair_mem_prod]

theorem preparationWitnessBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes T Q : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.preparationWitnessBound nodes T Q ∈ M.sets := by
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  exact M.prod_mem pairing unions powers separation hQ
    (M.prod_mem pairing unions powers separation
      (M.groundRelations_mem pairing unions powers separation hW
        (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega))
      (M.groundRelations_mem pairing unions powers separation hW
        (M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega)))

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundVaryingPreparationRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationCode_pair_iff (packed Q upperOrder nodes T levels omega C E alpha p y : ZFSet.{u}) :
    M.VaryingPreparationCode packed Q upperOrder nodes T levels omega C E
      (ZFSet.pair (ZFSet.pair alpha p) y) ↔
    ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
        (canonicalMeetGraph (fields 10) (fields 11)) omega C E fields p y := by
  constructor
  · rintro ⟨alpha', p', y', fields, equal, rest⟩
    obtain ⟨input, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 input
    exact ⟨fields, rest⟩
  · rintro ⟨fields, rest⟩
    exact ⟨alpha, p, y, fields, rfl, rest⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_varyingPreparationRelation
    (stages packed Q upperOrder nodes T alpha p y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T ↔
    alpha ∈ stages ∧ p ∈ Q ∧ y ∈ M.preparationWitnessBound nodes T Q ∧
      ∃ fields : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
        fields 6 = T ∧ fields 10 = nodes ∧
        MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
        M.StoredPreparationCode upperOrder
          (rowAssignmentCutGraph Q (fields 7) (refinementDataHistoryLevels stages packed T) alpha)
          (canonicalMeetGraph (fields 10) (fields 11)) ZFSet.omega
          (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
          (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) fields p y := by
  simp only [varyingPreparationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod,
    M.varyingPreparationCode_pair_iff, and_assoc]

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RefinementBirthSchedules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace RefinementDataHistory
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
include valid

theorem birthList_assignment_visit (assignments enumerations : Nat → ZFSet.{u})
    (shape : ∀ i, assignments i ⊆ stageOneAssignments (refinementDataHistoryIndices stages history) T)
    (retained : ∀ i k, i ≤ k → assignments i ⊆ assignments k)
    (onto : ∀ i alpha,
      alpha ∈ relationImage (assignments i) stages (refinementDataHistoryLevels stages history T) →
      ∃ j : Nat, ZFSet.pair (natSetCode j) alpha ∈ enumerations i)
    {x : ZFSet.{u}} (member : x ∈ stageOneAssignmentUnion assignments) :
    ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
      Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
      x ∈ assignments i ∧
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
      ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages history T ∧
      alpha ∈ relationImage (assignments i) stages (refinementDataHistoryLevels stages history T) ∧
      ZFSet.pair (natSetCode j) alpha ∈ enumerations i ∧
      x ∈ assignmentOnIndices (fields 0) T (assignments (Nat.pair i j)) := by
  obtain ⟨i, born⟩ := (mem_stageOneAssignmentUnion assignments x).1 member
  obtain ⟨t, ht, first, hFirst, second, hSecond, rfl⟩ :=
    (mem_stageOneAssignments _ _ _).1 (shape i born)
  obtain ⟨alpha, hAlpha, fields, stored, index⟩ :=
    (mem_refinementDataHistoryIndices _ _ _).1 ht
  have terms := valid.terms alpha fields stored
  have level := valid.coverage alpha hAlpha fields stored t index
    first (terms.symm ▸ hFirst) second (terms.symm ▸ hSecond)
  have attained : alpha ∈ relationImage (assignments i) stages
      (refinementDataHistoryLevels stages history T) :=
    (mem_relationImage _ _ _ _).2 ⟨hAlpha, _, born, level⟩
  obtain ⟨j, scheduled⟩ := onto i alpha attained
  have before := Nat.left_le_pair i j
  exact ⟨i, j, alpha, hAlpha, fields, Nat.unpair_pair i j, before, born, stored,
    level, attained, scheduled,
    (assignmentOnIndices_entry _ _ _ _ _ _).2
      ⟨retained i (Nat.pair i j) before born, index, hFirst, hSecond⟩⟩

end RefinementDataHistory

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RefinementBirthEnumerationFairness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

theorem BirthLevelEnumerationCode.enumerates {omega stages A levels e : ZFSet.{u}}
    (code : BirthLevelEnumerationCode omega stages A levels e)
    (active : (relationImage A stages levels).Nonempty) :
    ZFSet.IsFunc omega (relationImage A stages levels) e ∧
      ∀ alpha ∈ relationImage A stages levels, ∃ n ∈ omega, ZFSet.pair n alpha ∈ e := by
  rcases code with ⟨empty, _⟩ | ⟨function, range⟩
  · obtain ⟨alpha, ha⟩ := active
    exact False.elim (ZFSet.notMem_empty alpha (empty ▸ ha))
  · refine ⟨⟨?_, function.2⟩, ?_⟩
    · intro z hz
      obtain ⟨n, hn, alpha, ha, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨hn,
        (mem_relationImage A stages levels alpha).2 ⟨ha, (range alpha ha).1 ⟨n, hn, hz⟩⟩⟩
    · intro alpha ha
      obtain ⟨hs, witness⟩ := (mem_relationImage A stages levels alpha).1 ha
      exact (range alpha hs).2 witness

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_birthLevelEnumerationRelation (Q stages levels row A e : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair row A) e ∈ M.birthLevelEnumerationRelation Q stages levels ↔
      ZFSet.pair row A ∈ Q ∧ e ∈ M.groundRelations ZFSet.omega stages ∧
        BirthLevelEnumerationCode ZFSet.omega stages A levels e := by
  rw [birthLevelEnumerationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hp, he⟩, row', A', e', equal, code⟩
    obtain ⟨pair, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 pair
    exact ⟨hp, he, code⟩
  · rintro ⟨hp, he, code⟩
    exact ⟨⟨hp, he⟩, row, A, e, rfl, code⟩

end TransitiveGround

namespace RefinementDataHistory
universe u
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
include valid

theorem birthEnumeration_assignment_visit (assignments enumerations : Nat → ZFSet.{u})
    (shape : ∀ i, assignments i ⊆ stageOneAssignments (refinementDataHistoryIndices stages history) T)
    (retained : ∀ i k, i ≤ k → assignments i ⊆ assignments k)
    (coded : ∀ i, BirthLevelEnumerationCode ZFSet.omega stages (assignments i)
      (refinementDataHistoryLevels stages history T) (enumerations i))
    {x : ZFSet.{u}} (member : x ∈ stageOneAssignmentUnion assignments) :
    ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
      Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
      x ∈ assignments i ∧
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
      ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages history T ∧
      alpha ∈ relationImage (assignments i) stages (refinementDataHistoryLevels stages history T) ∧
      ZFSet.pair (natSetCode j) alpha ∈ enumerations i ∧
      ∀ k, Nat.pair i j ≤ k → x ∈ assignmentOnIndices (fields 0) T (assignments k) := by
  have onto : ∀ i alpha,
      alpha ∈ relationImage (assignments i) stages (refinementDataHistoryLevels stages history T) →
      ∃ j : Nat, ZFSet.pair (natSetCode j) alpha ∈ enumerations i := by
    intro i alpha attained
    obtain ⟨n, hn, entry⟩ := ((coded i).enumerates ⟨alpha, attained⟩).2 alpha attained
    obtain ⟨j, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact ⟨j, entry⟩
  obtain ⟨i, j, alpha, hAlpha, fields, scheduled, before, born, stored,
      level, attained, enumeration, visited⟩ :=
    valid.birthList_assignment_visit assignments enumerations shape retained onto member
  refine ⟨i, j, alpha, hAlpha, fields, scheduled, before, born, stored,
    level, attained, enumeration, ?_⟩
  intro k after
  have parts := (mem_assignmentOnIndices _ _ _ _).1 visited
  exact (mem_assignmentOnIndices _ _ _ _).2
    ⟨retained (Nat.pair i j) k after parts.1, parts.2⟩

end RefinementDataHistory

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFairPreparationMonotonicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_fairPreparationStates (Q stages U E0 enumSelector state : ZFSet.{u}) :
    state ∈ M.fairPreparationStates Q stages U E0 enumSelector ↔
      state ∈ ZFSet.prod ZFSet.omega (ZFSet.prod Q
        (ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U)))) ∧
      FairPreparationStateCode ZFSet.omega E0 enumSelector state := ZFSet.mem_sep

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationRelation_strengthens
    (stages packed Q upperOrder nodes T alpha p r payload : ZFSet.{u})
    (entry : ZFSet.pair (ZFSet.pair alpha p) (ZFSet.pair r payload) ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T) :
    ZFSet.pair r p ∈ upperOrder := by
  obtain ⟨_, _, _, fields, _, _, _, _, code⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed Q upperOrder nodes T
      alpha p (ZFSet.pair r payload)).1 entry
  obtain ⟨_row, _A, r', _k, _enumerations, _q, _input, output, below, _rest⟩ := code
  obtain ⟨rfl, _⟩ := ZFSet.pair_inj.1 output
  exact below

theorem fairPreparationStep_strengthens
    (omega E0 stages U enumSelector prepSelector gridGraph packed Q upperOrder nodes T : ZFSet.{u})
    (selected : prepSelector ⊆ M.varyingPreparationRelation stages packed Q upperOrder nodes T)
    (n p births last m q nextBirths event : ZFSet.{u})
    (reflexive : ZFSet.pair p p ∈ upperOrder)
    (step : FairPreparationStepCode omega E0 stages U enumSelector prepSelector gridGraph
      (ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)))
      (ZFSet.pair m (ZFSet.pair q (ZFSet.pair nextBirths event)))) :
    ZFSet.pair q p ∈ upperOrder := by
  obtain ⟨n', p', births', last', m', q', nextBirths', event', first, second,
    _clock, _i, _hi, _j, _hj, _e, _he, _newE, _hNewE, _grid, _lookup,
    _newLookup, _append, action⟩ := step
  have oldCondition : p = p' := (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 first).2).1
  have newCondition : q = q' := (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 second).2).1
  rw [oldCondition, newCondition]
  rcases action with idle | ⟨alpha, _, y, _, ⟨payload, equal⟩, _, chosen, _⟩
  · rw [idle.2.1, ← oldCondition]
    exact reflexive
  · exact M.varyingPreparationRelation_strengthens stages packed Q upperOrder nodes T
      alpha p' q' payload (equal ▸ selected chosen)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFairPreparationConditionSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem fairPreparationConditionGraph_function
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit) :
    ZFSet.IsFunc ZFSet.omega Q (M.fairPreparationConditionGraph Q stages U E0 orbit) := by
  let tail := ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U))
  let middle := ZFSet.prod Q tail
  have widened : ZFSet.IsFunc ZFSet.omega (ZFSet.prod ZFSet.omega middle) orbit := by
    refine ⟨?_, function.2⟩
    intro z member
    obtain ⟨i, hi, state, hs, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hi, ((M.mem_fairPreparationStates _ _ _ _ _ _).1 hs).1⟩
  exact relationCompose_function_of_subset
    (relationCompose_function_of_subset widened
      (productSecond_function ZFSet.omega middle) (fun _ h => h))
    (productFirst_function Q tail) (fun _ h => h)

theorem pair_mem_fairPreparationConditionGraph
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (i p : ZFSet.{u}) :
    ZFSet.pair i p ∈ M.fairPreparationConditionGraph Q stages U E0 orbit ↔
      ∃ clock births event,
        ZFSet.pair i (ZFSet.pair clock (ZFSet.pair p (ZFSet.pair births event))) ∈ orbit := by
  dsimp only [fairPreparationConditionGraph]
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, middle, _, first, second⟩
    obtain ⟨_, _, state, _, edge, projected⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨p', hp', tail, ht, eq⟩ := (mem_productFirst _ _ _).1 second
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨clock, hc, rest, hr, eq⟩ := (mem_productSecond _ _ _).1 projected
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨births, hb, event, he, rfl⟩ := ZFSet.mem_prod.1 ht
    exact ⟨clock, births, event, edge⟩
  · rintro ⟨clock, births, event, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have stateBound := ((M.mem_fairPreparationStates _ _ _ _ _ _).1 bounds.2).1
    have split := ZFSet.pair_mem_prod.1 stateBound
    have rest := ZFSet.pair_mem_prod.1 split.2
    refine ⟨bounds.1, rest.1, _, split.2, ?_, ?_⟩
    · exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨bounds.1, split.2, _, stateBound, edge,
          (mem_productSecond _ _ _).2 ⟨clock, split.1, _, split.2, rfl⟩⟩
    · exact (mem_productFirst _ _ _).2 ⟨p, rest.1, _, rest.2, rfl⟩

theorem fairPreparationConditionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages U E0 orbit : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (whole : orbit ∈ M.sets) :
    M.fairPreparationConditionGraph Q stages U E0 orbit ∈ M.sets := by
  have hTail := M.prod_mem pairing unions powers separation
    (M.groundRelations_mem pairing unions powers separation omega hE0)
    (M.insert_mem pairing unions (M.empty_mem ⟨Q, hQ⟩)
      (M.prod_mem pairing unions powers separation hStages hU))
  have hMiddle := M.prod_mem pairing unions powers separation hQ hTail
  exact M.relationCompose_mem pairing unions powers separation omega hMiddle hQ
    (M.relationCompose_mem pairing unions powers separation omega
      (M.prod_mem pairing unions powers separation omega hMiddle) hMiddle whole
      (M.productSecond_mem pairing unions powers separation omega hMiddle))
    (M.productFirst_mem pairing unions powers separation hQ hTail)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem fairPreparationOrbit_conditionSequence
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages U E0 enumSelector prepSelector grid packed nodes T orbit : ZFSet.{u}}
    (hQ : s.carrier ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (whole : orbit ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates s.carrier stages U E0 enumSelector) orbit)
    (selected : prepSelector ⊆
      M.varyingPreparationRelation stages packed s.carrier s.conditionOrder nodes T)
    (p : P) (e : ZFSet.{u})
    (initial : ∀ state, ZFSet.pair ∅ state ∈ orbit ↔
      state = ZFSet.pair ∅ (ZFSet.pair (s.encode p) (ZFSet.pair {ZFSet.pair ∅ e} ∅)))
    (steps : ∀ n ∈ ZFSet.omega, ∀ state next,
      ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
      FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector grid state next) :
    ∃ seq : Nat → P, seq 0 = p ∧
      natPresentation.graph s (fun n => seq n.down) ∈ M.sets ∧ Antitone seq ∧
      ∃ clocks births events : Nat → ZFSet.{u},
        clocks 0 = ∅ ∧ births 0 = {ZFSet.pair ∅ e} ∧ events 0 = ∅ ∧
        (∀ k, ZFSet.pair (natSetCode k)
          (ZFSet.pair (clocks k) (ZFSet.pair (s.encode (seq k))
            (ZFSet.pair (births k) (events k)))) ∈ orbit) ∧
        ∀ k, FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector grid
          (ZFSet.pair (clocks k) (ZFSet.pair (s.encode (seq k)) (ZFSet.pair (births k) (events k))))
          (ZFSet.pair (clocks (k + 1))
            (ZFSet.pair (s.encode (seq (k + 1))) (ZFSet.pair (births (k + 1)) (events (k + 1))))) := by
  let graph := M.fairPreparationConditionGraph s.carrier stages U E0 orbit
  have graphGround : graph ∈ M.sets :=
    M.fairPreparationConditionGraph_mem pairing unions powers separation hQ hStages hU hE0 omega whole
  have graphFunction : ZFSet.IsFunc ZFSet.omega s.carrier graph :=
    M.fairPreparationConditionGraph_function function
  let seq : Nat → P := fun n => natPresentation.decodeFunction s graph graphFunction ⟨n⟩
  have represented (k : Nat) : ∃ clock births event,
      ZFSet.pair (natSetCode k)
        (ZFSet.pair clock (ZFSet.pair (s.encode (seq k)) (ZFSet.pair births event))) ∈ orbit :=
    (M.pair_mem_fairPreparationConditionGraph function _ _).1
      (natPresentation.decodeFunction_mem s graph graphFunction ⟨k⟩)
  choose clocks births events entries using represented
  have atZero := (initial _).1 (entries 0)
  have zeroClock := (ZFSet.pair_inj.1 atZero).1
  have zeroCondition := (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 atZero).2).1
  have zeroTail := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 atZero).2).2
  have rawSteps (k : Nat) := steps (natSetCode k) (natSetCode_mem_omega k)
    _ _ (entries k) (entries (k + 1))
  have decreasing : Antitone seq := by
    apply antitone_nat_of_succ_le
    intro k
    apply (s.pair_mem_conditionOrder _ _).1
    exact M.fairPreparationStep_strengthens ZFSet.omega E0 stages U enumSelector prepSelector
      grid packed s.carrier s.conditionOrder nodes T selected
      (clocks k) (s.encode (seq k)) (births k) (events k)
      (clocks (k + 1)) (s.encode (seq (k + 1))) (births (k + 1)) (events (k + 1))
      ((s.pair_mem_conditionOrder _ _).2 le_rfl) (rawSteps k)
  exact ⟨seq, s.injective zeroCondition,
    M.decoded_function_graph_mem natPresentation s graphGround graphFunction, decreasing,
    clocks, births, events, zeroClock, zeroTail.1, zeroTail.2, entries, rawSteps⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRefinementBinaryUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
universe u

namespace RecursiveRefinementDataHistory
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}

theorem cut_order (run : RecursiveRefinementDataHistory M rows T stages history)
    {q A p D beta : ZFSet.{u}}
    (below : ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈
      M.refinementHistoryOrder rows rowOrder T stages history) (hbeta : beta ∈ stages) :
    ZFSet.pair (ZFSet.pair q (assignmentCut (refinementDataHistoryLevels stages history T) beta A))
      (ZFSet.pair p (assignmentCut (refinementDataHistoryLevels stages history T) beta D)) ∈
      M.refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history) := by
  obtain ⟨hq, hp, rowsBelow, data⟩ := (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history q A p D).1 below
  exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history) _ _ _ _).2
    ⟨run.cut_mem hq hbeta, run.cut_mem hp hbeta, rowsBelow, assignmentCut_mono data⟩

end RecursiveRefinementDataHistory
namespace RecursiveRefinementOrderHistory
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
include run

theorem lower_order {q A p D beta : ZFSet.{u}} (d : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
    (below : ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈
      M.refinementHistoryOrder rows rowOrder T stages history) :
    ZFSet.pair (ZFSet.pair q (assignmentCut (refinementDataHistoryLevels stages history T) beta A))
      (ZFSet.pair p (assignmentCut (refinementDataHistoryLevels stages history T) beta D)) ∈ d 8 :=
  (run.order beta d entry).symm ▸ run.carriers.cut_order below (run.carriers.data.function.pair_source entry)

end RecursiveRefinementOrderHistory





end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_FairPreparationBirthPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem fairPreparation_birthPersistence
    {Q E0 stages U enumSelector prepSelector gridGraph : ZFSet.{u}}
    (function : ZFSet.IsFunc Q E0 enumSelector)
    (clocks conditions births events enumerations : Nat → ZFSet.{u})
    (chosen : ∀ k, ZFSet.pair (conditions k) (enumerations k) ∈ enumSelector)
    (initialClock : clocks 0 = ∅)
    (initialBirths : births 0 = {ZFSet.pair ∅ (enumerations 0)})
    (steps : ∀ k, FairPreparationStepCode ZFSet.omega E0 stages U
      enumSelector prepSelector gridGraph
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k))))
      (ZFSet.pair (clocks (k + 1))
        (ZFSet.pair (conditions (k + 1)) (ZFSet.pair (births (k + 1)) (events (k + 1)))))) :
    ∀ k, clocks k = natSetCode k ∧ births k = finiteStageHistory enumerations (k + 1) ∧
      (∀ i y, ZFSet.pair (natSetCode i) y ∈ births k ↔ i ≤ k ∧ y = enumerations i) ∧
      ∀ y, ZFSet.pair (natSetCode (Nat.unpair k).1) y ∈ births k ↔
        y = enumerations (Nat.unpair k).1 := by
  have successor (k : Nat) : clocks (k + 1) = insert (clocks k) (clocks k) ∧
      births (k + 1) = insert (ZFSet.pair (clocks (k + 1)) (enumerations (k + 1))) (births k) := by
    obtain ⟨n, p, b, last, m, q, nextBirths, event, source, target, next,
      i, _hi, j, _hj, e, _he, newE, _hNew, _grid, _old, selected, append, _branch⟩ := steps k
    obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 source
    obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 target
    obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    have hp := (ZFSet.pair_mem_prod.1 (function.1 (chosen (k + 1)))).1
    obtain ⟨_, _, unique⟩ := function.2 _ hp
    have same := (unique newE selected).trans (unique _ (chosen (k + 1))).symm
    exact ⟨next, same ▸ append⟩
  have exactHistory : ∀ k, clocks k = natSetCode k ∧ births k = finiteStageHistory enumerations (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨initialClock, ?_⟩
      exact initialBirths
    | succ k ih =>
      have next := successor k
      have clock : clocks (k + 1) = natSetCode (k + 1) := by
        rw [next.1, ih.1, natSetCode_succ]
      exact ⟨clock, by rw [next.2, clock, ih.2]; rfl⟩
  intro k
  have facts := exactHistory k
  have lookup (i : Nat) (y : ZFSet.{u}) :
      ZFSet.pair (natSetCode i) y ∈ births k ↔ i ≤ k ∧ y = enumerations i := by
    rw [facts.2, pair_mem_finiteStageHistory, Nat.lt_succ_iff]
  exact ⟨facts.1, facts.2, lookup, fun y => (lookup _ y).trans
    ⟨And.right, fun equal => ⟨Nat.unpair_left_le k, equal⟩⟩⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFairRefinementAssignmentVisits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem fairPreparation_scheduledActiveEvent
    {Q E0 stages U enumSelector prepSelector : ZFSet.{u}}
    (function : ZFSet.IsFunc Q E0 enumSelector)
    (clocks conditions births events enumerations : Nat → ZFSet.{u})
    (enumerationCases : ∀ k, enumerations k = ∅ ∨
      ZFSet.IsFunc ZFSet.omega stages (enumerations k))
    (chosen : ∀ k, ZFSet.pair (conditions k) (enumerations k) ∈ enumSelector)
    (initialClock : clocks 0 = ∅)
    (initialBirths : births 0 = {ZFSet.pair ∅ (enumerations 0)})
    (steps : ∀ k, FairPreparationStepCode ZFSet.omega E0 stages U
      enumSelector prepSelector
      (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k))))
      (ZFSet.pair (clocks (k + 1))
        (ZFSet.pair (conditions (k + 1)) (ZFSet.pair (births (k + 1)) (events (k + 1))))))
    (i j : Nat) (alpha : ZFSet.{u})
    (entry : ZFSet.pair (natSetCode j) alpha ∈ enumerations i) :
    ∃ y ∈ U,
      (∃ payload, y = ZFSet.pair (conditions (Nat.pair i j + 1)) payload) ∧
      ZFSet.pair (ZFSet.pair alpha (conditions (Nat.pair i j))) y ∈ prepSelector ∧
      events (Nat.pair i j + 1) = ZFSet.pair alpha y := by
  have persistent := fairPreparation_birthPersistence function clocks conditions births events
    enumerations chosen initialClock initialBirths steps (Nat.pair i j)
  obtain ⟨n, p, b, last, m, q, nextBirths, event, source, target, _next,
    oldI, _hi, oldJ, _hj, e, _he, newE, _hNew, grid, old, _selected, _append, branch⟩ :=
    steps (Nat.pair i j)
  obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 source
  obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
  obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 target
  obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
  rw [persistent.1] at grid
  have exactGrid : ZFSet.pair (natSetCode (Nat.pair i j))
      (ZFSet.pair (natSetCode i) (natSetCode j)) ∈
      natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv := by
    have edge : ZFSet.pair (natSetCode (Nat.pair i j))
        (ZFSet.pair (natSetCode (Nat.unpair (Nat.pair i j)).1)
          (natSetCode (Nat.unpair (Nat.pair i j)).2)) ∈
        natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv :=
      (natPresentation.pair_mem_graph (natPresentation.product natPresentation)
        omegaGridEquiv ⟨Nat.pair i j⟩ (omegaGridEquiv ⟨Nat.pair i j⟩)).2 rfl
    simpa only [Nat.unpair_pair] using edge
  have gridFunction := natPresentation.graph_isFunc
    (natPresentation.product natPresentation) omegaGridEquiv
  obtain ⟨_, _, gridUnique⟩ := gridFunction.2 _ (natSetCode_mem_omega (Nat.pair i j))
  have sameGrid := (gridUnique _ grid).trans (gridUnique _ exactGrid).symm
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 sameGrid
  have sameEnumeration := ((persistent.2.2.1 i e).1 old).2
  subst e
  have nonempty : enumerations i ≠ ∅ := by
    intro empty
    exact ZFSet.notMem_empty _ (empty ▸ entry)
  rcases branch with idle | active
  · exact False.elim (nonempty idle.1)
  · obtain ⟨level, _hLevel, y, hy, shape, levelEntry, prepared, recorded⟩ := active
    have enumFunction := (enumerationCases i).resolve_left nonempty
    obtain ⟨_, _, unique⟩ := enumFunction.2 _ (natSetCode_mem_omega j)
    have sameLevel := (unique _ levelEntry).trans (unique _ entry).symm
    subst level
    exact ⟨y, hy, shape, prepared, recorded⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R]
variable (c : Presentation R) (T stages history : ZFSet.{u})
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "B" => M.groundSmallSubsets
  (stageOneAssignments (refinementDataHistoryIndices stages history) T) ZFSet.omega
local notation "shape" => M.refinementHistoryForcing_shape c.carrier T stages history
local notation "data" => flatCarrierData c Q B shape

theorem refinementHistorySequence_assignment_mono :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ seq : Nat → SetMembers Q, Antitone seq →
      ∀ i k, i ≤ k → SetMembers.raw (data (seq i)) ⊆ SetMembers.raw (data (seq k)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq decreasing i k before
  have below := decreasing before
  change ZFSet.pair (SetMembers.raw (seq k)) (SetMembers.raw (seq i)) ∈
    M.refinementHistoryOrder c.carrier c.conditionOrder T stages history at below
  rw [flatCarrier_coordinates c Q B shape (seq k), flatCarrier_coordinates c Q B shape (seq i)] at below
  exact ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages history
    _ _ _ _).1 below).2.2.2

theorem refinementHistorySequence_assignment_visit
    (valid : RefinementDataHistory stages history T) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ seq : Nat → SetMembers Q, Antitone seq → ∀ enumerations : Nat → ZFSet.{u},
      (∀ i, BirthLevelEnumerationCode ZFSet.omega stages (SetMembers.raw (data (seq i)))
        (refinementDataHistoryLevels stages history T) (enumerations i)) →
      ∀ x ∈ stageOneAssignmentUnion (fun i => SetMembers.raw (data (seq i))),
        ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
          Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
          x ∈ SetMembers.raw (data (seq i)) ∧
          ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
          ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages history T ∧
          alpha ∈ relationImage (SetMembers.raw (data (seq i))) stages
            (refinementDataHistoryLevels stages history T) ∧
          ZFSet.pair (natSetCode j) alpha ∈ enumerations i ∧
          ∀ k, Nat.pair i j ≤ k →
            x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k))) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq decreasing enumerations coded x member
  have bounded : ∀ i, SetMembers.raw (data (seq i)) ⊆
      stageOneAssignments (refinementDataHistoryIndices stages history) T := by
    intro i
    exact ((M.mem_groundSmallSubsets _ _ _).1 (SetMembers.raw_mem (data (seq i)))).2.1
  exact valid.birthEnumeration_assignment_visit (fun i => SetMembers.raw (data (seq i))) enumerations
    bounded (M.refinementHistorySequence_assignment_mono c T stages history seq decreasing) coded member

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R]
variable (c : Presentation R) (T stages history : ZFSet.{u})
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "B" => M.groundSmallSubsets
  (stageOneAssignments (refinementDataHistoryIndices stages history) T) ZFSet.omega
local notation "shape" => M.refinementHistoryForcing_shape c.carrier T stages history
local notation "data" => flatCarrierData c Q B shape

theorem fairRefinementSequence_assignment_prepared
    (valid : RefinementDataHistory stages history T)
    {E0 U enumSelector prepSelector : ZFSet.{u}}
    (function : ZFSet.IsFunc Q E0 enumSelector)
    (selected : enumSelector ⊆ M.birthLevelEnumerationRelation Q stages
      (refinementDataHistoryLevels stages history T)) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ (seq : Nat → SetMembers Q), Antitone seq →
    ∀ (clocks births events : Nat → ZFSet.{u}) (initialE : ZFSet.{u}),
    ZFSet.pair (SetMembers.raw (seq 0)) initialE ∈ enumSelector →
    clocks 0 = ∅ → births 0 = {ZFSet.pair ∅ initialE} →
    (∀ k, FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector
      (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
      (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k))
        (ZFSet.pair (births k) (events k))))
      (ZFSet.pair (clocks (k + 1)) (ZFSet.pair (SetMembers.raw (seq (k + 1)))
        (ZFSet.pair (births (k + 1)) (events (k + 1)))))) →
    ∀ x ∈ stageOneAssignmentUnion (fun i => SetMembers.raw (data (seq i))),
      ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
        Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
        x ∈ SetMembers.raw (data (seq i)) ∧
        ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
        ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages history T ∧
        (∀ k, Nat.pair i j ≤ k →
          x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k)))) ∧
        ∃ y ∈ U, ∃ payload,
          y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
          ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
          events (Nat.pair i j + 1) = ZFSet.pair alpha y := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro seq decreasing clocks births events initialE initialChosen initialClock initialBirths steps x member
  have available (k : Nat) : ∃ e, ZFSet.pair (SetMembers.raw (seq k)) e ∈ enumSelector := by
    obtain ⟨e, edge, _⟩ := function.2 _ (SetMembers.raw_mem (seq k))
    exact ⟨e, edge⟩
  choose enumerations chosen using available
  have codes (k : Nat) : BirthLevelEnumerationCode ZFSet.omega stages
      (SetMembers.raw (data (seq k))) (refinementDataHistoryLevels stages history T) (enumerations k) := by
    have entry := selected (chosen k)
    rw [flatCarrier_coordinates c Q B shape (seq k)] at entry
    exact ((M.pair_mem_birthLevelEnumerationRelation _ _ _ _ _ _).1 entry).2.2
  have enumerationCases (k : Nat) : enumerations k = ∅ ∨ ZFSet.IsFunc ZFSet.omega stages (enumerations k) :=
    (codes k).elim (fun idle => Or.inl idle.2) (fun active => Or.inr active.1)
  have initialSame : initialE = enumerations 0 := by
    obtain ⟨_, _, unique⟩ := function.2 _ (SetMembers.raw_mem (seq 0))
    exact (unique _ initialChosen).trans (unique _ (chosen 0)).symm
  have initialTable : births 0 = {ZFSet.pair ∅ (enumerations 0)} := by
    rw [← initialSame]
    exact initialBirths
  obtain ⟨i, j, alpha, hAlpha, fields, grid, before, born, stored, level, _attained, enumerated, retained⟩ :=
    M.refinementHistorySequence_assignment_visit c T stages history valid seq decreasing
      enumerations codes x member
  obtain ⟨y, hy, ⟨payload, output⟩, edge, event⟩ :=
    fairPreparation_scheduledActiveEvent function clocks (fun k => SetMembers.raw (seq k)) births events
      enumerations enumerationCases chosen initialClock initialTable steps i j alpha enumerated
  exact ⟨i, j, alpha, hAlpha, fields, grid, before, born, stored, level, retained,
    y, hy, payload, output, edge, event⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticFairPreparationLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
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

theorem semanticStructuralTrace_exact_assignment_union
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let B := M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
    let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
    let row := flatCarrierRow c Q B shape
    let data := flatCarrierData c Q B shape
    ∀ seq : Nat → SetMembers Q, groundSequenceGraph seq ∈ M.sets → Antitone seq →
      ∃ q : R, (∀ n, q ≤ row (seq n)) ∧ ∃ p : SetMembers Q,
        SetMembers.raw p = ZFSet.pair (c.encode q)
          (stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n)))) ∧
        (∀ n, p ≤ seq n) ∧
        SetMembers.raw (data p) = stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∧
        stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∈ M.sets ∧
        ∀ z, z ∈ SetMembers.raw (data p) ↔ ∃ n, z ∈ SetMembers.raw (data (seq n)) := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have unionTests := M.structuralHistory_rawTests_union t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  let B := M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
  let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
  let data := flatCarrierData c Q B shape
  dsimp only
  intro seq whole decreasing
  obtain ⟨q, belowRows, p, code, below⟩ := M.refinementHistory_lower_bound c T stages packed
    run ordinal unionTests pairing unions powers separation infinite choice carrier hT hs hPacked
    rowClosed seq whole decreasing
  have dataEqual : SetMembers.raw (data p) =
      stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) := by
    have coordinates := flatCarrier_coordinates c Q B shape p
    rw [code] at coordinates
    exact (ZFSet.pair_inj.1 coordinates).2.symm
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have conditionGround := M.transitive hQ (SetMembers.raw_mem p)
  rw [code] at conditionGround
  refine ⟨q, belowRows, p, code, below, dataEqual, M.pair_right conditionGround, ?_⟩
  intro z
  rw [dataEqual]
  exact mem_stageOneAssignmentUnion _ z

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
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

theorem semanticStructuralFairPreparation_lower_bound
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let B := M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
    let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
    let data := flatCarrierData c Q B shape
    ∀ (p : SetMembers Q) (E0 enumSelector prepSelector orbit e : ZFSet.{u}),
      E0 ∈ M.sets → orbit ∈ M.sets →
      ZFSet.IsFunc Q E0 enumSelector →
      enumSelector ⊆ M.birthLevelEnumerationRelation Q stages (refinementDataHistoryLevels stages packed T) →
      prepSelector ⊆ M.varyingPreparationRelation stages packed Q
        (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) b.carrier T →
      ZFSet.pair (SetMembers.raw p) e ∈ enumSelector →
      ZFSet.IsFunc ZFSet.omega
        (M.fairPreparationStates Q stages (M.preparationWitnessBound b.carrier T Q) E0 enumSelector) orbit →
      (∀ state, ZFSet.pair ∅ state ∈ orbit ↔
        state = ZFSet.pair ∅ (ZFSet.pair (SetMembers.raw p) (ZFSet.pair {ZFSet.pair ∅ e} ∅))) →
      (∀ n ∈ ZFSet.omega, ∀ state next,
        ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
        FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T Q)
          enumSelector prepSelector
          (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv) state next) →
      ∃ seq : Nat → SetMembers Q, seq 0 = p ∧ groundSequenceGraph seq ∈ M.sets ∧ Antitone seq ∧
      ∃ clocks births events : Nat → ZFSet.{u},
        clocks 0 = ∅ ∧ births 0 = {ZFSet.pair ∅ e} ∧ events 0 = ∅ ∧
        (∀ k, FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T Q)
          enumSelector prepSelector
          (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
          (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k)) (ZFSet.pair (births k) (events k))))
          (ZFSet.pair (clocks (k + 1))
            (ZFSet.pair (SetMembers.raw (seq (k + 1))) (ZFSet.pair (births (k + 1)) (events (k + 1)))))) ∧
      ∃ limit : SetMembers Q, (∀ n, limit ≤ seq n) ∧
        SetMembers.raw (data limit) = stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∧
        stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∈ M.sets ∧
        (∀ z, z ∈ SetMembers.raw (data limit) ↔ ∃ n, z ∈ SetMembers.raw (data (seq n))) ∧
        ∀ x ∈ SetMembers.raw (data limit),
          ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
            Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
            x ∈ SetMembers.raw (data (seq i)) ∧
            ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
            ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages packed T ∧
            (∀ k, Nat.pair i j ≤ k →
              x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k)))) ∧
            ∃ y ∈ M.preparationWitnessBound b.carrier T Q, ∃ payload,
              y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
              ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
              events (Nat.pair i j + 1) = ZFSet.pair alpha y := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  let upper := SetMembers.presentation Q
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hU := M.preparationWitnessBound_mem pairing unions powers separation nodes hT hQ omega
  dsimp only
  intro p E0 enumSelector prepSelector orbit e hE0 whole enumFunction enumSelected
    prepSelected chosen orbitFunction initial steps
  have selected : prepSelector ⊆ M.varyingPreparationRelation stages packed
      upper.carrier upper.conditionOrder b.carrier T := by
    exact Eq.mpr (congrArg
      (fun order => prepSelector ⊆ M.varyingPreparationRelation stages packed Q order b.carrier T)
      (M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed)) prepSelected
  obtain ⟨seq, start, seqGround, decreasing, clocks, births, events,
      clockZero, birthZero, eventZero, _entries, rawSteps⟩ :=
    M.fairPreparationOrbit_conditionSequence upper pairing unions powers separation
      hQ hs hU hE0 omega whole orbitFunction selected p e initial steps
  obtain ⟨_q, _belowRows, limit, _code, below, dataEqual, unionGround, exactEntries⟩ :=
    M.semanticStructuralTrace_exact_assignment_union c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
      nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
      symmetric1 symmetric2 topMem topRows hs hh ordinal trace infinite choice rowClosed seq seqGround decreasing
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have initialChosen : ZFSet.pair (SetMembers.raw (seq 0)) e ∈ enumSelector := start.symm ▸ chosen
  refine ⟨seq, start, seqGround, decreasing, clocks, births, events, clockZero, birthZero, eventZero,
    rawSteps, limit, below, dataEqual, unionGround, exactEntries, ?_⟩
  intro x member
  exact M.fairRefinementSequence_assignment_prepared c T stages packed run.carriers.data
    enumFunction enumSelected seq decreasing clocks births events e initialChosen clockZero birthZero
    rawSteps x (dataEqual ▸ member)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRawPreparedFamilyConditionPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem preparedCertificateCode_condition_mono
    (nodes nodeOrder meet N visibility top omega : ZFSet.{u})
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes → IsName s V)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F B f e names : ZFSet.{u})
    {p q : P} (qp : q ≤ p)
    (code : PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      nodes nodeOrder meet N visibility top omega z.val.val F B f e names) :
    PreparedCertificateCode M s.carrier s.conditionOrder (s.encode q)
      nodes nodeOrder meet N visibility top omega z.val.val F B f e names := by
  obtain ⟨filter, coinitial, nonempty, enumerated, supported, forced⟩ := code
  refine ⟨filter, coinitial, nonempty, enumerated, supported, ?_⟩
  apply M.preparationForcingCode_condition_mono s pairing unions powers separation collection
    carrier order nodes N visibility graphGround graphNames namesGround validN z F f _ qp forced
  intro entry member
  obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (enumerated.1.1 member)
  have incidence := (pair_mem_visibilitySupportIncidence nodes N visibility top v tau).1
    (supported v tau member)
  exact ZFSet.pair_mem_prod.2 ⟨incidence.1, htau⟩

theorem preparedCertificateFamilyCode_condition_mono
    (nodes nodeOrder meet N visibility top omega J C E k enumerations : ZFSet.{u})
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes → IsName s V)
    (namesGround : N ∈ M.sets) (validN : ∀ tau ∈ N, IsName s tau)
    (requestsGround : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
    {p q : P} (qp : q ≤ p)
    (code : PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode p)
      nodes nodeOrder meet N visibility top omega J C E k enumerations) :
    PreparedCertificateFamilyCode M s.carrier s.conditionOrder (s.encode q)
      nodes nodeOrder meet N visibility top omega J C E k enumerations := by
  refine ⟨code.1, code.2.1, ?_⟩
  intro z F B f e names stored enumerated
  have member := (ZFSet.pair_mem_prod.1 (code.1.1 stored)).1
  let name : (M.nameDomain s).names :=
    ⟨⟨z, validJ z member⟩, M.transitive requestsGround member⟩
  exact M.preparedCertificateCode_condition_mono s pairing unions powers separation collection
    carrier order nodes nodeOrder meet N visibility top omega graphGround graphNames
    namesGround validN name F B f e names qp (code.2.2 z F B f e names stored enumerated)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem preparedCertificateFamilyCode_raw_condition_mono
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (P order nodes nodeOrder meet N visibility top omega J C E k enumerations : ZFSet.{u})
    (orderCode : PartialOrderCode P order)
    (carrierGround : P ∈ M.sets) (orderGround : order ∈ M.sets)
    (graphGround : visibility ∈ M.sets)
    (graphNames : ∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes →
      IsName (SetMembers.presentation P) V)
    (namesGround : N ∈ M.sets)
    (validN : ∀ tau ∈ N, IsName (SetMembers.presentation P) tau)
    (requestsGround : J ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName (SetMembers.presentation P) z)
    (p q : ZFSet.{u}) (hp : p ∈ P) (hq : q ∈ P) (qp : ZFSet.pair q p ∈ order)
    (code : PreparedCertificateFamilyCode M P order p
      nodes nodeOrder meet N visibility top omega J C E k enumerations) :
    PreparedCertificateFamilyCode M P order q
      nodes nodeOrder meet N visibility top omega J C E k enumerations := by
  let := orderCode.toPartialOrder
  let s := SetMembers.presentation P
  have groundOrder : s.conditionOrder ∈ M.sets := M.decoded_order_mem orderCode orderGround
  have orderEq : s.conditionOrder = order := orderCode.conditionOrder_eq
  have pCode : s.encode (SetMembers.ofMem p hp) = p := SetMembers.raw_ofMem p hp
  have qCode : s.encode (SetMembers.ofMem q hq) = q := SetMembers.raw_ofMem q hq
  have typedBelow : SetMembers.ofMem q hq ≤ SetMembers.ofMem p hp := by
    change ZFSet.pair (SetMembers.raw (SetMembers.ofMem q hq))
      (SetMembers.raw (SetMembers.ofMem p hp)) ∈ order
    simpa only [SetMembers.raw_ofMem] using qp
  have initial : PreparedCertificateFamilyCode M s.carrier s.conditionOrder
      (s.encode (SetMembers.ofMem p hp)) nodes nodeOrder meet N visibility top omega
      J C E k enumerations := by
    exact (congrArg₂ (fun r c => PreparedCertificateFamilyCode M P r c
      nodes nodeOrder meet N visibility top omega J C E k enumerations) orderEq pCode).mpr code
  have moved := M.preparedCertificateFamilyCode_condition_mono s pairing unions powers
    separation collection carrierGround groundOrder nodes nodeOrder meet N visibility top omega
    J C E k enumerations graphGround graphNames namesGround validN requestsGround validJ
    typedBelow initial
  exact (congrArg₂ (fun r c => PreparedCertificateFamilyCode M P r c
    nodes nodeOrder meet N visibility top omega J C E k enumerations) orderEq qCode).mp moved

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundStoredPreparationFamilyPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
include run

theorem preparationCut_strengthens
    {alpha r p q : ZFSet.{u}} (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history)
    (stronger : r ∈ M.refinementHistoryForcing rows T stages history)
    (below : ZFSet.pair r p ∈ M.refinementHistoryOrder rows rowOrder T stages history)
    (selected : ZFSet.pair p q ∈ rowAssignmentCutGraph
      (M.refinementHistoryForcing rows T stages history) (fields 7)
      (refinementDataHistoryLevels stages history T) alpha) :
    ∃ rCut, rCut ∈ fields 7 ∧ q ∈ fields 7 ∧
      ZFSet.pair r rCut ∈ rowAssignmentCutGraph
        (M.refinementHistoryForcing rows T stages history) (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      ZFSet.pair rCut q ∈ fields 8 := by
  obtain ⟨_, oldRow, oldA, equal⟩ := (mem_rowAssignmentCutGraph _ _ _ _ _).1 selected
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  have oldValid := ((pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).1 selected).2.1
  obtain ⟨newRow, _, newA, _, rfl⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape rows T stages history stronger)
  have member := run.carriers.data.function.pair_source stored
  have newValid := (run.carriers.carrier alpha fields stored).symm ▸
    run.carriers.cut_mem stronger member
  refine ⟨ZFSet.pair newRow
      (assignmentCut (refinementDataHistoryLevels stages history T) alpha newA),
    newValid, oldValid, ?_, run.lower_order fields stored below⟩
  exact (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2 ⟨stronger, newValid, rfl⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem storedPreparationFamily_cut_mono
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {rows rowOrder T stages history alpha r p q A meet C E k enumerations : ZFSet.{u}}
    (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
    (fields : Fin 15 → ZFSet.{u}) (environment : StoredPreparationEnvironment M fields)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history)
    (hA : A ∈ M.sets)
    (stronger : r ∈ M.refinementHistoryForcing rows T stages history)
    (below : ZFSet.pair r p ∈ M.refinementHistoryOrder rows rowOrder T stages history)
    (selected : ZFSet.pair p q ∈ rowAssignmentCutGraph
      (M.refinementHistoryForcing rows T stages history) (fields 7)
      (refinementDataHistoryLevels stages history T) alpha)
    (code : PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
      meet (fields 14) (fields 13) (fields 9) ZFSet.omega
      (M.storedPreparationRequests A fields) C E k enumerations) :
    ∃ rCut, rCut ∈ fields 7 ∧
      ZFSet.pair r rCut ∈ rowAssignmentCutGraph
        (M.refinementHistoryForcing rows T stages history) (fields 7)
        (refinementDataHistoryLevels stages history T) alpha ∧
      ZFSet.pair rCut q ∈ fields 8 ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) rCut (fields 10) (fields 11)
        meet (fields 14) (fields 13) (fields 9) ZFSet.omega
        (M.storedPreparationRequests A fields) C E k enumerations := by
  obtain ⟨rCut, hrCut, hq, cut, lowerBelow⟩ :=
    run.preparationCut_strengthens fields stored stronger below selected
  have requestsGround := M.storedPreparationRequests_mem pairing unions powers separation
    hA fields environment.ground
  have requestsValid : ∀ z ∈ M.storedPreparationRequests A fields,
      IsName (SetMembers.presentation (fields 7)) z := by
    intro z hz
    rcases ZFSet.mem_union.1 hz with left | right
    · exact environment.names_valid z ((mem_relationImage _ _ _ _).1 left).1
    · exact environment.names_valid z ((mem_relationImage _ _ _ _).1 right).1
  refine ⟨rCut, hrCut, cut, lowerBelow, ?_⟩
  exact M.preparedCertificateFamilyCode_raw_condition_mono pairing unions powers separation collection
    (fields 7) (fields 8) (fields 10) (fields 11) meet (fields 14) (fields 13) (fields 9)
    ZFSet.omega (M.storedPreparationRequests A fields) C E k enumerations environment.order
    (environment.ground 7) (environment.ground 8) (environment.ground 13)
    environment.visibility_valid (environment.ground 14) environment.names_valid
    requestsGround requestsValid q rCut hq hrCut lowerBelow code

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedCopyCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
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
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_preparationEnvironment (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed) :
    StoredPreparationEnvironment M fields := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have exactStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same : fields = M.refinementLevelFormulaData act lower b d alpha T T2 valid :=
    refinementFormulaDataCode_injective ((run).carriers.data.function.unique stored exactStored)
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have members : ∀ j, fields j ∈ M.sets := M.refinementFormulaDataCode_fields_mem fields
    (M.transitive (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion stored))
  refine ⟨?_, members, ?_, ?_⟩
  · rw [same]
    exact lower.conditionOrder_code
  · rw [same]
    intro z hz
    exact Name.isName_of_subset valid ((M.mem_groundRelations T lower.carrier z).1 hz).2
  · rw [same]
    intro v V entry _
    obtain ⟨i, equal⟩ := (M.mem_niceVisibilityGraph act lower b T d.principalFix
      (ZFSet.pair v V)).1 entry
    have value := (ZFSet.pair_inj.1 equal).2
    rw [value]
    exact (M.niceVisibilityName act lower T (d.principalFix i)).property

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundFairPreparationLimitCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v

variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {R : Type u} [PartialOrder R] (c : Presentation R)

theorem exists_groundFairPreparationLowerBound
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    ∀ (_descent : ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
    ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val
    ),
    ∀ p ∈ upperQ, FairPreparationLowerBoundResult M c T stages packed b.carrier p := by
  let geometry := run.finalGeometry i₀
  let instGeometryGroup := geometry.group_code.toGroup
  let instGeometryOrder := geometry.meet.order.toPartialOrder
  let instGeometryBottom := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
  intro stages history hs hh ordinal trace
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T
  intro descent p hp
  refine Exists.elim
    (fulfilled.exists_groundFairPreparationOrbit c collection infinite choice small smallD irreflexive rowClosed
      a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
      topMem topRows stages history hs hh ordinal trace descent p hp)
    (fun enumSelector enumRest => ?_)
  have hEnum := enumRest.1
  have enumFunction := enumRest.2.1
  have enumSelected := enumRest.2.2.1
  refine Exists.elim enumRest.2.2.2 (fun E0 rangeRest => ?_)
  have hE0 := rangeRest.1
  have rangeFunction := rangeRest.2.1
  refine Exists.elim rangeRest.2.2 (fun prepSelector prepRest => ?_)
  have hPrep := prepRest.1
  have prepFunction := prepRest.2.1
  have prepSelected := prepRest.2.2.1
  refine Exists.elim prepRest.2.2.2 (fun e eRest => ?_)
  have he := eRest.1
  have chosen := eRest.2.1
  refine Exists.elim eRest.2.2 (fun orbit orbitRest => ?_)
  have hOrbit := orbitRest.1
  have orbitFunction := orbitRest.2.1
  have initial := orbitRest.2.2.1
  have steps := orbitRest.2.2.2
  let instHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let pTyped : SetMembers upperQ := SetMembers.ofMem p hp
  have typedChosen : ZFSet.pair (SetMembers.raw pTyped) e ∈ enumSelector := by
    simpa only [pTyped, SetMembers.raw_ofMem] using chosen
  have typedInitial : ∀ state, ZFSet.pair ∅ state ∈ orbit ↔
      state = ZFSet.pair ∅ (ZFSet.pair (SetMembers.raw pTyped) (ZFSet.pair {ZFSet.pair ∅ e} ∅)) := by
    simpa only [pTyped, SetMembers.raw_ofMem] using initial
  obtain ⟨seq, start, seqGround, decreasing, clocks, births, events,
      clockZero, birthZero, eventZero, rawSteps, limit, below, dataEqual,
      unionGround, exactEntries, visits⟩ :=
    M.semanticStructuralFairPreparation_lower_bound c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction
      geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
      hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hs hh ordinal trace infinite choice rowClosed pTyped E0 enumSelector prepSelector orbit e
      hE0 hOrbit rangeFunction enumSelected prepSelected typedChosen orbitFunction typedInitial steps
  refine ⟨enumSelector, hEnum, enumFunction, enumSelected, E0, hE0, rangeFunction,
    prepSelector, hPrep, prepFunction, prepSelected, seq, ?_, seqGround, (fun _ _ h => decreasing h),
    e, he, chosen, clocks, births, events, clockZero, birthZero, eventZero, rawSteps,
    limit, below, dataEqual, unionGround, exactEntries, visits⟩
  exact (congrArg SetMembers.raw start).trans (SetMembers.raw_ofMem p hp)

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {R : Type u} [PartialOrder R]

theorem FairPreparationLowerBoundResult.exists_storedPreparedLimit
    (c : Presentation R)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {T stages packed nodes p : ZFSet.{u}}
    (run : RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages packed)
    (environments : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
        StoredPreparationEnvironment M fields)
    (result : FairPreparationLowerBoundResult M c T stages packed nodes p) :
    ∃ limit ∈ M.refinementHistoryForcing c.carrier T stages packed,
      ZFSet.pair limit p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
      StoredPreparedConditionCode M c.carrier T stages packed nodes limit := by
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  let order := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let B := M.groundSmallSubsets
    (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
  let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
  let data := flatCarrierData c Q B shape
  let row := flatCarrierRow c Q B shape
  obtain ⟨enumSelector, _hEnum, _enumFunction, _enumSelected, E0, _hE0, _rangeFunction,
    prepSelector, _hPrep, _prepFunction, prepSelected, seq, start, _seqGround, _decreasing,
    e, _he, _chosen, clocks, births, events, _clockZero, _birthZero, _eventZero, _rawSteps,
    limit, below, _dataEqual, _unionGround, _exactEntries, visits⟩ := result
  refine ⟨SetMembers.raw limit, SetMembers.raw_mem limit, ?_, ?_⟩
  · exact start ▸ below 0
  intro limitRow limitA limitCode x hx
  have limitData : SetMembers.raw (data limit) = limitA :=
    (ZFSet.pair_inj.1 ((flatCarrier_coordinates c Q B shape limit).symm.trans limitCode)).2
  have inData : x ∈ SetMembers.raw (data limit) := limitData.symm ▸ hx
  obtain ⟨i, j, alpha, hAlpha, fields, _unpaired, _born, _early, stored, _level,
    retained, y, _hy, payload, yCode, selected, _event⟩ := visits x inData
  let n := Nat.pair i j
  have relationEntry := prepSelected selected
  rw [yCode] at relationEntry
  obtain ⟨_, _inputMember, bounded, other, otherStored, terms, nodeCarrier, meetCode, code⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed Q order nodes T alpha
      (SetMembers.raw (seq n)) (ZFSet.pair (SetMembers.raw (seq (n + 1))) payload)).1 relationEntry
  have same : other = fields :=
    refinementFormulaDataCode_injective (run.carriers.data.function.unique otherStored stored)
  subst other
  obtain ⟨sourceRow, sourceA, output, k, enumerations, q,
    inputCode, outputCode, _visitBelow, cut, family⟩ := code
  have sourceData : SetMembers.raw (data (seq n)) = sourceA :=
    (ZFSet.pair_inj.1 ((flatCarrier_coordinates c Q B shape (seq n)).symm.trans inputCode)).2
  obtain ⟨outputEq, payloadEq⟩ := ZFSet.pair_inj.1 outputCode
  subst output
  rw [payloadEq] at bounded
  obtain ⟨_, hkBound, heBound⟩ := (M.mem_preparationWitnessBound nodes T Q
    (SetMembers.raw (seq (n + 1))) k enumerations).1 bounded
  have hk := ((M.mem_groundRelations _ _ k).1 hkBound).1
  have hEnumerations := ((M.mem_groundRelations _ _ enumerations).1 heBound).1
  have hSourceA : sourceA ∈ M.sets := sourceData ▸
    ((M.mem_groundSmallSubsets _ _ _).1 (SetMembers.raw_mem (data (seq n)))).1
  have sourceMember : ZFSet.pair sourceRow sourceA ∈ Q := inputCode ▸ SetMembers.raw_mem (seq n)
  have sourceBelow := below n
  rw [limitCode, inputCode] at sourceBelow
  have sourceSubset := ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
    stages packed limitRow limitA sourceRow sourceA).1 sourceBelow).2.2.2
  have sourceSelected : x ∈ assignmentOnIndices (fields 0) T sourceA :=
    sourceData ▸ retained n (Nat.le_refl n)
  have environment := environments alpha fields stored
  obtain ⟨rCut, hrCut, finalCut, _cutBelow, finalFamily⟩ :=
    M.storedPreparationFamily_cut_mono pairing unions powers separation collection run fields
      environment stored hSourceA (SetMembers.raw_mem limit) (below (n + 1)) cut family
  exact ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meetCode, environment,
    sourceRow, sourceA, hSourceA, sourceMember, sourceSubset, sourceSelected,
    k, hk, enumerations, hEnumerations, rCut, hrCut, finalCut, finalFamily⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalStoredPreparedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {R : Type u} [PartialOrder R] (c : Presentation R)

theorem exists_groundStoredPreparedStrengthening_oai
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    ∀ (_descent : ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
    ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val
    ),
    ∀ p ∈ upperQ, ∃ q ∈ upperQ,
      ZFSet.pair q p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
      StoredPreparedConditionCode M c.carrier T stages packed b.carrier q := by
  let geometry := run.finalGeometry i₀
  let instGeometryGroup := geometry.group_code.toGroup
  let instGeometryOrder := geometry.meet.order.toPartialOrder
  let instGeometryBottom := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
  intro stages history hs hh ordinal trace
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  intro descent p hp
  have fair := fulfilled.exists_groundFairPreparationLowerBound c collection infinite choice small smallD
    irreflexive rowClosed a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows stages history hs hh ordinal trace descent p hp
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  apply FairPreparationLowerBoundResult.exists_storedPreparedLimit c pairing unions powers separation
    collection historyRun _ fair
  intro alpha fields stored
  have member := historyRun.carriers.data.function.pair_source stored
  exact M.semanticStructuralPrefix_preparationEnvironment c a t b d ⊥ directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrder rowAction
    geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
    hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
    hs hh ordinal trace member fields stored

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundStoredPreparedStrengthening_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_groundStoredPreparedStrengthening_oai.{u, v}
