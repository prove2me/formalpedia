-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralFairPreparation_supported_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:27:10.662204+00:00
-- url     : https://prove2.me/submissions/9f58290c-e915-4dc9-8705-22d3f1fc9ead

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
import Definitions.Def_OAIQ253P009
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_preparationEvent_certificate_domain

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionClosure
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundCountable_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets) (nonempty : R.Nonempty)
    (small : M.groundEmbeddable R ZFSet.omega) :
    ∃ g ∈ M.sets, ZFSet.IsFunc ZFSet.omega R g ∧
      ∀ p ∈ R, ∃ n ∈ ZFSet.omega, ZFSet.pair n p ∈ g :=
  M.groundEmbeddable_enumeration pairing unions powers separation hR
    (M.omega_mem separation infinite) nonempty small

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})






theorem groundCountable_family_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets)
    (countR : M.groundEmbeddable R ZFSet.omega)
    (small : ∀ p ∈ R, M.groundEmbeddable p ZFSet.omega) :
    M.groundEmbeddable (⋃₀ R) ZFSet.omega := by
  classical
  by_cases nonempty : R.Nonempty
  · obtain ⟨g, hg, enumeration, onto⟩ :=
      M.groundCountable_enumeration pairing unions powers separation infinite hR nonempty countR
    exact M.countable_enumerated_union pairing unions powers separation infinite choice
      hR (M.union_mem unions hR) hg enumeration onto
      (fun p hp _ hz => ZFSet.mem_sUnion.2 ⟨p, hp, hz⟩) small
  · have empty : R = ∅ := by
      apply ZFSet.ext
      intro p
      exact ⟨fun hp => False.elim (nonempty ⟨p, hp⟩), fun hp => False.elim (ZFSet.notMem_empty p hp)⟩
    rw [empty, ZFSet.sUnion_empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨R, hR⟩

end PartitionPilot.Forcing.TransitiveGround



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStoredPreparedFamilyActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem mem_certificateUsedSupports (nodes k v : ZFSet.{u}) :
    v ∈ certificateUsedSupports nodes k ↔ v ∈ nodes ∧
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B :=
  ZFSet.mem_sep

theorem preparationEventUsedSupports_active (nodes alpha r k enumerations : ZFSet.{u}) :
    preparationEventUsedSupports nodes (ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))) =
      certificateUsedSupports nodes k := by
  apply ZFSet.ext
  intro v
  rw [preparationEventUsedSupports, ZFSet.mem_sep, mem_certificateUsedSupports]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨alpha', r', k', e', equal, data⟩
    have middle := (ZFSet.pair_inj.1 equal).2
    have last := (ZFSet.pair_inj.1 middle).2
    have same := (ZFSet.pair_inj.1 last).1
    exact same.symm ▸ data
  · intro data
    exact ⟨alpha, r, k, enumerations, rfl, data⟩

theorem preparationEventUsedSupports_idle (nodes : ZFSet.{u}) :
    preparationEventUsedSupports nodes ∅ = ∅ := by
  apply ZFSet.ext
  intro v
  rw [preparationEventUsedSupports, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, alpha, r, k, enumerations, equal, _⟩
    have member : ({alpha} : ZFSet.{u}) ∈
        ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations)) := by
      exact ZFSet.mem_insert _ _
    rw [← equal] at member
    exact False.elim (ZFSet.notMem_empty _ member)
  · intro member
    exact False.elim (ZFSet.notMem_empty _ member)

namespace BoundedFormula

theorem truth_certificateBasisMemberFormula {n} (v k : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (certificateBasisMemberFormula v k) env ↔
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ env k ∧ env v ∈ B := by
  simp only [certificateBasisMemberFormula, truth_exGraphFields, truth_exPairFields, Truth]
  change (∃ z c, ZFSet.pair z c ∈ env k ∧ ∃ F tail, c = ZFSet.pair F tail ∧
    ∃ B f, tail = ZFSet.pair B f ∧ env v ∈ B) ↔ _
  constructor
  · rintro ⟨z, c, edge, F, tail, rfl, B, f, rfl, member⟩
    exact ⟨z, F, B, f, edge, member⟩
  · rintro ⟨z, F, B, f, edge, member⟩
    exact ⟨z, _, edge, F, _, rfl, B, f, rfl, member⟩

theorem truth_preparationEventSupportFormula {n} (v event : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (preparationEventSupportFormula v event) env ↔
      ∃ alpha r k enumerations,
        env event = ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations)) ∧
          ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ env v ∈ B := by
  simp only [preparationEventSupportFormula, truth_exPairFields, truth_certificateBasisMemberFormula]
  change (∃ alpha output, env event = ZFSet.pair alpha output ∧ ∃ r tail,
    output = ZFSet.pair r tail ∧ ∃ k enumerations, tail = ZFSet.pair k enumerations ∧
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ env v ∈ B) ↔ _
  constructor
  · rintro ⟨alpha, output, equal, r, tail, rfl, k, enumerations, rfl, data⟩
    exact ⟨alpha, r, k, enumerations, equal, data⟩
  · rintro ⟨alpha, r, k, enumerations, equal, data⟩
    exact ⟨alpha, _, equal, r, _, rfl, k, enumerations, rfl, data⟩

end BoundedFormula






end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPreparationEventSupportGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

private theorem truth_eventSupportSetFormula {n} (nodes event output : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (eventSupportSetFormula nodes event output) env ↔
      env output = preparationEventUsedSupports (env nodes) (env event) := by
  simp only [eventSupportSetFormula, Truth, truth_imp, truth_preparationEventSupportFormula]
  change (env output ⊆ env nodes ∧ ∀ v ∈ env nodes,
    (v ∈ env output → _) ∧ (_ → v ∈ env output)) ↔ _
  constructor
  · rintro ⟨inside, exact⟩
    apply ZFSet.ext
    intro v
    rw [preparationEventUsedSupports, ZFSet.mem_sep]
    exact ⟨fun hv => ⟨inside hv, (exact v (inside hv)).1 hv⟩,
      fun hv => (exact v hv.1).2 hv.2⟩
  · intro equal
    refine ⟨fun _ h => (ZFSet.mem_sep.1 (equal ▸ h)).1, ?_⟩
    intro v hv
    exact ⟨fun h => (ZFSet.mem_sep.1 (equal ▸ h)).2,
      fun h => equal.symm ▸ ZFSet.mem_sep.2 ⟨hv, h⟩⟩

private theorem truth_eventSupportGraphFormula (entry nodes : ZFSet.{u}) :
    Truth eventSupportGraphFormula ![entry, nodes] ↔
      ∃ event support, entry = ZFSet.pair event support ∧
        support = preparationEventUsedSupports nodes event := by
  simp only [eventSupportGraphFormula, truth_exPairFields, truth_eventSupportSetFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem preparationEventUsedSupports_mem (separation : SeparationSchema M.sets)
    {nodes event : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hEvent : event ∈ M.sets) :
    preparationEventUsedSupports nodes event ∈ M.sets := by
  have ground := M.bounded_separation_mem separation
    (BoundedFormula.preparationEventSupportFormula 0 1) ![event]
    (Fin.cases hEvent (fun j => Fin.elim0 j)) hNodes
  have equal : ZFSet.sep (fun v => BoundedFormula.Truth
      (BoundedFormula.preparationEventSupportFormula 0 1) (extend v ![event])) nodes =
        preparationEventUsedSupports nodes event := by
    apply ZFSet.ext
    intro v
    rw [ZFSet.mem_sep, BoundedFormula.truth_preparationEventSupportFormula,
      preparationEventUsedSupports, ZFSet.mem_sep]
    rfl
  exact equal ▸ ground

theorem pair_mem_preparationEventSupportGraph (nodes E event support : ZFSet.{u}) :
    ZFSet.pair event support ∈ M.preparationEventSupportGraph nodes E ↔
      event ∈ E ∧ support ∈ M.groundPower nodes ∧
        support = preparationEventUsedSupports nodes event := by
  rw [preparationEventSupportGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨he, hs⟩, event', support', equal, value⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨he, hs, value⟩
  · rintro ⟨he, hs, value⟩
    exact ⟨⟨he, hs⟩, event, support, rfl, value⟩

theorem preparationEventSupportGraph_function (separation : SeparationSchema M.sets)
    {nodes E : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets) :
    ZFSet.IsFunc E (M.groundPower nodes) (M.preparationEventSupportGraph nodes E) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
  intro event he
  have hs := (M.mem_groundPower nodes _).2
    ⟨M.preparationEventUsedSupports_mem separation hNodes (M.transitive hE he),
      fun _ h => (ZFSet.mem_sep.1 h).1⟩
  refine ⟨preparationEventUsedSupports nodes event,
    (M.pair_mem_preparationEventSupportGraph nodes E event _).2 ⟨he, hs, rfl⟩, ?_⟩
  intro support entry
  exact (M.pair_mem_preparationEventSupportGraph nodes E event support).1 entry |>.2.2

theorem preparationEventSupportGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes E : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets) :
    M.preparationEventSupportGraph nodes E ∈ M.sets := by
  have ground := M.bounded_separation_mem separation BoundedFormula.eventSupportGraphFormula
    ![nodes] (Fin.cases hNodes (fun j => Fin.elim0 j))
    (M.prod_mem pairing unions powers separation hE (M.groundPower_mem powers hNodes))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.eventSupportGraphFormula
      (extend z ![nodes])) (ZFSet.prod E (M.groundPower nodes)) =
        M.preparationEventSupportGraph nodes E := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, preparationEventSupportGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_eventSupportGraphFormula z nodes)
  exact equal ▸ ground

theorem preparationUsedSupportSequence_ground_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes E events : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (whole : events ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) :
    M.preparationUsedSupportSequence nodes E events ∈ M.sets ∧
      ZFSet.IsFunc ZFSet.omega (M.groundPower nodes)
        (M.preparationUsedSupportSequence nodes E events) :=
  ⟨M.relationCompose_mem pairing unions powers separation omega hE
    (M.groundPower_mem powers hNodes) whole
    (M.preparationEventSupportGraph_mem pairing unions powers separation hNodes hE),
    relationCompose_function_of_subset function
      (M.preparationEventSupportGraph_function separation hNodes hE) (fun _ h => h)⟩

theorem pair_mem_preparationUsedSupportSequence
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) (i support : ZFSet.{u}) :
    ZFSet.pair i support ∈ M.preparationUsedSupportSequence nodes E events ↔
      ∃ event, ZFSet.pair i event ∈ events ∧ support = preparationEventUsedSupports nodes event := by
  rw [preparationUsedSupportSequence, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, event, _, edge, value⟩
    exact ⟨event, edge, (M.pair_mem_preparationEventSupportGraph nodes E event support).1 value |>.2.2⟩
  · rintro ⟨event, edge, rfl⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have hs := (M.mem_groundPower nodes _).2
      ⟨M.preparationEventUsedSupports_mem separation hNodes (M.transitive hE bounds.2),
        fun _ h => (ZFSet.mem_sep.1 h).1⟩
    exact ⟨bounds.1, hs, event, bounds.2, edge,
      (M.pair_mem_preparationEventSupportGraph nodes E event _).2 ⟨bounds.2, hs, rfl⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

end

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



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticFairPreparationRecordedLimits
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

theorem fairPreparationEventGraph_function
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit) :
    ZFSet.IsFunc ZFSet.omega (insert ∅ (ZFSet.prod stages U))
      (M.fairPreparationEventGraph Q stages U E0 orbit) := by
  let histories := M.groundRelations ZFSet.omega E0
  let events := insert ∅ (ZFSet.prod stages U)
  let tail := ZFSet.prod histories events
  let middle := ZFSet.prod Q tail
  have widened : ZFSet.IsFunc ZFSet.omega (ZFSet.prod ZFSet.omega middle) orbit := by
    refine ⟨?_, function.2⟩
    intro z member
    obtain ⟨i, hi, state, hs, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hi, ((M.mem_fairPreparationStates _ _ _ _ _ _).1 hs).1⟩
  exact relationCompose_function_of_subset
    (relationCompose_function_of_subset
      (relationCompose_function_of_subset widened
        (productSecond_function ZFSet.omega middle) (fun _ h => h))
      (productSecond_function Q tail) (fun _ h => h))
    (productSecond_function histories events) (fun _ h => h)

theorem pair_mem_fairPreparationEventGraph
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (i event : ZFSet.{u}) :
    ZFSet.pair i event ∈ M.fairPreparationEventGraph Q stages U E0 orbit ↔
      ∃ clock p births,
        ZFSet.pair i (ZFSet.pair clock (ZFSet.pair p (ZFSet.pair births event))) ∈ orbit := by
  dsimp only [fairPreparationEventGraph]
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, tail, _, second, projectedEvent⟩
    obtain ⟨births, hb, event', he, equal⟩ := (mem_productSecond _ _ _).1 projectedEvent
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨_, _, middle, _, first, projectedTail⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
    obtain ⟨p, hp, tail', ht, equal⟩ := (mem_productSecond _ _ _).1 projectedTail
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨_, _, state, _, edge, projectedMiddle⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨clock, hc, middle', hm, equal⟩ := (mem_productSecond _ _ _).1 projectedMiddle
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨clock, p, births, edge⟩
  · rintro ⟨clock, p, births, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have stateBound := ((M.mem_fairPreparationStates _ _ _ _ _ _).1 bounds.2).1
    have split := ZFSet.pair_mem_prod.1 stateBound
    have middle := ZFSet.pair_mem_prod.1 split.2
    have tail := ZFSet.pair_mem_prod.1 middle.2
    refine ⟨bounds.1, tail.2, _, middle.2, ?_, ?_⟩
    · refine (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨bounds.1, middle.2, _, split.2, ?_, ?_⟩
      · exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
          ⟨bounds.1, split.2, _, stateBound, edge,
            (mem_productSecond _ _ _).2 ⟨clock, split.1, _, split.2, rfl⟩⟩
      · exact (mem_productSecond _ _ _).2 ⟨p, middle.1, _, middle.2, rfl⟩
    · exact (mem_productSecond _ _ _).2 ⟨births, tail.1, event, tail.2, rfl⟩

theorem fairPreparationEventGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages U E0 orbit : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (whole : orbit ∈ M.sets) :
    M.fairPreparationEventGraph Q stages U E0 orbit ∈ M.sets := by
  have hHistories := M.groundRelations_mem pairing unions powers separation omega hE0
  have hEvents := M.insert_mem pairing unions (M.empty_mem ⟨Q, hQ⟩)
    (M.prod_mem pairing unions powers separation hStages hU)
  have hTail := M.prod_mem pairing unions powers separation hHistories hEvents
  have hMiddle := M.prod_mem pairing unions powers separation hQ hTail
  exact M.relationCompose_mem pairing unions powers separation omega hTail hEvents
    (M.relationCompose_mem pairing unions powers separation omega hMiddle hTail
      (M.relationCompose_mem pairing unions powers separation omega
        (M.prod_mem pairing unions powers separation omega hMiddle) hMiddle whole
        (M.productSecond_mem pairing unions powers separation omega hMiddle))
      (M.productSecond_mem pairing unions powers separation hQ hTail))
    (M.productSecond_mem pairing unions powers separation hHistories hEvents)

theorem fairPreparationEvents_graph_eq
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (clocks conditions births events : Nat → ZFSet.{u})
    (entries : ∀ k, ZFSet.pair (natSetCode k)
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k)))) ∈ orbit) :
    familyCodeGraph natSetCode events = M.fairPreparationEventGraph Q stages U E0 orbit := by
  have domain : ZFSet.range (natSetCode : Nat → ZFSet.{u}) = ZFSet.omega := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_range, mem_omega_iff_natSetCode]
    exact ⟨fun ⟨n, h⟩ => ⟨n, h.symm⟩, fun ⟨n, h⟩ => ⟨n, h.symm⟩⟩
  exact familyCodeGraph_eq_of_entries ⟨_, M.fairPreparationEventGraph_function function⟩
    natSetCode events domain (fun k =>
      (M.pair_mem_fairPreparationEventGraph function _ _).2 ⟨clocks k, conditions k, births k, entries k⟩)

theorem fairPreparationEvents_ground_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (whole : orbit ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (clocks conditions births events : Nat → ZFSet.{u})
    (entries : ∀ k, ZFSet.pair (natSetCode k)
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k)))) ∈ orbit) :
    familyCodeGraph natSetCode events ∈ M.sets ∧
      ZFSet.IsFunc ZFSet.omega (insert ∅ (ZFSet.prod stages U)) (familyCodeGraph natSetCode events) := by
  rw [M.fairPreparationEvents_graph_eq function clocks conditions births events entries]
  exact ⟨M.fairPreparationEventGraph_mem pairing unions powers separation hQ hStages hU hE0 omega whole,
    M.fairPreparationEventGraph_function function⟩

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateBasisUnions
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

theorem certificateBasisGraph_function {J nodes N k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k) :
    ZFSet.IsFunc J (M.groundSmallSubsets nodes ZFSet.omega)
      (M.certificateBasisGraph J nodes N k) :=
  relationCompose_function_of_subset
    (relationCompose_function_of_subset function (productSecond_function _ _) (fun _ h => h))
    (productFirst_function _ _) (fun _ h => h)

theorem pair_mem_certificateBasisGraph {J nodes N k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k)
    (z B : ZFSet.{u}) :
    ZFSet.pair z B ∈ M.certificateBasisGraph J nodes N k ↔
      ∃ F f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k := by
  dsimp only [certificateBasisGraph]
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, tail, _, first, projected⟩
    obtain ⟨B', hB, f, hf, equal⟩ := (mem_productFirst _ _ _).1 projected
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨_, _, c, _, edge, projected⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨F, hF, tail', ht, equal⟩ := (mem_productSecond _ _ _).1 projected
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨F, f, edge⟩
  · rintro ⟨F, f, edge⟩
    have bound := ZFSet.pair_mem_prod.1 (function.1 edge)
    have fields := ZFSet.pair_mem_prod.1 bound.2
    have tail := ZFSet.pair_mem_prod.1 fields.2
    exact ⟨bound.1, tail.1, _, fields.2,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨bound.1, fields.2, _, bound.2, edge,
          (mem_productSecond _ _ _).2 ⟨F, fields.1, _, fields.2, rfl⟩⟩,
      (mem_productFirst _ _ _).2 ⟨B, tail.1, f, tail.2, rfl⟩⟩

theorem certificateBasisGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J nodes N k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hN : N ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (hk : k ∈ M.sets) :
    M.certificateBasisGraph J nodes N k ∈ M.sets := by
  have hBases := M.groundSmallSubsets_mem powers separation hNodes omega
  have hFunctions := M.groundRelations_mem pairing unions powers separation hNodes hN
  have hTail := M.prod_mem pairing unions powers separation hBases hFunctions
  exact M.relationCompose_mem pairing unions powers separation hJ hTail hBases
    (M.relationCompose_mem pairing unions powers separation hJ
      (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hN omega)
      hTail hk (M.productSecond_mem pairing unions powers separation
        (M.groundPower_mem powers hNodes) hTail))
    (M.productFirst_mem pairing unions powers separation hBases hFunctions)

theorem certificateUsedSupports_eq_basisUnion {J nodes N k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k) :
    certificateUsedSupports nodes k = (relationImage J
      (M.groundSmallSubsets nodes ZFSet.omega) (M.certificateBasisGraph J nodes N k)).sUnion := by
  apply ZFSet.ext
  intro v
  rw [mem_certificateUsedSupports, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨_, z, F, B, f, edge, member⟩
    have bound := ZFSet.pair_mem_prod.1 (function.1 edge)
    have hB := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 bound.2).2).1
    exact ⟨B, (mem_relationImage _ _ _ _).2
      ⟨hB, z, bound.1, (M.pair_mem_certificateBasisGraph function z B).2 ⟨F, f, edge⟩⟩, member⟩
  · rintro ⟨B, hB, member⟩
    obtain ⟨hB, z, _, edge⟩ := (mem_relationImage _ _ _ _).1 hB
    obtain ⟨F, f, original⟩ := (M.pair_mem_certificateBasisGraph function z B).1 edge
    exact ⟨((M.mem_groundSmallSubsets _ _ _).1 hB).2.1 member, z, F, B, f, original, member⟩

theorem certificateUsedSupports_ground_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J nodes N k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hN : N ∈ M.sets) (hk : k ∈ M.sets)
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k)
    (smallJ : M.groundEmbeddable J ZFSet.omega) :
    certificateUsedSupports nodes k ∈ M.sets ∧
      M.groundEmbeddable (certificateUsedSupports nodes k) ZFSet.omega := by
  have omega := M.omega_mem separation infinite
  have hBases := M.groundSmallSubsets_mem powers separation hNodes omega
  have hGraph := M.certificateBasisGraph_mem pairing unions powers separation hJ hNodes hN omega hk
  have graphFunction := M.certificateBasisGraph_function function
  have hRange := M.relationImage_mem separation hJ hBases hGraph
  have rangeSmall := M.groundEmbeddable_function_image pairing unions powers separation choice
    hJ hBases omega hGraph graphFunction smallJ
  rw [M.certificateUsedSupports_eq_basisUnion function]
  exact ⟨M.union_mem unions hRange,
    M.groundCountable_family_union pairing unions powers separation infinite choice hRange rangeSmall
      (fun B hB => ((M.mem_groundSmallSubsets _ _ _).1
        ((mem_relationImage _ _ _ _).1 hB).1).2.2)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecordedPreparationSupportInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem preparationUsedSupportUnion_ground_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {nodes E events : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (whole : events ∈ M.sets) (function : ZFSet.IsFunc ZFSet.omega E events)
    (certificates : ∀ i event, ZFSet.pair i event ∈ events → event = ∅ ∨
      ∃ alpha r k enumerations J N,
        event = ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations)) ∧
        J ∈ M.sets ∧ N ∈ M.sets ∧ k ∈ M.sets ∧
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k ∧
        M.groundEmbeddable J ZFSet.omega) :
    M.preparationUsedSupportUnion nodes E events ∈ M.sets ∧
      M.groundEmbeddable (M.preparationUsedSupportUnion nodes E events) ZFSet.omega := by
  have omega := M.omega_mem separation infinite
  let g := M.preparationUsedSupportSequence nodes E events
  have grounded := M.preparationUsedSupportSequence_ground_function pairing unions powers separation
    hNodes hE omega whole function
  have valueSmall {i support : ZFSet.{u}} (edge : ZFSet.pair i support ∈ g) :
      M.groundEmbeddable support ZFSet.omega := by
    obtain ⟨event, eventEdge, rfl⟩ :=
      (M.pair_mem_preparationUsedSupportSequence separation hNodes hE function i support).1 edge
    rcases certificates i event eventEdge with idle | active
    · rw [idle, preparationEventUsedSupports_idle]
      exact M.empty_groundEmbeddable ZFSet.omega ⟨nodes, hNodes⟩
    · obtain ⟨alpha, r, k, enumerations, J, N, rfl, hJ, hN, hk, selected, smallJ⟩ := active
      rw [preparationEventUsedSupports_active]
      exact (M.certificateUsedSupports_ground_countable pairing unions powers separation infinite choice
        hJ hNodes hN hk selected smallJ).2
  let bases := M.groundSmallSubsets nodes ZFSet.omega
  have narrowed : ZFSet.IsFunc ZFSet.omega bases g := by
    refine ⟨?_, grounded.2.2⟩
    intro z hz
    obtain ⟨i, hi, support, hs, rfl⟩ := ZFSet.mem_prod.1 (grounded.2.1 hz)
    have fields := (M.mem_groundPower nodes support).1 hs
    exact ZFSet.pair_mem_prod.2 ⟨hi, (M.mem_groundSmallSubsets nodes ZFSet.omega support).2
      ⟨fields.1, fields.2, valueSmall hz⟩⟩
  have equal : relationImage ZFSet.omega (M.groundPower nodes) g =
      relationImage ZFSet.omega bases g := by
    apply ZFSet.ext
    intro support
    rw [mem_relationImage, mem_relationImage]
    constructor
    · rintro ⟨_, i, hi, edge⟩
      exact ⟨(ZFSet.pair_mem_prod.1 (narrowed.1 edge)).2, i, hi, edge⟩
    · rintro ⟨_, i, hi, edge⟩
      exact ⟨(ZFSet.pair_mem_prod.1 (grounded.2.1 edge)).2, i, hi, edge⟩
  change (relationImage ZFSet.omega (M.groundPower nodes) g).sUnion ∈ M.sets ∧
    M.groundEmbeddable (relationImage ZFSet.omega (M.groundPower nodes) g).sUnion ZFSet.omega
  rw [equal]
  exact M.countable_union_of_sequence_graph pairing unions powers separation infinite choice
    (M.groundSmallSubsets_mem powers separation hNodes omega) hNodes grounded.1 narrowed
    (fun B hB => ((M.mem_groundSmallSubsets nodes ZFSet.omega B).1 hB).2.1)
    (fun B hB => ((M.mem_groundSmallSubsets nodes ZFSet.omega B).1 hB).2.2)

theorem mem_preparationUsedSupportUnion
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) (v : ZFSet.{u}) :
    v ∈ M.preparationUsedSupportUnion nodes E events ↔
      v ∈ nodes ∧ ∃ i ∈ ZFSet.omega, ∃ alpha r k enumerations z F B f,
        ZFSet.pair i (ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))) ∈ events ∧
          ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B := by
  rw [preparationUsedSupportUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨support, hs, member⟩
    obtain ⟨_, i, hi, edge⟩ := (mem_relationImage _ _ _ _).1 hs
    obtain ⟨event, eventEdge, rfl⟩ :=
      (M.pair_mem_preparationUsedSupportSequence separation hNodes hE function i support).1 edge
    obtain ⟨hv, alpha, r, k, enumerations, rfl, z, F, B, f, certificate, inside⟩ := ZFSet.mem_sep.1 member
    exact ⟨hv, i, hi, alpha, r, k, enumerations, z, F, B, f, eventEdge, certificate, inside⟩
  · rintro ⟨hv, i, hi, alpha, r, k, enumerations, z, F, B, f, eventEdge, certificate, inside⟩
    let event := ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations))
    let support := preparationEventUsedSupports nodes event
    have edge := (M.pair_mem_preparationUsedSupportSequence separation hNodes hE function i support).2
      ⟨event, eventEdge, rfl⟩
    have hs := (pair_mem_relationCompose _ _ _ _ _ _ _).1 edge |>.2.1
    exact ⟨support, (mem_relationImage _ _ _ _).2 ⟨hs, i, hi, edge⟩,
      ZFSet.mem_sep.2 ⟨hv, alpha, r, k, enumerations, rfl, z, F, B, f, certificate, inside⟩⟩

theorem preparationUsedSupportUnion_subset
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) :
    M.preparationUsedSupportUnion nodes E events ⊆ nodes := by
  intro v member
  exact ((M.mem_preparationUsedSupportUnion separation hNodes hE function v).1 member).1

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFairPreparationEventOrigins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem fairPreparationStep_event_origin
    {omega E0 stages U enumSelector prepSelector grid packed Q order nodes T : ZFSet.{u}}
    (selected : prepSelector ⊆ M.varyingPreparationRelation stages packed Q order nodes T)
    (clock p births last nextClock q nextBirths event : ZFSet.{u})
    (step : FairPreparationStepCode omega E0 stages U enumSelector prepSelector grid
      (ZFSet.pair clock (ZFSet.pair p (ZFSet.pair births last)))
      (ZFSet.pair nextClock (ZFSet.pair q (ZFSet.pair nextBirths event)))) :
    event = ∅ ∨ ∃ alpha ∈ stages, ∃ y ∈ U,
      (∃ payload, y = ZFSet.pair q payload) ∧
      ZFSet.pair (ZFSet.pair alpha p) y ∈
        M.varyingPreparationRelation stages packed Q order nodes T ∧
      event = ZFSet.pair alpha y := by
  obtain ⟨n, p', b, last', m, q', nextBirths', event', source, target, _next,
    i, _hi, j, _hj, e, _he, newE, _hNew, _grid, _old, _selected, _append, branch⟩ := step
  obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 source
  obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
  obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 target
  obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
  rcases branch with idle | active
  · exact Or.inl idle.2.2
  · obtain ⟨alpha, hAlpha, y, hy, shape, _entry, edge, equal⟩ := active
    exact Or.inr ⟨alpha, hAlpha, y, hy, shape, selected edge, equal⟩

theorem fairPreparationEvents_origins
    {Q stages U E0 enumSelector prepSelector grid packed order nodes T orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (selected : prepSelector ⊆ M.varyingPreparationRelation stages packed Q order nodes T)
    (clocks conditions births events : Nat → ZFSet.{u})
    (initialEvent : events 0 = ∅)
    (entries : ∀ k, ZFSet.pair (natSetCode k)
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k)
        (ZFSet.pair (births k) (events k)))) ∈ orbit)
    (steps : ∀ k, FairPreparationStepCode ZFSet.omega E0 stages U
      enumSelector prepSelector grid
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k))))
      (ZFSet.pair (clocks (k + 1))
        (ZFSet.pair (conditions (k + 1)) (ZFSet.pair (births (k + 1)) (events (k + 1))))))
    (i event : ZFSet.{u})
    (edge : ZFSet.pair i event ∈ familyCodeGraph natSetCode events) :
    event = ∅ ∨ ∃ k : Nat, ∃ alpha ∈ stages, ∃ y ∈ U,
      i = natSetCode (k + 1) ∧ conditions k ∈ Q ∧ conditions (k + 1) ∈ Q ∧
      (∃ payload, y = ZFSet.pair (conditions (k + 1)) payload) ∧
      ZFSet.pair (ZFSet.pair alpha (conditions k)) y ∈
        M.varyingPreparationRelation stages packed Q order nodes T ∧
      event = ZFSet.pair alpha y ∧
      ZFSet.pair (natSetCode k)
        (ZFSet.pair (clocks k) (ZFSet.pair (conditions k)
          (ZFSet.pair (births k) (events k)))) ∈ orbit ∧
      ZFSet.pair (natSetCode (k + 1))
        (ZFSet.pair (clocks (k + 1)) (ZFSet.pair (conditions (k + 1))
          (ZFSet.pair (births (k + 1)) (events (k + 1))))) ∈ orbit := by
  have condition_mem (k : Nat) : conditions k ∈ Q := by
    have state := (ZFSet.pair_mem_prod.1 (function.1 (entries k))).2
    have bound := ((M.mem_fairPreparationStates Q stages U E0 enumSelector _).1 state).1
    exact (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 bound).2).1
  obtain ⟨n, equal⟩ := (mem_familyCodeGraph natSetCode events _).1 edge
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  cases n with
  | zero => exact Or.inl initialEvent
  | succ k =>
    rcases M.fairPreparationStep_event_origin selected
      (clocks k) (conditions k) (births k) (events k)
      (clocks (k + 1)) (conditions (k + 1)) (births (k + 1)) (events (k + 1))
      (steps k) with idle | active
    · exact Or.inl idle
    · obtain ⟨alpha, hAlpha, y, hy, shape, relation, eventEq⟩ := active
      exact Or.inr ⟨k, alpha, hAlpha, y, hy, rfl, condition_mem k, condition_mem (k + 1),
        shape, relation, eventEq, entries k, entries (k + 1)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticFairPreparationSupportedLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

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

theorem semanticStructuralFairPreparation_supported_lower_bound_oai
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
        (∀ k, ZFSet.pair (natSetCode k)
          (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k))
            (ZFSet.pair (births k) (events k)))) ∈ orbit) ∧
        familyCodeGraph natSetCode events ∈ M.sets ∧
        ZFSet.IsFunc ZFSet.omega
          (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
          (familyCodeGraph natSetCode events) ∧
        M.preparationUsedSupportUnion b.carrier
          (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
          (familyCodeGraph natSetCode events) ∈ M.sets ∧
        M.preparationUsedSupportUnion b.carrier
          (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
          (familyCodeGraph natSetCode events) ⊆ b.carrier ∧
        M.groundEmbeddable (M.preparationUsedSupportUnion b.carrier
          (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
          (familyCodeGraph natSetCode events)) ZFSet.omega ∧
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
      clockZero, birthZero, eventZero, entries, rawSteps⟩ :=
    M.fairPreparationOrbit_conditionSequence upper pairing unions powers separation
      hQ hs hU hE0 omega whole orbitFunction selected p e initial steps
  have eventGraph := M.fairPreparationEvents_ground_function pairing unions powers separation
    hQ hs hU hE0 omega whole orbitFunction clocks
    (fun k => SetMembers.raw (seq k)) births events entries
  have hEvents := M.insert_mem pairing unions (M.empty_mem ⟨Q, hQ⟩)
    (M.prod_mem pairing unions powers separation hs hU)
  have countableSupports := M.preparationUsedSupportUnion_ground_countable
    pairing unions powers separation infinite choice nodes hEvents eventGraph.1 eventGraph.2 (by
      intro i event edge
      rcases M.fairPreparationEvents_origins orbitFunction prepSelected clocks
          (fun k => SetMembers.raw (seq k)) births events eventZero entries rawSteps i event edge with
        idle | active
      · exact Or.inl idle
      · obtain ⟨j, alpha, hAlpha, y, _hy, _index, _source, _target, _shape,
          relation, eventEq, _oldEntry, _newEntry⟩ := active
        obtain ⟨r, k, enumerations, J, N, yCode, _nameBound, hJ, hN, hk, _hEnum,
            smallJ, kFunction, _enumFunction⟩ :=
          M.semanticStructuralPrefix_preparationEvent_certificate_domain c a t b d base directed
            T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
            group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
            closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha
            infinite choice relation
        exact Or.inr ⟨alpha, r, k, enumerations, J, N,
          eventEq.trans (congrArg (ZFSet.pair alpha) yCode), hJ, hN, hk, kFunction, smallJ⟩)
  have supportsSubset := M.preparationUsedSupportUnion_subset separation nodes hEvents eventGraph.2
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
    entries, eventGraph.1, eventGraph.2, countableSupports.1, supportsSubset, countableSupports.2,
    rawSteps, limit, below, dataEqual, unionGround, exactEntries, ?_⟩
  intro x member
  exact M.fairRefinementSequence_assignment_prepared c T stages packed run.carriers.data
    enumFunction enumSelected seq decreasing clocks births events e initialChosen clockZero birthZero
    rawSteps x (dataEqual ▸ member)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralFairPreparation_supported_lower_bound_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralFairPreparation_supported_lower_bound_oai.{u}
