-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:26:39.521427+00:00
-- url     : https://prove2.me/submissions/4d35fe86-7756-41d4-957b-578671b78b9c

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainCandidateLevel_exists_groundConditionalPrefixFunction
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_exists_initialRecursionSeed
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_omegaOne_taskBearingSuccessor_total

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SetRankBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) {x y : ZFSet.{u}}
include limit

theorem rank_singleton_lt (hx : ZFSet.rank x < o) : ZFSet.rank {x} < o := by
  rw [ZFSet.rank_singleton]
  exact limit.succ_lt hx

theorem rank_unorderedPair_lt (hx : ZFSet.rank x < o) (hy : ZFSet.rank y < o) :
    ZFSet.rank {x, y} < o := by
  rw [ZFSet.rank_pair]
  exact max_lt (limit.succ_lt hx) (limit.succ_lt hy)

theorem rank_orderedPair_lt (hx : ZFSet.rank x < o) (hy : ZFSet.rank y < o) :
    ZFSet.rank (ZFSet.pair x y) < o :=
  rank_unorderedPair_lt limit (rank_singleton_lt limit hx) (rank_unorderedPair_lt limit hx hy)

end PartitionPilot.SetRealization

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NatUnionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

theorem functionGraphOn_sUnion {A W : ZFSet.{u}}
    (shape : ∀ f ∈ W, ∃ B, B ⊆ A ∧ FunctionGraphOn B f)
    (cover : ∀ x ∈ A, ∃ f ∈ W, ∃ y, ZFSet.pair x y ∈ f)
    (agree : ∀ f ∈ W, ∀ g ∈ W, ∀ x y z,
      ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z) :
    FunctionGraphOn A (⋃₀ W) := by
  refine ⟨⋃₀ ⋃₀ (⋃₀ W), ?_, ?_⟩
  · intro z hz
    obtain ⟨f, hf, entry⟩ := ZFSet.mem_sUnion.1 hz
    obtain ⟨B, subset, func⟩ := shape f hf
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (func.to_isFunc.1 entry)
    exact ZFSet.pair_mem_prod.2 ⟨subset hx, pair_second_mem_doubleUnion hz⟩
  · intro x hx
    obtain ⟨f, hf, y, entry⟩ := cover x hx
    refine ⟨y, ZFSet.mem_sUnion.2 ⟨f, hf, entry⟩, ?_⟩
    intro z hz
    obtain ⟨g, hg, rel⟩ := ZFSet.mem_sUnion.1 hz
    exact agree g hg f hf x z y rel entry

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_OrdinalRecursionTraces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open scoped ZFSet
universe u

namespace OrdinalRecursionTrace

variable {R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}

theorem restriction_eq_of_common_values {A B C f g : ZFSet.{u}}
    (first : FunctionGraphOn A f) (second : FunctionGraphOn B g)
    (left : C ⊆ A) (right : C ⊆ B)
    (agree : ∀ x ∈ C, ∀ y z, ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z) :
    graphRestriction C f = graphRestriction C g := by
  apply ZFSet.ext
  intro w
  constructor
  · intro hw
    obtain ⟨V, function⟩ := first.restrict left
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 hw)
    obtain ⟨xy, hx⟩ := pair_mem_graphRestriction.1 hw
    obtain ⟨z, xz⟩ := second.total (right hx)
    exact pair_mem_graphRestriction.2 ⟨agree x hx y z xy xz ▸ xz, hx⟩
  · intro hw
    obtain ⟨V, function⟩ := second.restrict right
    obtain ⟨x, _, z, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 hw)
    obtain ⟨xz, hx⟩ := pair_mem_graphRestriction.1 hw
    obtain ⟨y, xy⟩ := first.total (left hx)
    exact pair_mem_graphRestriction.2 ⟨agree x hx y z xy xz ▸ xy, hx⟩

theorem overlap {A B T f g : ZFSet.{u}}
    (first : OrdinalRecursionTrace R A f) (second : OrdinalRecursionTrace R B g)
    (ordinalA : ordinalSetProperty A) (ordinalB : ordinalSetProperty B)
    (left : A ⊆ T) (_right : B ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z) :
    ∀ β ∈ A, β ∈ B → ∀ y z, ZFSet.pair β y ∈ f → ZFSet.pair β z ∈ g → y = z := by
  intro β
  induction β using ZFSet.inductionOn with
  | h β ih =>
    intro hβA hβB y z hy hz
    have beforeA : β ⊆ A := fun x hx => ordinalA.1 β hβA x hx
    have beforeB : β ⊆ B := fun x hx => ordinalB.1 β hβB x hx
    have prefixes : graphRestriction β f = graphRestriction β g :=
      restriction_eq_of_common_values first.1 second.1 beforeA beforeB
        (fun x hx a b xa xb => ih x hx (beforeA hx) (beforeB hx) a b xa xb)
    have prefixTrace := first.restrict (ordinalSetProperty_member ordinalA hβA) beforeA
    have firstStep := first.2 β hβA y hy
    have secondStep := second.2 β hβB z hz
    rw [← prefixes] at secondStep
    exact stepUnique β (left hβA) (graphRestriction β f) prefixTrace y z firstStep secondStep

theorem unique {A T f g : ZFSet.{u}}
    (first : OrdinalRecursionTrace R A f) (second : OrdinalRecursionTrace R A g)
    (ordinalA : ordinalSetProperty A) (subset : A ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z) : f = g := by
  have eq := restriction_eq_of_common_values first.1 second.1 (fun _ hx => hx) (fun _ hx => hx)
    (fun x hx y z xy xz => first.overlap second ordinalA ordinalA subset subset stepUnique x hx hx y z xy xz)
  simpa only [first.1.restriction_eq, second.1.restriction_eq] using eq

theorem restriction_insert_last {A B f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (subset : B ⊆ A) (y : ZFSet.{u}) :
    graphRestriction B (insert (ZFSet.pair A y) f) = graphRestriction B f := by
  apply restriction_eq_of_common_values (function.insert (ZFSet.mem_irrefl A) y) function
    (fun _ hx => ZFSet.mem_insert_of_mem A (subset hx)) subset
  intro x hx z w xz xw
  rcases ZFSet.mem_insert_iff.1 xz with eq | xz
  · have same : x = A := (ZFSet.pair_inj.1 eq).1
    exact False.elim (ZFSet.mem_irrefl A (same ▸ subset hx))
  · exact function.unique xz xw

theorem succ {A f y : ZFSet.{u}} (trace : OrdinalRecursionTrace R A f)
    (ordinalA : ordinalSetProperty A) (step : R A f y) :
    OrdinalRecursionTrace R (insert A A) (insert (ZFSet.pair A y) f) := by
  refine ⟨trace.1.insert (ZFSet.mem_irrefl A) y, ?_⟩
  intro β hβ z hz
  rcases ZFSet.mem_insert_iff.1 hβ with eq | hβ
  · subst β
    have value : z = y := (trace.1.insert (ZFSet.mem_irrefl A) y).unique hz
      (ZFSet.mem_insert _ _)
    rw [restriction_insert_last trace.1 (fun _ hx => hx) y, trace.1.restriction_eq, value]
    exact step
  · rw [restriction_insert_last trace.1 (fun x hx => ordinalA.1 β hβ x hx) y]
    rcases ZFSet.mem_insert_iff.1 hz with eq | hz
    · have same : β = A := (ZFSet.pair_inj.1 eq).1
      exact False.elim (ZFSet.mem_irrefl A (same ▸ hβ))
    · exact trace.2 β hβ z hz

theorem sUnion {A T W : ZFSet.{u}} (subset : A ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z)
    (members : ∀ f ∈ W, ∃ B, ordinalSetProperty B ∧ B ⊆ A ∧ OrdinalRecursionTrace R B f)
    (cover : ∀ β ∈ A, ∃ f ∈ W, ∃ y, ZFSet.pair β y ∈ f) :
    OrdinalRecursionTrace R A (⋃₀ W) := by
  have agree : ∀ f ∈ W, ∀ g ∈ W, ∀ x y z,
      ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z := by
    intro f hf g hg x y z xy xz
    obtain ⟨B, ordinalB, boundB, first⟩ := members f hf
    obtain ⟨C, ordinalC, boundC, second⟩ := members g hg
    exact first.overlap second ordinalB ordinalC (fun _ hx => subset (boundB hx))
      (fun _ hx => subset (boundC hx)) stepUnique x
      (first.1.pair_source xy) (second.1.pair_source xz) y z xy xz
  have function : FunctionGraphOn A (⋃₀ W) := functionGraphOn_sUnion
    (fun f hf => by
      obtain ⟨B, _, bound, trace⟩ := members f hf
      exact ⟨B, bound, trace.1⟩) cover agree
  refine ⟨function, ?_⟩
  intro β _ y hy
  obtain ⟨f, hf, βy⟩ := ZFSet.mem_sUnion.1 hy
  obtain ⟨B, ordinalB, boundB, trace⟩ := members f hf
  have βB := trace.1.pair_source βy
  have beforeB : β ⊆ B := fun x hx => ordinalB.1 β βB x hx
  have prefixes : graphRestriction β (⋃₀ W) = graphRestriction β f := by
    apply restriction_eq_of_common_values function trace.1 (fun _ hx => boundB (beforeB hx)) beforeB
    intro x _ z w xz xw
    obtain ⟨g, hg, xz⟩ := ZFSet.mem_sUnion.1 xz
    exact agree g hg f hf x z w xz xw
  rw [prefixes]
  exact trace.2 β βB y βy

theorem sUnion_successors {A T W : ZFSet.{u}} (ordinalA : ordinalSetProperty A)
    (subset : A ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z)
    (members : ∀ f ∈ W, ∃ β ∈ A, OrdinalRecursionTrace R (insert β β) f)
    (cover : ∀ β ∈ A, ∃ f ∈ W, OrdinalRecursionTrace R (insert β β) f) :
    OrdinalRecursionTrace R A (⋃₀ W) := by
  apply sUnion subset stepUnique
  · intro f hf
    obtain ⟨β, hβ, trace⟩ := members f hf
    refine ⟨insert β β, ordinalSetProperty_succ (ordinalSetProperty_member ordinalA hβ), ?_, trace⟩
    intro x hx
    exact (ZFSet.mem_insert_iff.1 hx).elim (fun eq => eq ▸ hβ) (fun hx => ordinalA.1 β hβ x hx)
  · intro β hβ
    obtain ⟨f, hf, trace⟩ := cover β hβ
    obtain ⟨y, βy⟩ := trace.1.total (ZFSet.mem_insert β β)
    exact ⟨f, hf, y, βy⟩

end OrdinalRecursionTrace

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PresentedGroupCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_graphFiberInclusionFormula {n} (x y f g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (graphFiberInclusionFormula x y f g) env ↔
      ∀ z, ZFSet.pair (env x) z ∈ env f → ZFSet.pair (env y) z ∈ env g := by
  simp only [graphFiberInclusionFormula, Truth, truth_imp,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  change (∀ p ∈ env f, ∀ a ∈ p, ∀ z ∈ a,
    p = ZFSet.pair (env x) z → ZFSet.pair (env y) z ∈ env g) ↔ _
  constructor
  · intro h z entry
    exact h (ZFSet.pair (env x) z) entry {env x, z}
      (ZFSet.mem_pair.2 (Or.inr rfl)) z (ZFSet.mem_pair.2 (Or.inr rfl)) rfl
  · intro h p hp a _ z _ equal
    exact h z (equal ▸ hp)

theorem truth_graphFiberEqualityFormula {n} (x y f g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (graphFiberEqualityFormula x y f g) env ↔
      ∀ z, ZFSet.pair (env x) z ∈ env f ↔ ZFSet.pair (env y) z ∈ env g := by
  simp only [graphFiberEqualityFormula, Truth, truth_graphFiberInclusionFormula]
  exact ⟨fun h z => ⟨h.1 z, h.2 z⟩, fun h => ⟨fun z => (h z).1, fun z => (h z).2⟩⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_relationOnFormula {n} (c r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (relationOnFormula c r) env ↔ env r ⊆ ZFSet.prod (env c) (env c) := by
  simp only [relationOnFormula, Truth, truth_exMem, truth_orderedPairFormula]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ZFSet.mem_prod.symm))

theorem truth_partialOrderFormula {n} (c r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (partialOrderFormula c r) env ↔ PartialOrderCode (env c) (env r) := by
  simp only [partialOrderFormula, Truth, truth_relationOnFormula, reflexiveFormula,
    antisymmetricFormula, transitiveFormula, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨shape, refl, antisymm, trans⟩
    exact ⟨shape, refl, fun x hx y hy xy yx => antisymm x hx y hy ⟨xy, yx⟩,
      fun x hx y hy z hz xy yz => trans x hx y hy z hz ⟨xy, yz⟩⟩
  · intro h
    exact ⟨h.relation, h.refl, fun x hx y hy ⟨xy, yx⟩ => h.antisymm x hx y hy xy yx,
      fun x hx y hy z hz ⟨xy, yz⟩ => h.trans x hx y hy z hz xy yz⟩

theorem truth_topFormula {n} (c r t : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (topFormula c r t) env ↔ env t ∈ env c ∧ ∀ x ∈ env c, ZFSet.pair x (env t) ∈ env r := by
  simp only [topFormula, Truth, truth_pairMembershipFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_binaryRelationFormula {n} (g f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (binaryRelationFormula g f) env ↔
      env f ⊆ ZFSet.prod (ZFSet.prod (env g) (env g)) (env g) := by
  simp only [binaryRelationFormula, Truth, truth_exMem, truth_orderedTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, y, hy, z, hz, eq⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨ZFSet.pair x y, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, z, hz, eq⟩
  · intro h w hw
    obtain ⟨xy, hxy, z, hz, eq⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact ⟨x, hx, y, hy, z, hz, eq⟩

theorem truth_binaryFunctionFormula {n} (g f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (binaryFunctionFormula g f) env ↔
      ZFSet.IsFunc (ZFSet.prod (env g) (env g)) (env g) (env f) := by
  simp only [binaryFunctionFormula, Truth, truth_binaryRelationFormula, truth_exMem,
    truth_tripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro xy hxy
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    obtain ⟨z, _, rel, unique⟩ := total x hx y hy
    refine ⟨z, rel, ?_⟩
    intro w hw
    exact unique w (ZFSet.pair_mem_prod.1 (shape hw)).2 hw
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx y hy
    obtain ⟨z, rel, unique⟩ := total (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    exact ⟨z, (ZFSet.pair_mem_prod.1 (shape rel)).2, rel, fun w _ hw => unique w hw⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_groupFormula {n} (g m i e : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (groupFormula g m i e) env ↔ GroupCode (env g) (env m) (env i) (env e) := by
  simp only [groupFormula, Truth, truth_binaryFunctionFormula, truth_functionFormula,
    groupIdentityFormula, groupInverseFormula, groupAssociativeFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨mul, inv, one, identity, inverse, assoc⟩
    exact ⟨mul, inv, one, fun x hx => (identity x hx).1,
      fun x hx => (identity x hx).2, inverse,
      fun x hx y hy z hz a ha b hb c hc xy yz az => assoc x hx y hy z hz a ha b hb c hc ⟨xy, yz, az⟩⟩
  · intro h
    exact ⟨h.mul_function, h.inv_function, h.identity_mem,
      fun x hx => ⟨h.one_mul x hx, h.mul_one x hx⟩, h.inv_mul,
      fun x hx y hy z hz a ha b hb c hc ⟨xy, yz, az⟩ => h.mul_assoc x hx y hy z hz a ha b hb c hc xy yz az⟩

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFlatCopyGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

theorem functionGraphRange_rank_le (A f : ZFSet.{u}) :
    ZFSet.rank (functionGraphRange A f) ≤ ZFSet.rank f := by
  have subset : functionGraphRange A f ⊆ ⋃₀ ⋃₀ f :=
    fun _ hy => (mem_relationImage _ _ _ _).1 hy |>.1
  exact (ZFSet.rank_mono subset).trans
    ((ZFSet.rank_sUnion_le (⋃₀ f)).trans (ZFSet.rank_sUnion_le f))

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPairCompositions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing

universe u v w

theorem literalTaskField_map {α : Type v} {β : Type w} (f : α → β)
    (a c ell e F label : α) (j : Fin 6) :
    f (literalTaskField a c ell e F label j) =
      literalTaskField (f a) (f c) (f ell) (f e) (f F) (f label) j := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun i => Fin.elim0 i)))))) j <;> rfl

namespace BoundedFormula

open SetFormula

theorem truth_literalTaskFormula {n} (z a c ell e F label : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (literalTaskFormula z a c ell e F label) env ↔
      env z = literalTaskCode (env a) (env c) (env ell) (env e) (env F) (env label) := by
  simp only [literalTaskFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ u ∈ env z, ∃ v ∈ u, env z = ZFSet.pair (env a) v ∧
    ∃ u' ∈ v, ∃ v' ∈ u', v = ZFSet.pair (env c) v' ∧
    ∃ u'' ∈ v', ∃ v'' ∈ u'', v' = ZFSet.pair (env ell) v'' ∧
    ∃ u''' ∈ v'', ∃ v''' ∈ u''', v'' = ZFSet.pair (env e) v''' ∧
      v''' = ZFSet.pair (env F) (env label)) ↔ _
  constructor
  · rintro ⟨_, _, v, _, outer, _, _, v', _, second, _, _, v'', _, third,
      _, _, v''', _, fourth, last⟩
    rw [outer, second, third, fourth, last]
    rfl
  · intro equal
    let v''' := ZFSet.pair (env F) (env label)
    let v'' := ZFSet.pair (env e) v'''
    let v' := ZFSet.pair (env ell) v''
    let v := ZFSet.pair (env c) v'
    have outer : env z = ZFSet.pair (env a) v := equal
    refine ⟨{env a, v}, ?_, v, ZFSet.mem_pair.2 (Or.inr rfl), outer,
      {env c, v'}, ZFSet.mem_pair.2 (Or.inr rfl), v', ZFSet.mem_pair.2 (Or.inr rfl), rfl,
      {env ell, v''}, ZFSet.mem_pair.2 (Or.inr rfl), v'', ZFSet.mem_pair.2 (Or.inr rfl), rfl,
      {env e, v'''}, ZFSet.mem_pair.2 (Or.inr rfl), v''', ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl⟩
    rw [outer]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

theorem truth_literalTaskFieldEntryFormula {n} (j : Fin 6) (z I P R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (literalTaskFieldEntryFormula j z I P R U Labels) env ↔
      ∃ i ∈ env I, ∃ a ∈ env P, ∃ c ∈ env P, ∃ ell ∈ env R, ∃ e ∈ env P,
        ∃ F ∈ env U, ∃ label ∈ env Labels,
          env z = ZFSet.pair i (literalTaskField a c ell e F label j) ∧
            i = literalTaskCode a c ell e F label := by
  simp only [literalTaskFieldEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_literalTaskFormula]
  simp only [literalTaskField_map]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ParentSupportCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_relationToProductFormula {n} (a c q f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relationToProductFormula a c q f) env ↔
      env f ⊆ ZFSet.prod (env a) (ZFSet.prod (env c) (env q)) := by
  simp only [relationToProductFormula, Truth, truth_exMem, truth_orderedRightTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, d, hd, v, hv, equal⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨x, hx, ZFSet.pair d v, ZFSet.pair_mem_prod.2 ⟨hd, hv⟩, equal⟩
  · intro h w hw
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 hy
    exact ⟨x, hx, d, hd, v, hv, equal⟩

theorem truth_functionToProductFormula {n} (a c q f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (functionToProductFormula a c q f) env ↔
      ZFSet.IsFunc (env a) (ZFSet.prod (env c) (env q)) (env f) := by
  simp only [functionToProductFormula, Truth, truth_relationToProductFormula, truth_exMem,
    truth_rightTripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨d, _, v, _, entry, unique⟩ := total x hx
    refine ⟨ZFSet.pair d v, entry, ?_⟩
    intro y hy
    obtain ⟨b, hb, z, hz, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (shape hy)).2
    have both : b = d ∧ z = v := unique b hb z hz hy
    obtain ⟨rfl, rfl⟩ := both
    rfl
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨y, entry, unique⟩ := total x hx
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (shape entry)).2
    refine ⟨d, hd, v, hv, entry, ?_⟩
    intro b _ z _ hz
    exact ZFSet.pair_injective (unique _ hz)

end PartitionPilot.Forcing.BoundedFormula



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MapFamilyApplicationGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



open SetFormula
universe u

theorem pair_mem_mapFamilyApplicationGraph (I P Q family i x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i x) y ∈ mapFamilyApplicationGraph I P Q family ↔
      i ∈ I ∧ x ∈ P ∧ y ∈ Q ∧ ∃ f, ZFSet.pair i f ∈ family ∧ ZFSet.pair x y ∈ f := by
  rw [mapFamilyApplicationGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, a, ha, b, hb, f, _, equal, indexed, entry⟩
    obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    exact ⟨hj, ha, hb, f, indexed, entry⟩
  · rintro ⟨hi, hx, hy, f, indexed, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy⟩,
      i, hi, x, hx, y, hy, f, pair_second_mem_doubleUnion indexed, rfl, indexed, entry⟩

namespace BoundedFormula

theorem truth_mapFamilyApplicationEntryFormula {n} (z I P Q B family : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mapFamilyApplicationEntryFormula z I P Q B family) env ↔
      ∃ i ∈ env I, ∃ x ∈ env P, ∃ y ∈ env Q, ∃ f ∈ env B,
        env z = ZFSet.pair (ZFSet.pair i x) y ∧
          ZFSet.pair i f ∈ env family ∧ ZFSet.pair x y ∈ f := by
  simp only [mapFamilyApplicationEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mapFamilyApplicationGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Q family : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQ : Q ∈ M.sets) (hFamily : family ∈ M.sets) :
    mapFamilyApplicationGraph I P Q family ∈ M.sets := by
  have hB := M.union_mem unions (M.union_mem unions hFamily)
  let params := extend I (extend P (extend Q (extend (ZFSet.sUnion (ZFSet.sUnion family)) (extend family Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.mapFamilyApplicationEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hP (Fin.cases hQ (Fin.cases hB (Fin.cases hFamily
      (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hI hP) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.mapFamilyApplicationEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod I P) Q) = mapFamilyApplicationGraph I P Q family := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mapFamilyApplicationGraph, ZFSet.mem_sep,
      BoundedFormula.truth_mapFamilyApplicationEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyPairs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace BoundedFormula

theorem truth_chronologyPairsEquationFormula {n} (J T : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyPairsEquationFormula J T) env ↔ env J = chronologyPairs (env T) := by
  simp only [chronologyPairsEquationFormula, Truth, truth_chronologyPairFormula,
    truth_imp, truth_disj, truth_pairMembershipFormula]
  change ((∀ z ∈ env J, z ∈ chronologyPairs (env T)) ∧
    ∀ s ∈ env T, ∀ t ∈ env T, (t = s ∨ t ∈ s) → ZFSet.pair s t ∈ env J) ↔ _
  constructor
  · rintro ⟨subset, cover⟩
    apply ZFSet.ext
    intro z
    refine ⟨subset z, ?_⟩
    intro hz
    obtain ⟨s, hs, t, ht, rfl, before⟩ := (mem_chronologyPairs (env T) z).1 hz
    exact cover s hs t ht before
  · intro equal
    rw [equal]
    exact ⟨fun _ hz => hz, fun s hs t ht before =>
      (pair_mem_chronologyPairs (env T) s t).2 ⟨hs, ht, before⟩⟩

theorem realize_chronologyPairsEquationFormula (M : TransitiveGround.{u}) {n}
    (J T : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyPairsEquationFormula J T).toFormula env ↔ env J = chronologyPairs (env T) :=
  (realize_toFormula M _ env members).trans (truth_chronologyPairsEquationFormula J T env)

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SeparationFulfillmentCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula
universe u

theorem truth_productRelationFormula {n} (a b c f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productRelationFormula a b c f) env ↔
      env f ⊆ ZFSet.prod (ZFSet.prod (env a) (env b)) (env c) := by
  simp only [productRelationFormula, Truth, truth_exMem, truth_orderedTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, y, hy, z, hz, eq⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨ZFSet.pair x y, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, z, hz, eq⟩
  · intro h w hw
    obtain ⟨xy, hxy, z, hz, eq⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact ⟨x, hx, y, hy, z, hz, eq⟩

theorem truth_productFunctionFormula {n} (a b c f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productFunctionFormula a b c f) env ↔
      ZFSet.IsFunc (ZFSet.prod (env a) (env b)) (env c) (env f) := by
  simp only [productFunctionFormula, Truth, truth_productRelationFormula, truth_exMem,
    truth_tripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro xy hxy
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    obtain ⟨z, _, rel, unique⟩ := total x hx y hy
    exact ⟨z, rel, fun w hw => unique w (ZFSet.pair_mem_prod.1 (shape hw)).2 hw⟩
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx y hy
    obtain ⟨z, rel, unique⟩ := total (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    exact ⟨z, (ZFSet.pair_mem_prod.1 (shape rel)).2, rel, fun w _ hw => unique w hw⟩

end BoundedFormula




universe u

namespace BoundedFormula

open SetFormula

theorem truth_posetActionFormula {n} (g p m e r a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (posetActionFormula g p m e r a) env ↔
      PosetActionCode (env g) (env p) (env m) (env e) (env r) (env a) := by
  simp only [posetActionFormula, Truth, truth_productFunctionFormula, actionOneFormula,
    actionMulFormula, actionMonotoneFormula, truth_tripleMembershipFormula,
    truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨function, one, mul, monotone⟩
    exact ⟨function, one,
      fun g hg h hh k hk p hp q hq r hr gh hpq gr => mul g hg h hh k hk p hp q hq r hr ⟨gh, hpq, gr⟩,
      fun g hg p hp q hq r hr s hs gr gs pq => monotone g hg p hp q hq r hr s hs ⟨gr, gs, pq⟩⟩
  · intro h
    exact ⟨h.function, h.one,
      fun g hg j hj k hk p hp q hq r hr ⟨gj, jq, gr⟩ => h.mul g hg j hj k hk p hp q hq r hr gj jq gr,
      fun g hg p hp q hq r hr s hs ⟨gr, gs, pq⟩ => h.monotone g hg p hp q hq r hr s hs gr gs pq⟩

end BoundedFormula

namespace BoundedFormula

theorem truth_separationActorFormula {n} (P r Q R ν A e W k : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (separationActorFormula P r Q R ν A e W k) env ↔
      SeparationActorCode (env P) (env r) (env Q) (env R) (env ν) (env A) (env e) (env W) (env k) := by
  simp only [separationActorFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

theorem truth_separationFulfillmentFormula {n} (P r Q R ν H A e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (separationFulfillmentFormula P r Q R ν H A e) env ↔
      SeparationFulfillmentCode (env P) (env r) (env Q) (env R) (env ν) (env H) (env A) (env e) := by
  simp only [separationFulfillmentFormula, Truth, truth_exMem, truth_separationActorFormula]
  rfl

end BoundedFormula


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLiteralTaskFieldRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem literalTaskBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P R U Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) : literalTaskBound P R U Labels ∈ M.sets :=
  M.prod_mem pairing unions powers separation hP
    (M.prod_mem pairing unions powers separation hP
      (M.prod_mem pairing unions powers separation hR
        (M.prod_mem pairing unions powers separation hP
          (M.prod_mem pairing unions powers separation hU hLabels))))

theorem literalTaskFieldBound_mem
    {P R U Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) (j : Fin 6) :
    literalTaskFieldBound P R U Labels j ∈ M.sets :=
  Fin.cases hP (Fin.cases hP (Fin.cases hR (Fin.cases hP
    (Fin.cases hU (Fin.cases hLabels (fun i => Fin.elim0 i)))))) j

theorem literalTaskFieldGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P R U Labels : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) (j : Fin 6) :
    literalTaskFieldGraph I P R U Labels j ∈ M.sets := by
  let params := extend I (extend P (extend R (extend U (extend Labels Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.literalTaskFieldEntryFormula j 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hP (Fin.cases hR (Fin.cases hU (Fin.cases hLabels
      (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hI
      (M.literalTaskFieldBound_mem hP hR hU hLabels j))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.literalTaskFieldEntryFormula j 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod I (literalTaskFieldBound P R U Labels j)) =
      literalTaskFieldGraph I P R U Labels j := by
    apply ZFSet.ext
    intro z
    rw [literalTaskFieldGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_literalTaskFieldEntryFormula j 0 1 2 3 4 5 _)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_literalTaskFieldSetFormula {n} (j : Fin 6) (output I P R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (literalTaskFieldSetFormula j output I P R U Labels) env ↔
      env output = literalTaskFieldGraph (env I) (env P) (env R) (env U) (env Labels) j := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => M.transitive (M.literalTaskFieldGraph_mem pairing unions powers separation
      (members I) (members P) (members R) (members U) (members Labels) j) hz)
  intro z hz
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
    BoundedFormula.truth_literalTaskFieldEntryFormula]
  exact (mem_literalTaskFieldGraph _ _ _ _ _ _ j).symm

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_FiniteFamilyRankBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot
universe u
namespace SetRealization

theorem rank_functionGraph_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {A B f : ZFSet.{u}} (function : ZFSet.IsFunc A B f)
    (source : ZFSet.rank A < o) (target : ZFSet.rank B < o) :
    ZFSet.rank f < o :=
  (ZFSet.rank_mono function.1).trans_lt (rank_product_lt limit source target)

end SetRealization

namespace Forcing
open SetRealization

theorem rank_nonemptyTupleCode_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (k : Nat) (fields : Fin (k + 1) → ZFSet.{u}) (bounds : ∀ j, ZFSet.rank (fields j) < o) :
    ZFSet.rank (nonemptyTupleCode k fields) < o := by
  induction k with
  | zero => exact bounds 0
  | succ k ih => exact rank_orderedPair_lt limit (bounds 0) (ih _ (fun j => bounds j.succ))

end Forcing
end PartitionPilot



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem rank_finiteRange_lt (n : Nat) (f : Fin n → ZFSet.{u})
    (bounds : ∀ i, ZFSet.rank (f i) < o) : ZFSet.rank (ZFSet.range f) < o := by
  induction n with
  | zero =>
    have empty : ZFSet.range f = ∅ := by
      apply ZFSet.ext
      intro x
      rw [ZFSet.mem_range]
      exact ⟨fun ⟨i, _⟩ => Fin.elim0 i, fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    simpa only [empty, ZFSet.rank_empty] using limit.pos
  | succ n ih =>
    have split : ZFSet.range f = insert (f 0) (ZFSet.range (fun i : Fin n => f i.succ)) := by
      apply ZFSet.ext
      intro x
      rw [ZFSet.mem_range, ZFSet.mem_insert_iff, ZFSet.mem_range]
      constructor
      · rintro ⟨i, equal⟩
        exact Fin.cases (fun h => Or.inl h.symm) (fun j h => Or.inr ⟨j, h⟩) i equal
      · rintro (equal | ⟨i, equal⟩)
        · exact ⟨0, equal.symm⟩
        · exact ⟨i.succ, equal⟩
    rw [split, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (bounds 0)) (ih _ (fun i => bounds i.succ))

end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBelowFunctionGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundBelowFormula {n} (a k : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (groundBelowFormula a k) env ↔ GroundBelow M (env a) (env k) := by
  rw [groundBelowFormula, realize_ex]
  constructor
  · rintro ⟨β, hβ, bound, witness⟩
    exact ⟨β, bound, (M.realize_hasInjectionFormula a.succ 0 (extend β env)
      (Fin.cases hβ members)).1 witness⟩
  · rintro ⟨β, bound, witness⟩
    have hβ := M.transitive (members k) bound
    exact ⟨β, hβ, bound, (M.realize_hasInjectionFormula a.succ 0 (extend β env)
      (Fin.cases hβ members)).2 witness⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

open scoped ZFSet

theorem pair_mem_functionSourceProjection (A f z x : ZFSet.{u}) :
    ZFSet.pair z x ∈ functionSourceProjection A f ↔
      z ∈ f ∧ x ∈ A ∧ ∃ y, z = ZFSet.pair x y := by
  rw [functionSourceProjection, pair_mem_graphRestriction, mem_productFirst]
  constructor
  · rintro ⟨⟨a, ha, b, _, equal⟩, hz⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hz, ha, b, rfl⟩
  · rintro ⟨hz, hx, y, rfl⟩
    exact ⟨⟨x, hx, y, pair_second_mem_doubleUnion hz, rfl⟩, hz⟩

theorem functionSourceProjection_injection {A f : ZFSet.{u}}
    (function : FunctionGraphOn A f) : InjectionCode f A (functionSourceProjection A f) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨z, hz, x, rfl, entry⟩ := mem_graphRestriction.1 hp
    have hx := (ZFSet.pair_mem_prod.1 ((productFirst_function A (⋃₀ ⋃₀ f)).1 entry)).2
    exact ZFSet.pair_mem_prod.2 ⟨hz, hx⟩
  · intro z hz
    obtain ⟨x, hx, y, rfl⟩ := function.shape z hz
    refine ⟨x, (pair_mem_functionSourceProjection _ _ _ _).2 ⟨hz, hx, y, rfl⟩, ?_⟩
    intro a entry
    obtain ⟨_, _, b, equal⟩ := (pair_mem_functionSourceProjection _ _ _ _).1 entry
    exact (ZFSet.pair_inj.1 equal).1.symm
  · intro z w x first second
    obtain ⟨hz, _, y, rfl⟩ := (pair_mem_functionSourceProjection _ _ _ _).1 first
    obtain ⟨hw, _, b, rfl⟩ := (pair_mem_functionSourceProjection _ _ _ _).1 second
    exact congrArg (ZFSet.pair x) (function.unique hz hw)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem functionSourceProjection_mem {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) : functionSourceProjection A f ∈ M.sets :=
  M.graphRestriction_mem unions separation hf (M.productFirst_mem pairing unions powers separation
    hA (M.union_mem unions (M.union_mem unions hf)))

theorem functionGraph_embeds_source {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn A f) :
    M.groundEmbeddable f A :=
  ⟨functionSourceProjection A f, M.functionSourceProjection_mem pairing unions powers separation hA hf,
    functionSourceProjection_injection function⟩

end TransitiveGround

namespace GroundBelow
variable {M : TransitiveGround.{u}} {A B f K : ZFSet.{u}}

theorem functionGraphOn (small : GroundBelow M A K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) (hK : K ∈ M.sets)
    (function : FunctionGraphOn A f) : GroundBelow M f K :=
  small.of_embeddable pairing unions powers separation hf hA hK
    (M.functionGraph_embeds_source pairing unions powers separation hA hf function)

end GroundBelow

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCoinitialOperations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem mem_copyPullback (A L e F x : ZFSet.{u}) :
    x ∈ copyPullback A L e F ↔
      x ∈ A ∧ ∃ y ∈ F, y ∈ L ∧ ZFSet.pair x y ∈ e := by
  rw [copyPullback, mem_relationImage]
  constructor
  · rintro ⟨hx, y, hy, rel⟩
    exact ⟨hx, y, hy, ((pair_mem_relationConverse A L e x y).1 rel).2⟩
  · rintro ⟨hx, y, hy, hyL, rel⟩
    exact ⟨hx, y, hy, (pair_mem_relationConverse A L e x y).2 ⟨hx, hyL, rel⟩⟩

theorem relationImage_copyPullback {A L e : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e) (F : ZFSet.{u}) :
    relationImage (copyPullback A L e F) L e = F ∩ relationImage A L e := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, ZFSet.mem_inter, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, rel⟩
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    have equal : y = z := (unique y rel).trans (unique z relz).symm
    exact ⟨equal ▸ hz, hy, x, hxA, rel⟩
  · rintro ⟨hyF, hy, x, hx, rel⟩
    exact ⟨hy, x, (mem_copyPullback A L e F x).2 ⟨hx, y, hyF, hy, rel⟩, rel⟩

theorem CoinitialBelowCode.copy {A L e sourceOrder targetOrder F target B : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : CoinitialBelowCode sourceOrder (copyPullback A L e F) target B) :
    CoinitialBelowCode targetOrder F (relationImage target L e) (relationImage B L e) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage B L e y).1 hy
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 (basis.1 hx)
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    exact (unique y rel).trans (unique z relz).symm ▸ hz
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage target L e y).1 hy
    obtain ⟨b, hb, below⟩ := basis.2 x hx
    have hbA := ((mem_copyPullback A L e F b).1 (basis.1 hb)).1
    obtain ⟨b', relb, _⟩ := func.2 b hbA
    have hbL := (ZFSet.pair_mem_prod.1 (func.1 relb)).2
    exact ⟨b', (mem_relationImage B L e b').2 ⟨hbL, b, hb, relb⟩,
      monotone b x b' y below relb rel⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem copyPullback_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A L e F : ZFSet.{u}} (hA : A ∈ M.sets) (hL : L ∈ M.sets)
    (he : e ∈ M.sets) (hF : F ∈ M.sets) : copyPullback A L e F ∈ M.sets :=
  M.relationImage_mem separation hF hA
    (M.relationConverse_mem pairing unions powers separation hA hL he)

theorem internalCountableBelow_copy
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F target : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F) target) :
    M.InternalCountableBelow targetOrder F (relationImage target L e) := by
  obtain ⟨B, hB, small, coinitial⟩ := basis
  have subset : B ⊆ A := fun x hx => ((mem_copyPullback A L e F x).1 (coinitial.1 hx)).1
  exact ⟨relationImage B L e, M.relationImage_mem separation hB hL he,
    M.groundEmbeddable_image pairing unions powers separation hB hL
      (M.omega_mem separation infinite) he code subset small,
    coinitial.copy code.function monotone⟩

theorem internalCountableBelow_copy_pullback
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F)
      (copyPullback A L e F)) :
    M.InternalCountableBelow targetOrder F (F ∩ relationImage A L e) := by
  rw [← relationImage_copyPullback code.function F]
  exact M.internalCountableBelow_copy pairing unions powers separation infinite hL he code monotone basis

end TransitiveGround






theorem pair_mem_basisChoiceRelation (I W order target parts i B : ZFSet.{u}) :
    ZFSet.pair i B ∈ basisChoiceRelation I W order target parts ↔
      i ∈ I ∧ B ∈ W ∧ FiberCoveredCode order target parts i B := by
  rw [basisChoiceRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, A, hA, eq, covers⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hj, hA, covers⟩
  · rintro ⟨hi, hB, covers⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hB⟩, i, hi, B, hB, rfl, covers⟩

namespace BoundedFormula

open SetFormula

theorem truth_fiberCoveredFormula {n} (order target parts i B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fiberCoveredFormula order target parts i B) env ↔
      FiberCoveredCode (env order) (env target) (env parts) (env i) (env B) := by
  simp only [fiberCoveredFormula, Truth, truth_imp, truth_exMem, truth_pairMembershipFormula]
  rfl

theorem truth_basisChoiceEntryFormula {n} (z I W order target parts : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (basisChoiceEntryFormula z I W order target parts) env ↔
      ∃ i ∈ env I, ∃ B ∈ env W, env z = ZFSet.pair i B ∧
        FiberCoveredCode (env order) (env target) (env parts) i B := by
  simp only [basisChoiceEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_fiberCoveredFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem basisChoiceRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W order target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hW : W ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets) :
    basisChoiceRelation I W order target parts ∈ M.sets := by
  let params := extend I (extend W (extend order (extend target (extend parts Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hOrder (Fin.cases hTarget (Fin.cases hParts
      (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hI hW)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) (extend z params)) (ZFSet.prod I W) =
      basisChoiceRelation I W order target parts := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, basisChoiceRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_basisChoiceEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem internalCountableBelow_indexed_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I order F target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hOrder : order ∈ M.sets)
    (hF : F ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets)
    (smallI : M.groundEmbeddable I ZFSet.omega)
    (cover : ∀ x ∈ target, ∃ i ∈ I, ZFSet.pair i x ∈ parts)
    (localBases : ∀ i ∈ I, M.InternalCountableBelow order F (relationFiber target parts i)) :
    M.InternalCountableBelow order F target := by
  have hO := M.omega_mem separation infinite
  let W := M.groundSmallSubsets F ZFSet.omega
  have hW : W ∈ M.sets := M.groundSmallSubsets_mem powers separation hF hO
  have choices := M.basisChoiceRelation_mem pairing unions powers separation hI hW hOrder hTarget hParts
  have total (i : ZFSet.{u}) (hi : i ∈ I) :
      ∃ B ∈ W, ZFSet.pair i B ∈ basisChoiceRelation I W order target parts := by
    obtain ⟨B, hB, smallB, positive, below⟩ := localBases i hi
    have hBW : B ∈ W := (M.mem_groundSmallSubsets F ZFSet.omega B).2 ⟨hB, positive, smallB⟩
    exact ⟨B, hBW, (pair_mem_basisChoiceRelation I W order target parts i B).2
      ⟨hi, hBW, fun x hx rel => below x ((mem_relationFiber target parts i x).2 ⟨hx, rel⟩)⟩⟩
  obtain ⟨g, hg, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hI hW choices total
  let family := relationImage I W g
  have hFamily : family ∈ M.sets := M.relationImage_mem separation hI hW hg
  have smallFamily : M.groundEmbeddable family ZFSet.omega :=
    M.groundEmbeddable_function_image pairing unions powers separation choice hI hW hO hg func smallI
  have candidates (B : ZFSet.{u}) (hB : B ∈ family) : B ∈ W :=
    ((mem_relationImage I W g B).1 hB).1
  have smallBasis (B : ZFSet.{u}) (hB : B ∈ family) : M.groundEmbeddable B ZFSet.omega :=
    ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.2
  refine ⟨family.sUnion, M.union_mem unions hFamily,
    M.groundCountable_family_union pairing unions powers separation infinite choice
      hFamily smallFamily smallBasis, ?_, ?_⟩
  · intro x hx
    obtain ⟨B, hB, xB⟩ := ZFSet.mem_sUnion.1 hx
    exact ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.1 xB
  · intro x hx
    obtain ⟨i, hi, ix⟩ := cover x hx
    obtain ⟨B, chosen, _⟩ := func.2 i hi
    have spec := (pair_mem_basisChoiceRelation I W order target parts i B).1 (selected chosen)
    obtain ⟨b, hb, lower⟩ := spec.2.2 x hx ix
    have hB : B ∈ family := (mem_relationImage I W g B).2 ⟨spec.2.1, i, hi, chosen⟩
    exact ⟨b, ZFSet.mem_sUnion.2 ⟨B, hB, hb⟩, lower⟩

end TransitiveGround

end



namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem InternalCountableBelow.mono {order F target smaller : ZFSet.{u}}
    (basis : M.InternalCountableBelow order F target) (subset : smaller ⊆ target) :
    M.InternalCountableBelow order F smaller := by
  obtain ⟨B, hB, small, positive, below⟩ := basis
  exact ⟨B, hB, small, positive, fun x hx => below x (subset hx)⟩

theorem internalCountableBelow_empty (inhabited : M.sets.Nonempty) (order F : ZFSet.{u}) :
    M.InternalCountableBelow order F ∅ := by
  exact ⟨∅, M.empty_mem inhabited, M.empty_groundEmbeddable ZFSet.omega inhabited,
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx),
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx)⟩

theorem internalCountableBelow_of_countable {order F target : ZFSet.{u}}
    (hTarget : target ∈ M.sets) (small : M.groundEmbeddable target ZFSet.omega)
    (positive : target ⊆ F) (refl : ∀ x ∈ target, ZFSet.pair x x ∈ order) :
    M.InternalCountableBelow order F target :=
  ⟨target, hTarget, small, positive, fun x hx => ⟨x, hx, refl x hx⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologicalBasis
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem mem_birthEssentialSet (F T r birth x : ZFSet.{u}) :
    x ∈ birthEssentialSet F T r birth ↔ x ∈ F ∧
      ∀ y ∈ F, ∀ a ∈ T, ∀ b ∈ T,
        ZFSet.pair y x ∈ r → ZFSet.pair y a ∈ birth → ZFSet.pair x b ∈ birth → a ∉ b :=
  ZFSet.mem_sep

theorem birthEssentialSet_subset (F T r birth : ZFSet.{u}) :
    birthEssentialSet F T r birth ⊆ F := fun _ hx => (ZFSet.mem_sep.1 hx).1

theorem mem_essentialBirthIndices (F T r birth t : ZFSet.{u}) :
    t ∈ essentialBirthIndices F T r birth ↔ t ∈ T ∧
      ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair x t ∈ birth :=
  mem_relationImage _ _ _ _

theorem positive_above_birthEssential {L F T r birth : ZFSet.{u}}
    (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (refl : ∀ x ∈ L, ZFSet.pair x x ∈ r)
    (trans : ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
      ZFSet.pair x y ∈ r → ZFSet.pair y z ∈ r → ZFSet.pair x z ∈ r)
    {x : ZFSet.{u}} (positive : x ∈ F) :
    ∃ y ∈ birthEssentialSet F T r birth, ZFSet.pair y x ∈ r := by
  let S : Set ZFSet.{u} := {t | ∃ y ∈ F, ZFSet.pair y x ∈ r ∧ ZFSet.pair y t ∈ birth}
  obtain ⟨t, xt, _⟩ := born.2 x (subset positive)
  have inhabited : S.Nonempty := ⟨t, x, positive, refl x (subset positive), xt⟩
  obtain ⟨t, ⟨y, hy, below, yt⟩, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨y, (mem_birthEssentialSet F T r birth y).2 ⟨hy, ?_⟩, below⟩
  intro z hz a _ b _ zy za yb earlier
  obtain ⟨_, _, unique⟩ := born.2 y (subset hy)
  have eq : b = t := (unique b yb).trans (unique t yt).symm
  have aS : a ∈ S := ⟨z, hz, trans z (subset hz) y (subset hy) x (subset positive) zy below, za⟩
  exact minimal a aS (eq ▸ earlier)

namespace BoundedFormula

open SetFormula

theorem truth_birthEssentialFormula {n} (x f t r birth : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (birthEssentialFormula x f t r birth) env ↔
      ∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
        ZFSet.pair y (env x) ∈ env r → ZFSet.pair y a ∈ env birth →
          ZFSet.pair (env x) b ∈ env birth → a ∉ b := by
  simp only [birthEssentialFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change (∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
    ZFSet.pair y (env x) ∈ env r ∧ ZFSet.pair y a ∈ env birth ∧
      ZFSet.pair (env x) b ∈ env birth → a ∉ b) ↔ _
  constructor
  · intro h y hy a ha b hb below bornY bornX
    exact h y hy a ha b hb ⟨below, bornY, bornX⟩
  · intro h y hy a ha b hb premises
    exact h y hy a ha b hb premises.1 premises.2.1 premises.2.2

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem birthEssentialSet_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    birthEssentialSet F T r birth ∈ M.sets := by
  let params := extend F (extend T (extend r (extend birth Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.birthEssentialFormula 0 1 2 3 4) params
    (Fin.cases hF (Fin.cases hT (Fin.cases hr (Fin.cases hBirth (fun j => Fin.elim0 j))))) hF
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.birthEssentialFormula 0 1 2 3 4) (extend x params)) F =
      birthEssentialSet F T r birth := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_birthEssentialSet]
    exact and_congr Iff.rfl (BoundedFormula.truth_birthEssentialFormula 0 1 2 3 4 _)
  exact eq ▸ selected

theorem essentialBirthIndices_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    essentialBirthIndices F T r birth ∈ M.sets :=
  M.relationImage_mem separation (M.birthEssentialSet_mem separation hF hT hr hBirth) hT hBirth

theorem exists_essentialBirthRepresentatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    ∃ g ∈ M.sets,
      ZFSet.IsFunc (essentialBirthIndices F T r birth) (birthEssentialSet F T r birth) g ∧
      g ⊆ relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth ∧
      ∀ t ∈ essentialBirthIndices F T r birth,
        ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair t x ∈ g ∧ ZFSet.pair x t ∈ birth := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hConverse := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have total : ∀ t ∈ S, ∃ x ∈ E, ZFSet.pair t x ∈ relationConverse E S birth := by
    intro t ht
    obtain ⟨_, x, hx, born⟩ := (mem_essentialBirthIndices F T r birth t).1 ht
    exact ⟨x, hx, (pair_mem_relationConverse E S birth x t).2 ⟨hx, ht, born⟩⟩
  obtain ⟨g, hg, function, restricted⟩ :=
    M.uniformize_relation pairing unions powers separation choice hS hE hConverse total
  refine ⟨g, hg, function, restricted, ?_⟩
  intro t ht
  obtain ⟨x, chosen, _⟩ := function.2 t ht
  have spec := (pair_mem_relationConverse E S birth x t).1 (restricted chosen)
  exact ⟨x, spec.1, chosen, spec.2.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem internal_countable_basis_of_birth_layers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (order : PartialOrderCode L r) (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (small : M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    M.InternalCountableBelow r F F := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  let parts := relationConverse E S birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hParts : parts ∈ M.sets := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have cover (x : ZFSet.{u}) (hx : x ∈ E) : ∃ t ∈ S, ZFSet.pair t x ∈ parts := by
    obtain ⟨t, xt, _⟩ := born.2 x (subset (birthEssentialSet_subset F T r birth hx))
    have htT := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
    have htS : t ∈ S := (mem_essentialBirthIndices F T r birth t).2 ⟨htT, x, hx, xt⟩
    exact ⟨t, htS, (pair_mem_relationConverse E S birth x t).2 ⟨hx, htS, xt⟩⟩
  obtain ⟨B, hB, smallB, positive, below⟩ := M.internalCountableBelow_indexed_union
    pairing unions powers separation infinite choice hS hr hF hE hParts small cover localBases
  refine ⟨B, hB, smallB, positive, ?_⟩
  intro x hx
  obtain ⟨y, hy, yx⟩ := positive_above_birthEssential subset born order.refl order.trans hx
  obtain ⟨b, hb, byLower⟩ := below y hy
  exact ⟨b, hb, order.trans b (subset (positive hb)) y
    (subset (birthEssentialSet_subset F T r birth hy)) x (subset hx) byLower yx⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNaturalFamilyShift
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem mem_heightColumnFiber (S C Q h c i : ZFSet.{u}) :
    i ∈ heightColumnFiber S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ ∃ q ∈ Q, ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnFiber, mem_relationImage]
  constructor
  · rintro ⟨hi, v, hv, vi⟩
    obtain ⟨a, ha, q, hq, rfl⟩ := ZFSet.mem_prod.1 hv
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    have rel := (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).1 vi
    exact ⟨hi, (ZFSet.pair_mem_prod.1 rel.2.1).1, q, hq, rel.2.2⟩
  · rintro ⟨hi, hc, q, hq, iq⟩
    exact ⟨hi, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hq⟩,
      (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).2
        ⟨hi, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq⟩⟩

theorem pair_mem_heightColumnGraph (S C Q h c i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ heightColumnGraph S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ q ∈ Q ∧ ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨hi, hq, v, hv, iv, vq⟩
    obtain ⟨a, ha, b, _, eq⟩ := (mem_productSecond {c} Q (ZFSet.pair v q)).1 vq
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hi, (ZFSet.pair_mem_prod.1 hv).1, hq, iv⟩
  · rintro ⟨hi, hc, hq, iq⟩
    exact ⟨hi, hq, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq,
      (mem_productSecond {c} Q _).2 ⟨c, ZFSet.mem_singleton.2 rfl, q, hq, rfl⟩⟩

theorem heightColumnGraph_injection {S C Q h : ZFSet.{u}}
    (height : InjectionCode S (ZFSet.prod C Q) h) (c : ZFSet.{u}) :
    InjectionCode (heightColumnFiber S C Q h c) Q (heightColumnGraph S C Q h c) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have shape : z ∈ ZFSet.prod S Q := (ZFSet.mem_sep.1
      (show z ∈ relationCompose S (ZFSet.prod C Q) Q h (productSecond {c} Q) from hz)).1
    obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 shape
    obtain ⟨_, hc, _, iq⟩ := (pair_mem_heightColumnGraph S C Q h c i q).1 hz
    exact ZFSet.pair_mem_prod.2
      ⟨(mem_heightColumnFiber S C Q h c i).2 ⟨hi, hc, q, hq, iq⟩, hq⟩
  · intro i hi
    obtain ⟨hiS, hc, q, hq, iq⟩ := (mem_heightColumnFiber S C Q h c i).1 hi
    refine ⟨q, (pair_mem_heightColumnGraph S C Q h c i q).2 ⟨hiS, hc, hq, iq⟩, ?_⟩
    intro r ir
    have irh := (pair_mem_heightColumnGraph S C Q h c i r).1 ir
    obtain ⟨v, _, unique⟩ := height.function.2 i hiS
    exact (ZFSet.pair_inj.1 ((unique _ irh.2.2.2).trans (unique _ iq).symm)).2
  · intro i j q iq jq
    exact height.injective i j (ZFSet.pair c q)
      ((pair_mem_heightColumnGraph S C Q h c i q).1 iq).2.2.2
      ((pair_mem_heightColumnGraph S C Q h c j q).1 jq).2.2.2

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightColumnFiber_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnFiber S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationImage_mem separation
    (M.prod_mem pairing unions powers separation singleton hQ) hS
    (M.relationConverse_mem pairing unions powers separation hS
      (M.prod_mem pairing unions powers separation hC hQ) hh)

theorem heightColumnGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnGraph S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationCompose_mem pairing unions powers separation hS
    (M.prod_mem pairing unions powers separation hC hQ) hQ hh
    (M.productSecond_mem pairing unions powers separation singleton hQ)

theorem groundEmbeddable_heightColumnFiber
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c N : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) (hN : N ∈ M.sets)
    (height : InjectionCode S (ZFSet.prod C Q) h) (small : M.groundEmbeddable Q N) :
    M.groundEmbeddable (heightColumnFiber S C Q h c) N := by
  obtain ⟨f, hf, code⟩ := small
  exact ⟨relationCompose (heightColumnFiber S C Q h c) Q N (heightColumnGraph S C Q h c) f,
    M.relationCompose_mem pairing unions powers separation
      (M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh hc) hQ hN
      (M.heightColumnGraph_mem pairing unions powers separation hS hC hQ hh hc) hf,
    (heightColumnGraph_injection height c).compose code⟩

end TransitiveGround

end



section

open SetRealization
universe u

theorem ordinalSubset_has_least {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    {S : Set ZFSet.{u}} (subset : ∀ i ∈ S, i ∈ T) (inhabited : S.Nonempty) :
    ∃ i ∈ S, ∀ j ∈ S, i = j ∨ i ∈ j := by
  obtain ⟨i, hi, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨i, hi, ?_⟩
  intro j hj
  rcases ordinalSetProperty_mem_compare ordinal (subset i hi) (subset j hj) with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact False.elim (minimal j hj h)

theorem mem_ordinalIndexTail (S i j : ZFSet.{u}) :
    j ∈ ordinalIndexTail S i ↔ j ∈ S ∧ (i = j ∨ i ∈ j) := ZFSet.mem_sep

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem ordinalIndexTail_mem (separation : SeparationSchema M.sets)
    {S i : ZFSet.{u}} (hS : S ∈ M.sets) (hi : i ∈ M.sets) :
    ordinalIndexTail S i ∈ M.sets := by
  have selected := M.bounded_separation_mem separation (.disj (.equal 1 0) (.mem 1 0))
    (extend i Fin.elim0) (Fin.cases hi (fun j => Fin.elim0 j)) hS
  simpa only [BoundedFormula.truth_disj, BoundedFormula.Truth, extend, Fin.cases_zero,
    show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ, ordinalIndexTail] using selected

theorem groundCountable_descending_heights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S T C Q h : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (subset : S ⊆ T)
    (ordinal : ordinalSetProperty T) (height : InjectionCode S (ZFSet.prod C Q) h)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (antitone : ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d r,
      ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d r) ∈ h →
        d = c ∨ d ∈ c) :
    M.groundEmbeddable S ZFSet.omega := by
  classical
  have hOmega := M.omega_mem separation infinite
  have tails : ∀ c, ∀ i ∈ S, ∀ q, ZFSet.pair i (ZFSet.pair c q) ∈ h →
      M.groundEmbeddable (ordinalIndexTail S i) ZFSet.omega := by
    intro c
    induction c using ZFSet.inductionOn with
    | h c ih =>
      intro i hi q iq
      have hc := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iq)).2).1
      have groundTail := M.ordinalIndexTail_mem separation hS (M.transitive hS hi)
      have groundFiber := M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh
        (M.transitive hC hc)
      have smallFiber := M.groundEmbeddable_heightColumnFiber pairing unions powers separation
        hS hC hQ hh (M.transitive hC hc) hOmega height smallQ
      have columnBelow (k : ZFSet.{u}) (hk : k ∈ S) (later : i = k ∨ i ∈ k)
          (d r : ZFSet.{u}) (kr : ZFSet.pair k (ZFSet.pair d r) ∈ h) : d = c ∨ d ∈ c := by
        rcases later with rfl | later
        · obtain ⟨_, _, unique⟩ := height.function.2 i hi
          exact Or.inl (ZFSet.pair_inj.1 ((unique _ kr).trans (unique _ iq).symm)).1
        · exact antitone i hi k hk later c q d r iq kr
      let lower : Set ZFSet.{u} := {j | j ∈ S ∧ (i = j ∨ i ∈ j) ∧
        ∃ d r, d ∈ c ∧ ZFSet.pair j (ZFSet.pair d r) ∈ h}
      by_cases inhabited : lower.Nonempty
      · obtain ⟨j, hj, minimal⟩ := ordinalSubset_has_least ordinal
          (fun k hk => subset hk.1) inhabited
        obtain ⟨hjS, _, d, r, dc, jr⟩ := hj
        have smallLater := ih d dc j hjS r jr
        have smallUnion := M.groundCountable_binary_union pairing unions powers separation
          infinite choice groundFiber (M.ordinalIndexTail_mem separation hS (M.transitive hS hjS))
          smallFiber smallLater
        apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallUnion
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact ZFSet.mem_union.2 (Or.inl
            ((mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩))
        · have klower : k ∈ lower := ⟨hkS, later, e, s, less, kv⟩
          exact ZFSet.mem_union.2 (Or.inr
            ((mem_ordinalIndexTail S j k).2 ⟨hkS, minimal k klower⟩))
      · apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallFiber
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact (mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩
        · exact False.elim (inhabited ⟨k, hkS, later, e, s, less, kv⟩)
  by_cases inhabited : (S.toSet).Nonempty
  · obtain ⟨i, hi, minimal⟩ := ordinalSubset_has_least ordinal (fun _ hx => subset hx) inhabited
    obtain ⟨v, iv, _⟩ := height.function.2 i hi
    obtain ⟨c, _, q, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iv)).2
    exact M.groundEmbeddable_restrict separation hS hOmega
      (fun j hj => (mem_ordinalIndexTail S i j).2 ⟨hj, minimal j hj⟩) (tails c i hi q iv)
  · have empty : S = ∅ := by
      apply ZFSet.ext
      intro x
      exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
        fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    rw [empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨S, hS⟩

end TransitiveGround






theorem essentialHeightComposite_strict {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt)
    {i j c q d v : ZFSet.{u}} (earlier : i ∈ j)
    (first : ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
    (second : ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height) :
    d ∈ c ∨ (d = c ∧ ZFSet.pair v q ∈ qlt) := by
  obtain ⟨_, _, x, hx, ix, xheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
  obtain ⟨_, _, y, hy, jy, yheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
  have xi := (pair_mem_relationConverse E S birth x i).1 (representatives ix)
  have yj := (pair_mem_relationConverse E S birth y j).1 (representatives jy)
  exact descent x hx y hy i j c q d v xi.2.2 yj.2.2 earlier xheight yheight

theorem essentialHeightComposite_antitone {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt) :
    ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d v,
      ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
      ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
        d = c ∨ d ∈ c := by
  intro i _ j _ earlier c q d v first second
  exact (essentialHeightComposite_strict representatives descent earlier first second).elim
    Or.inr (fun h => Or.inl h.1)

theorem essentialHeightComposite_injection {L S T E C Q birth reps height qlt : ZFSet.{u}}
    (stages : S ⊆ T) (ordinal : ordinalSetProperty T)
    (representatives : ZFSet.IsFunc S E reps)
    (chosenBirths : reps ⊆ relationConverse E S birth)
    (points : E ⊆ L) (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent E birth height qlt) :
    InjectionCode S (ZFSet.prod C Q) (relationCompose S E (ZFSet.prod C Q) reps height) := by
  have function := relationCompose_function_of_subset representatives heights points
  refine ⟨function, ?_⟩
  intro i j z first second
  have iShape := ZFSet.pair_mem_prod.1 (function.1 first)
  have jShape := ZFSet.pair_mem_prod.1 (function.1 second)
  obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 iShape.2
  have notEarlier (a b : ZFSet.{u})
      (aHeight : ZFSet.pair a (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
      (bHeight : ZFSet.pair b (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height) : a ∉ b := by
    intro earlier
    rcases essentialHeightComposite_strict chosenBirths descent earlier aHeight bHeight with h | h
    · exact ZFSet.mem_irrefl c h
    · exact irreflexive q hq h.2
  have eqI := ordinalSetProperty_eq_code_rank i (ordinalSetProperty_member ordinal (stages iShape.1))
  have eqJ := ordinalSetProperty_eq_code_rank j (ordinalSetProperty_member ordinal (stages jShape.1))
  rcases lt_trichotomy (ZFSet.rank i) (ZFSet.rank j) with earlier | equal | later
  · have ij : i ∈ j := by rw [eqI, eqJ, mem_ordinalCode_iff]; exact earlier
    exact False.elim (notEarlier i j first second ij)
  · exact eqI.trans ((congrArg ordinalCode equal).trans eqJ.symm)
  · have ji : j ∈ i := by rw [eqJ, eqI, mem_ordinalCode_iff]; exact later
    exact False.elim (notEarlier j i second first ji)

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_essentialBirthHeights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    ∃ h ∈ M.sets,
      InjectionCode (essentialBirthIndices F T r birth) (ZFSet.prod C Q) h ∧
      (∀ i ∈ essentialBirthIndices F T r birth, ∀ j ∈ essentialBirthIndices F T r birth,
        i ∈ j → ∀ c q d v,
          ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d v) ∈ h →
            d = c ∨ d ∈ c) ∧
      ∀ i z, ZFSet.pair i z ∈ h → ∃ x ∈ birthEssentialSet F T r birth,
        ZFSet.pair x i ∈ birth ∧ ZFSet.pair x z ∈ height := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS := M.essentialBirthIndices_mem separation hF hT hr hBirth
  obtain ⟨reps, hReps, function, chosen, _⟩ :=
    M.exists_essentialBirthRepresentatives pairing unions powers separation choice hF hT hr hBirth
  let h := relationCompose S E (ZFSet.prod C Q) reps height
  have ground : h ∈ M.sets := M.relationCompose_mem pairing unions powers separation hS hE
    (M.prod_mem pairing unions powers separation hC hQ) hReps hHeight
  have subset : S ⊆ T := fun _ hi => (mem_essentialBirthIndices F T r birth _).1 hi |>.1
  have points : E ⊆ L := fun _ hx => positive (birthEssentialSet_subset F T r birth hx)
  refine ⟨h, ground, essentialHeightComposite_injection subset ordinal function chosen points heights
    irreflexive descent, essentialHeightComposite_antitone chosen descent, ?_⟩
  intro i z hiz
  obtain ⟨_, _, x, hx, ix, xz⟩ := (pair_mem_relationCompose S E (ZFSet.prod C Q) reps height i z).1 hiz
  exact ⟨x, hx, ((pair_mem_relationConverse E S birth x i).1 (chosen ix)).2.2, xz⟩

theorem essentialBirthIndices_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega := by
  obtain ⟨h, hh, injection, antitone, _⟩ := M.exists_essentialBirthHeights pairing unions powers
    separation choice hF hT hr hBirth hC hQ hHeight positive ordinal heights irreflexive descent
  exact M.groundCountable_descending_heights pairing unions powers separation infinite choice
    (M.essentialBirthIndices_mem separation hF hT hr hBirth) hC hQ hh
    (fun _ hi => ((mem_essentialBirthIndices F T r birth _).1 hi).1)
    ordinal injection smallQ antitone

end TransitiveGround

end



open SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageFromCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem birthEssential_below_earlier {L F T r μ birth x y a b : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (essential : x ∈ birthEssentialSet F T r birth) (positive : y ∈ F)
    (bornY : ZFSet.pair y a ∈ birth) (bornX : ZFSet.pair x b ∈ birth)
    (earlier : a ∈ b) : ZFSet.pair x y ∈ r ∧ x ≠ y := by
  classical
  have hx := (mem_birthEssentialSet F T r birth x).1 essential
  have xL := filter.subset hx.1
  have yL := filter.subset positive
  have bT := (ZFSet.pair_mem_prod.1 (born.1 bornX)).2
  have lower : ZFSet.pair x y ∈ r := by
    by_contra notLower
    obtain ⟨z, meetXY, _⟩ := meet.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨xL, yL⟩)
    have zL := (ZFSet.pair_mem_prod.1 (meet.operation.1 meetXY)).2
    obtain ⟨c, bornZ, _⟩ := born.2 z zL
    have cT := (ZFSet.pair_mem_prod.1 (born.1 bornZ)).2
    exact hx.2 z (filter.closed_meet x hx.1 y positive z meetXY) c cT b bT
      (meet.lower_left x y z meetXY) bornZ bornX
      (oldMeet x y z a b c bornY bornX earlier notLower meetXY bornZ)
  refine ⟨lower, ?_⟩
  intro equal
  subst y
  obtain ⟨t, _, unique⟩ := born.2 x xL
  have sameBirth : a = b := (unique a bornY).trans (unique b bornX).symm
  exact ZFSet.mem_irrefl b (sameBirth ▸ earlier)

theorem essentialHeightDescent_of_chronological_laws
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt) :
    EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt := by
  intro x hx y hy i j c q d v bornX bornY earlier heightX heightY
  have lower := birthEssential_below_earlier meet filter born oldMeet hy
    (birthEssentialSet_subset F T r birth hx) bornX bornY earlier
  exact strictHeight.strict y (filter.subset (birthEssentialSet_subset F T r birth hy))
    x (filter.subset (birthEssentialSet_subset F T r birth hx)) d v c q
    lower.1 lower.2 heightY heightX

end



section

universe u v

theorem mem_essentialBirthFiber (F T r birth t x : ZFSet.{u}) :
    x ∈ essentialBirthFiber F T r birth t ↔
      x ∈ birthEssentialSet F T r birth ∧ t ∈ T ∧ ZFSet.pair x t ∈ birth := by
  rw [essentialBirthFiber, mem_relationFiber, pair_mem_relationConverse]
  constructor
  · rintro ⟨hx, _, ht, born⟩
    exact ⟨hx, ((mem_essentialBirthIndices F T r birth t).1 ht).1, born⟩
  · rintro ⟨hx, ht, born⟩
    exact ⟨hx, hx, (mem_essentialBirthIndices F T r birth t).2 ⟨ht, x, hx, born⟩, born⟩

theorem essentialBirthFiber_subset (F T r birth t : ZFSet.{u}) :
    essentialBirthFiber F T r birth t ⊆ birthEssentialSet F T r birth :=
  fun _ hx => ((mem_essentialBirthFiber F T r birth t _).1 hx).1

theorem birthEssentials_no_oldBridge {L F T r μ birth t x y : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (hx : x ∈ birthEssentialSet F T r birth) (hy : y ∈ birthEssentialSet F T r birth)
    (xt : ZFSet.pair x t ∈ birth) (yt : ZFSet.pair y t ∈ birth) :
    ¬ OldBridgeCode L r μ birth t x y := by
  have xE := (mem_birthEssentialSet F T r birth x).1 hx
  have yE := (mem_birthEssentialSet F T r birth y).1 hy
  have ht := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
  intro bridge
  rcases bridge with ⟨z, a, meetXY, za, old⟩ | ⟨z, hz, a, za, old, intermediate⟩
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    exact xE.2 z (filter.closed_meet x xE.1 y yE.1 z meetXY) a ha t ht
      (meet.lower_left x y z meetXY) za xt old
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    rcases intermediate with ⟨xz, zy⟩ | ⟨yz, zx⟩
    · exact yE.2 z (filter.upward x xE.1 z hz xz) a ha t ht zy za yt old
    · exact xE.2 z (filter.upward y yE.1 z hz yz) a ha t ht zx za xt old

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem essentialBirthFiber_mem (separation : SeparationSchema M.sets)
    {F T r birth t : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) (ht : t ∈ M.sets) :
    essentialBirthFiber F T r birth t ∈ M.sets := by
  let E := birthEssentialSet F T r birth
  let params := extend t (extend T (extend birth Fin.elim0))
  let φ : BoundedFormula 4 := .conj (.mem 1 2) (BoundedFormula.pairMembershipFormula 0 1 3)
  have selected := M.bounded_separation_mem separation φ params
    (Fin.cases ht (Fin.cases hT (Fin.cases hBirth (fun j => Fin.elim0 j))))
    (M.birthEssentialSet_mem separation hF hT hr hBirth)
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth φ (extend x params)) E =
      essentialBirthFiber F T r birth t := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_essentialBirthFiber]
    exact and_congr Iff.rfl
      (and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 0 1 3 _))
  exact eq ▸ selected

end TransitiveGround

end



section
universe u

namespace BoundedFormula
open SetFormula

theorem truth_mainStageFormula {n} (z P r μ G m inv one A bottom top height : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainStageFormula z P r μ G m inv one A bottom top height) env ↔
      env z = mainStageCode (env P) (env r) (env μ) (env G) (env m) (env inv) (env one) (env A) (env bottom) (env top) (env height) := by
  rw [mainStageFormula, truth_nonemptyTupleFormula]
  rfl

theorem realize_mainStageFormula (M : TransitiveGround.{u}) {n}
    (z P r μ G m inv one A bottom top height : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (mainStageFormula z P r μ G m inv one A bottom top height).toFormula env ↔
      env z = mainStageCode (env P) (env r) (env μ) (env G) (env m) (env inv) (env one) (env A) (env bottom) (env top) (env height) :=
  (realize_toFormula M _ env members).trans (truth_mainStageFormula z P r μ G m inv one A bottom top height env)

end BoundedFormula

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedChronologyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_oldMeetFormula {n} (L T r μ birth : Fin n) (env : Fin n → ZFSet.{u})
    (function : ZFSet.IsFunc (env L) (env T) (env birth)) :
    Truth (oldMeetFormula L T r μ birth) env ↔ OldMeetCode (env r) (env μ) (env birth) := by
  simp only [oldMeetFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  constructor
  · intro property x y z a b c bornY bornX earlier notLower meetXY bornZ
    have xBounds := ZFSet.pair_mem_prod.1 (function.1 bornX)
    have yBounds := ZFSet.pair_mem_prod.1 (function.1 bornY)
    have zBounds := ZFSet.pair_mem_prod.1 (function.1 bornZ)
    exact property x xBounds.1 y yBounds.1 z zBounds.1 a yBounds.2 b xBounds.2 c zBounds.2
      ⟨bornY, bornX, earlier, notLower, meetXY, bornZ⟩
  · intro property x _ y _ z _ a _ b _ c _ condition
    exact property x y z a b c condition.1 condition.2.1 condition.2.2.1
      condition.2.2.2.1 condition.2.2.2.2.1 condition.2.2.2.2.2

theorem truth_birthBoundFormula {n} (L T birth s : Fin n) (env : Fin n → ZFSet.{u})
    (function : ZFSet.IsFunc (env L) (env T) (env birth)) :
    Truth (birthBoundFormula L T birth s) env ↔
      ∀ x ∈ env L, ∀ t, ZFSet.pair x t ∈ env birth → t = env s ∨ t ∈ env s := by
  simp only [birthBoundFormula, Truth, truth_imp, truth_pairMembershipFormula, truth_disj]
  exact ⟨fun bound x hx t entry => bound x hx t
      (ZFSet.pair_mem_prod.1 (function.1 entry)).2 entry,
    fun bound x hx t _ entry => bound x hx t entry⟩

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedMeetOrderCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_meetOrderFormula {n} (P r μ : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (meetOrderFormula P r μ) env ↔ MeetOrderCode (env P) (env r) (env μ) := by
  simp only [meetOrderFormula, Truth, truth_partialOrderFormula,
    truth_binaryFunctionFormula, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  constructor
  · rintro ⟨order, operation, laws⟩
    have bounds (x y z : ZFSet.{u}) (entry : ZFSet.pair (ZFSet.pair x y) z ∈ env μ) :
        x ∈ env P ∧ y ∈ env P ∧ z ∈ env P := by
      have shape := ZFSet.pair_mem_prod.1 (operation.1 entry)
      exact ⟨(ZFSet.pair_mem_prod.1 shape.1).1,
        (ZFSet.pair_mem_prod.1 shape.1).2, shape.2⟩
    refine ⟨order, operation, ?_, ?_, ?_⟩
    · intro x y z entry
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).1
    · intro x y z entry
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).2.1
    · intro x y z w hw entry wx wy
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).2.2 w hw ⟨wx, wy⟩
  · intro meet
    exact ⟨meet.order, meet.operation, fun x _ y _ z _ entry =>
      ⟨meet.lower_left x y z entry, meet.lower_right x y z entry,
        fun w hw ⟨wx, wy⟩ => meet.greatest x y z w hw entry wx wy⟩⟩

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundStrongLimitFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_relativePowerFormula {n} (a p : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (relativePowerFormula a p) env ↔ env p = M.groundPower (env a) := by
  simp only [relativePowerFormula, realize_imp, Realize]
  have subset (x : ZFSet.{u}) (hx : x ∈ M.sets) :=
    (BoundedFormula.realize_toFormula M (BoundedFormula.subsetFormula 0 a.succ)
      (extend x env) (Fin.cases hx members)).trans
        (BoundedFormula.truth_subsetFormula 0 a.succ (extend x env))
  constructor
  · intro property
    apply ZFSet.ext
    intro x
    rw [M.mem_groundPower]
    constructor
    · intro hx
      have hxM := M.transitive (members p) hx
      exact ⟨hxM, (subset x hxM).1 ((property x hxM).1 hx)⟩
    · rintro ⟨hxM, included⟩
      exact (property x hxM).2 ((subset x hxM).2 included)
  · intro equal x hx
    constructor
    · intro entry
      change x ∈ env p at entry
      rw [equal, M.mem_groundPower] at entry
      exact (subset x hx).2 entry.2
    · intro included
      change x ∈ env p
      rw [equal, M.mem_groundPower]
      exact ⟨hx, (subset x hx).1 included⟩

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NaturalStepFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace BoundedFormula

theorem truth_graphRestrictionFormula {n} (p a b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphRestrictionFormula p a b f) env ↔
      env p = ZFSet.sep (fun z => z ∈ ZFSet.prod (env a) (env b)) (env f) := by
  simp only [graphRestrictionFormula, Truth, truth_imp, truth_productElementFormula]
  change ((∀ z ∈ env p, z ∈ env f ∧ z ∈ ZFSet.prod (env a) (env b)) ∧
    (∀ z ∈ env f, z ∈ ZFSet.prod (env a) (env b) → z ∈ env p)) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨forward z, fun hz => backward z hz.1 hz.2⟩
  · intro eq
    rw [eq]
    exact ⟨fun z hz => ZFSet.mem_sep.1 hz, fun z hz bound => ZFSet.mem_sep.2 ⟨hz, bound⟩⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_graphRestrictionFormula {n} (p a b f : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (BoundedFormula.graphRestrictionFormula p a b f).toFormula env ↔
      env p = ZFSet.sep (fun z => z ∈ ZFSet.prod (env a) (env b)) (env f) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_graphRestrictionFormula p a b f env)

end TransitiveGround

end




open SetFormula
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem realize_ordinalRecursionTraceFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    Realize M.sets (ordinalRecursionTraceFormula φ) (extend A (extend f params)) ↔
      OrdinalRecursionTrace (groundRecursionStep M φ params) A f := by
  rw [ordinalRecursionTraceFormula, realize_ex]
  constructor
  · rintro ⟨B, hB, function, steps⟩
    have mem3 : ∀ i, extend B (extend A (extend f params)) i ∈ M.sets :=
      Fin.cases hB (Fin.cases hA (Fin.cases hf members))
    have func : ZFSet.IsFunc A B f := (BoundedFormula.truth_functionFormula 1 0 2 _).1
      ((BoundedFormula.realize_toFormula M _ _ mem3).1 function)
    refine ⟨⟨B, func⟩, ?_⟩
    intro a ha y ay
    have haM := M.transitive hA ha
    have hyB := (ZFSet.pair_mem_prod.1 (func.1 ay)).2
    have hyM := M.transitive hB hyB
    have first := (realize_imp M.sets _ _ _).1 (steps a haM) ha
    have second := (realize_imp M.sets _ _ _).1 (first y hyM) hyB
    have mem5 : ∀ i, extend y (extend a (extend B (extend A (extend f params)))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases haM mem3)
    have pairCode := (BoundedFormula.realize_toFormula M _ _ mem5).2
      ((BoundedFormula.truth_pairMembershipFormula 1 0 4 _).2 ay)
    obtain ⟨p, hp, restricted, step⟩ := (realize_ex M.sets _ _).1
      ((realize_imp M.sets _ _ _).1 second pairCode)
    have eq := (M.realize_graphRestrictionFormula 0 2 3 5 _ (Fin.cases hp mem5)).1 restricted
    have same : p = graphRestriction a f := eq.trans (graphRestriction_eq_sep func).symm
    rw [realize_reindex, map_extend, map_extend, map_extend] at step
    change Realize M.sets φ (extend a (extend p (extend y params))) at step
    rw [same] at hp step
    exact ⟨hp, hyM, step⟩
  · intro trace
    let B := ZFSet.sUnion (ZFSet.sUnion f)
    have hB : B ∈ M.sets := M.union_mem unions (M.union_mem unions hf)
    have func : ZFSet.IsFunc A B f := trace.1.to_isFunc
    have mem3 : ∀ i, extend B (extend A (extend f params)) i ∈ M.sets :=
      Fin.cases hB (Fin.cases hA (Fin.cases hf members))
    refine ⟨B, hB, (BoundedFormula.realize_toFormula M _ _ mem3).2
      ((BoundedFormula.truth_functionFormula 1 0 2 _).2 func), ?_⟩
    intro a haM
    apply (realize_imp M.sets _ _ _).2
    intro ha y hyM
    apply (realize_imp M.sets _ _ _).2
    intro _
    apply (realize_imp M.sets _ _ _).2
    intro pairCode
    have mem5 : ∀ i, extend y (extend a (extend B (extend A (extend f params)))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases haM mem3)
    have ay := (BoundedFormula.truth_pairMembershipFormula 1 0 4 _).1
      ((BoundedFormula.realize_toFormula M _ _ mem5).1 pairCode)
    obtain ⟨hp, _, step⟩ := trace.2 a ha y ay
    apply (realize_ex M.sets _ _).2
    refine ⟨graphRestriction a f, hp,
      (M.realize_graphRestrictionFormula 0 2 3 5 _ (Fin.cases hp mem5)).2
        (graphRestriction_eq_sep func), ?_⟩
    rw [realize_reindex, map_extend, map_extend, map_extend]
    exact step

theorem realize_ordinalSuccessorTraceFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {a f : ZFSet.{u}}
    (ha : a ∈ M.sets) (hf : f ∈ M.sets) :
    Realize M.sets (ordinalSuccessorTraceFormula φ) (extend a (extend f params)) ↔
      OrdinalRecursionTrace (groundRecursionStep M φ params) (insert a a) f := by
  rw [ordinalSuccessorTraceFormula, realize_ex]
  constructor
  · rintro ⟨A, hA, successor, trace⟩
    have eq := (BoundedFormula.truth_successorFormula 0 1 _).1
      ((BoundedFormula.realize_toFormula M _ _
        (Fin.cases hA (Fin.cases ha (Fin.cases hf members)))).1 successor)
    rw [realize_reindex, map_extend, map_extend] at trace
    change Realize M.sets (ordinalRecursionTraceFormula φ) (extend A (extend f params)) at trace
    have code := (M.realize_ordinalRecursionTraceFormula unions φ params members hA hf).1 trace
    exact eq ▸ code
  · intro trace
    have hA := M.insert_mem pairing unions ha ha
    refine ⟨insert a a, hA, (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hA (Fin.cases ha (Fin.cases hf members)))).2
        ((BoundedFormula.truth_successorFormula 0 1 _).2 rfl), ?_⟩
    rw [realize_reindex, map_extend, map_extend]
    exact (M.realize_ordinalRecursionTraceFormula unions φ params members hA hf).2 trace

end TransitiveGround





end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundIntervalRecursion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem collect_ordinalSuccessorTraces
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (traces : ∀ β ∈ A, ∃ f ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M φ params) (insert β β) f) :
    ∃ family ∈ M.sets,
      (∀ f ∈ family, ∃ β ∈ A,
        OrdinalRecursionTrace (groundRecursionStep M φ params) (insert β β) f) ∧
      ∀ β ∈ A, ∃ f ∈ family,
        OrdinalRecursionTrace (groundRecursionStep M φ params) (insert β β) f := by
  have witnesses : ∀ β ∈ A, ∃ f ∈ M.sets,
      Realize M.sets (ordinalSuccessorTraceFormula φ) (extend β (extend f params)) := by
    intro β hβ
    obtain ⟨f, hf, trace⟩ := traces β hβ
    exact ⟨f, hf, (M.realize_ordinalSuccessorTraceFormula pairing unions φ params
      members (M.transitive hA hβ) hf).2 trace⟩
  obtain ⟨W, hW, covers⟩ := M.collection_witness collection (ordinalSuccessorTraceFormula φ)
    params members hA witnesses
  let family := ZFSet.sep (fun f => Realize M.sets
    (relationImageFormula (ordinalSuccessorTraceFormula φ)) (extend f (extend A params))) W
  have hFamily : family ∈ M.sets := M.separation_mem separation
    (relationImageFormula (ordinalSuccessorTraceFormula φ)) (extend A params)
    (Fin.cases hA members) hW
  refine ⟨family, hFamily, ?_, ?_⟩
  · intro f hf
    obtain ⟨hfW, selected⟩ := ZFSet.mem_sep.1 hf
    obtain ⟨β, hβ, relation⟩ := (M.realize_relationImageFormula
      (ordinalSuccessorTraceFormula φ) params A f hA).1 selected
    exact ⟨β, hβ, (M.realize_ordinalSuccessorTraceFormula pairing unions φ params
      members (M.transitive hA hβ) (M.transitive hW hfW)).1 relation⟩
  · intro β hβ
    obtain ⟨f, hfW, relation⟩ := covers β hβ
    have selected := (M.realize_relationImageFormula (ordinalSuccessorTraceFormula φ)
      params A f hA).2 ⟨β, hβ, relation⟩
    exact ⟨f, ZFSet.mem_sep.2 ⟨hfW, selected⟩,
      (M.realize_ordinalSuccessorTraceFormula pairing unions φ params members
        (M.transitive hA hβ) (M.transitive hW hfW)).1 relation⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem groundRecursionStep_unique_on_traces {T : ZFSet.{u}} {k : Nat}
    {φ : SetFormula (k + 3)} {params : Fin k → ZFSet.{u}}
    (step : GroundOrdinalStepClosure M T φ params) :
    ∀ α ∈ T, ∀ p, OrdinalRecursionTrace (groundRecursionStep M φ params) α p →
      ∀ y z, groundRecursionStep M φ params α p y →
        groundRecursionStep M φ params α p z → y = z := by
  intro α hα p trace y z first second
  obtain ⟨w, _, _, unique⟩ := step α hα p first.1 trace
  exact (unique y first.2.1 first.2.2).trans (unique z second.2.1 second.2.2).symm

theorem exists_ordinalRecursionTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (ordinal : ordinalSetProperty T)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets)
    (step : GroundOrdinalStepClosure M T φ params) :
    ∃ f ∈ M.sets, OrdinalRecursionTrace (groundRecursionStep M φ params) T f := by
  have unique := M.groundRecursionStep_unique_on_traces step
  have successors : ∀ α ∈ T, ∃ f ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M φ params) (insert α α) f := by
    intro α
    induction α using ZFSet.inductionOn with
    | h α ih =>
      intro hα
      have hαM := M.transitive hT hα
      have ordinalα := ordinalSetProperty_member ordinal hα
      have subsetα : α ⊆ T := fun β hβ => ordinal.1 α hα β hβ
      obtain ⟨family, hFamily, traces, covers⟩ := M.collect_ordinalSuccessorTraces pairing unions
        separation collection φ params members hαM
        (fun β hβ => ih β hβ (subsetα hβ))
      have prefixTrace := OrdinalRecursionTrace.sUnion_successors ordinalα subsetα unique traces covers
      have hPrefix := M.union_mem unions hFamily
      obtain ⟨y, hy, relation, _⟩ := step α hα family.sUnion hPrefix prefixTrace
      exact ⟨insert (ZFSet.pair α y) family.sUnion,
        M.insert_mem pairing unions (M.orderedPair_mem pairing hαM hy) hPrefix,
        prefixTrace.succ ordinalα ⟨hPrefix, hy, relation⟩⟩
  obtain ⟨family, hFamily, traces, covers⟩ := M.collect_ordinalSuccessorTraces pairing unions
    separation collection φ params members hT successors
  exact ⟨family.sUnion, M.union_mem unions hFamily,
    OrdinalRecursionTrace.sUnion_successors ordinal (fun _ hx => hx) unique traces covers⟩

theorem ordinalRecursionTrace_entry {T f : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    {k : Nat} {φ : SetFormula (k + 3)} {params : Fin k → ZFSet.{u}}
    (step : GroundOrdinalStepClosure M T φ params)
    (trace : OrdinalRecursionTrace (groundRecursionStep M φ params) T f) :
    ∀ α ∈ T, ∀ y ∈ M.sets, ZFSet.pair α y ∈ f ↔
      Realize M.sets φ (extend α (extend (graphRestriction α f) (extend y params))) := by
  intro α hα y hy
  constructor
  · intro entry
    exact (trace.2 α hα y entry).2.2
  · intro relation
    obtain ⟨w, entry⟩ := trace.1.total hα
    have stepW := trace.2 α hα w entry
    have prefixTrace := trace.restrict (ordinalSetProperty_member ordinal hα)
      (fun β hβ => ordinal.1 α hα β hβ)
    have equal := M.groundRecursionStep_unique_on_traces step α hα _ prefixTrace y w
      ⟨stepW.1, hy, relation⟩ stepW
    rw [equal]
    exact entry

theorem exists_unique_ordinalRecursionTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (ordinal : ordinalSetProperty T)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets)
    (step : GroundOrdinalStepClosure M T φ params) :
    ∃ f ∈ M.sets, OrdinalRecursionTrace (groundRecursionStep M φ params) T f ∧
      (∀ g, OrdinalRecursionTrace (groundRecursionStep M φ params) T g → g = f) ∧
      ∀ α ∈ T, ∀ y ∈ M.sets, ZFSet.pair α y ∈ f ↔
        Realize M.sets φ (extend α (extend (graphRestriction α f) (extend y params))) := by
  obtain ⟨f, hf, trace⟩ := M.exists_ordinalRecursionTrace pairing unions separation collection
    hT ordinal φ params members step
  exact ⟨f, hf, trace, fun g other => other.unique trace ordinal (fun _ hx => hx)
    (M.groundRecursionStep_unique_on_traces step), M.ordinalRecursionTrace_entry ordinal step trace⟩

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCumulativeHierarchyLevels
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_cumulativeNext (a p x : ZFSet.{u}) :
    x ∈ M.cumulativeNext a p ↔
      x ∈ M.sets ∧ ∃ b ∈ a, ∃ v, ZFSet.pair b v ∈ p ∧ x ⊆ v := by
  rw [cumulativeNext, ZFSet.mem_sep, M.mem_groundPower]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hx, b, hb, v, entry, subset⟩
    exact ⟨⟨hx, fun z hz => ZFSet.mem_sUnion.2
      ⟨v, pair_second_mem_doubleUnion entry, subset hz⟩⟩, b, hb, v, entry, subset⟩

theorem realize_cumulativeMemberFormula {n} (x a p : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeMemberFormula x a p) env ↔
      ∃ b ∈ env a, ∃ v, ZFSet.pair b v ∈ env p ∧ env x ⊆ v := by
  simp only [cumulativeMemberFormula, realize_ex, Realize]
  constructor
  · rintro ⟨b, hbM, hb, v, hvM, pairCode, subsetCode⟩
    have mem2 : ∀ i, extend v (extend b env) i ∈ M.sets :=
      Fin.cases hvM (Fin.cases hbM members)
    exact ⟨b, hb, v,
      (BoundedFormula.truth_pairMembershipFormula 1 0 p.succ.succ _).1
        ((BoundedFormula.realize_toFormula M _ _ mem2).1 pairCode),
      (BoundedFormula.truth_subsetFormula x.succ.succ 0 _).1
        ((BoundedFormula.realize_toFormula M _ _ mem2).1 subsetCode)⟩
  · rintro ⟨b, hb, v, entry, subset⟩
    have hbM := M.transitive (members a) hb
    have hvM : v ∈ M.sets := M.transitive
      (M.transitive (M.transitive (members p) entry)
        (ZFSet.mem_pair.2 (Or.inr rfl))) (ZFSet.mem_pair.2 (Or.inr rfl))
    have mem2 : ∀ i, extend v (extend b env) i ∈ M.sets :=
      Fin.cases hvM (Fin.cases hbM members)
    exact ⟨b, hbM, hb, v, hvM,
      (BoundedFormula.realize_toFormula M _ _ mem2).2
        ((BoundedFormula.truth_pairMembershipFormula 1 0 p.succ.succ _).2 entry),
      (BoundedFormula.realize_toFormula M _ _ mem2).2
        ((BoundedFormula.truth_subsetFormula x.succ.succ 0 _).2 subset)⟩

theorem cumulativeNext_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets)
    {a p : ZFSet.{u}} (ha : a ∈ M.sets) (hp : p ∈ M.sets) :
    M.cumulativeNext a p ∈ M.sets := by
  let params := extend a (extend p Fin.elim0)
  have members : ∀ i, params i ∈ M.sets := Fin.cases ha (Fin.cases hp (fun i => Fin.elim0 i))
  have hBound := M.groundPower_mem powers
    (M.union_mem unions (M.union_mem unions (M.union_mem unions hp)))
  have selected := M.separation_mem separation (cumulativeMemberFormula 0 1 2)
    params members hBound
  have equal : ZFSet.sep (fun x => Realize M.sets (cumulativeMemberFormula 0 1 2)
      (extend x params)) (M.groundPower (⋃₀ ⋃₀ ⋃₀ p)) = M.cumulativeNext a p := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, cumulativeNext, ZFSet.mem_sep]
    constructor
    · rintro ⟨hx, code⟩
      exact ⟨hx, (M.realize_cumulativeMemberFormula 0 1 2 _
        (Fin.cases (M.transitive hBound hx) members)).1 code⟩
    · rintro ⟨hx, witness⟩
      exact ⟨hx, (M.realize_cumulativeMemberFormula 0 1 2 _
        (Fin.cases (M.transitive hBound hx) members)).2 witness⟩
  exact equal ▸ selected

theorem realize_cumulativeStepFormula {a p y : ZFSet.{u}}
    (ha : a ∈ M.sets) (hp : p ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets cumulativeStepFormula (extend a (extend p (extend y Fin.elim0))) ↔
      y = M.cumulativeNext a p := by
  simp only [cumulativeStepFormula, realize_imp, Realize]
  have decode (x : ZFSet.{u}) (hx : x ∈ M.sets) :=
    M.realize_cumulativeMemberFormula 0 1 2
      (extend x (extend a (extend p (extend y Fin.elim0))))
      (Fin.cases hx (Fin.cases ha (Fin.cases hp (Fin.cases hy (fun i => Fin.elim0 i)))))
  constructor
  · intro property
    apply ZFSet.ext
    intro x
    rw [M.mem_cumulativeNext]
    constructor
    · intro hx
      have hxM := M.transitive hy hx
      exact ⟨hxM, (decode x hxM).1 ((property x hxM).1 hx)⟩
    · rintro ⟨hx, witness⟩
      exact (property x hx).2 ((decode x hx).2 witness)
  · intro equal x hx
    constructor
    · intro member
      exact (decode x hx).2 ((M.mem_cumulativeNext a p x).1 (equal ▸ member)).2
    · intro witness
      exact equal ▸ (M.mem_cumulativeNext a p x).2 ⟨hx, (decode x hx).1 witness⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCumulativeHierarchyCode
variable {M : TransitiveGround.{u}} {T H : ZFSet.{u}}

theorem function (code : GroundCumulativeHierarchyCode M T H) : FunctionGraphOn T H := code.1

theorem entry_iff (code : GroundCumulativeHierarchyCode M T H)
    {a v : ZFSet.{u}} (ha : a ∈ T) (entry : ZFSet.pair a v ∈ H) (x : ZFSet.{u}) :
    x ∈ v ↔ x ∈ M.sets ∧ ∃ b ∈ a, ∃ w, ZFSet.pair b w ∈ H ∧ x ⊆ w := by
  rw [code.2 a ha v entry, M.mem_cumulativeNext]
  constructor
  · rintro ⟨hx, b, hb, w, edge, subset⟩
    exact ⟨hx, b, hb, w, (pair_mem_graphRestriction.1 edge).1, subset⟩
  · rintro ⟨hx, b, hb, w, edge, subset⟩
    exact ⟨hx, b, hb, w, pair_mem_graphRestriction.2 ⟨edge, hb⟩, subset⟩

theorem unique (code : GroundCumulativeHierarchyCode M T H)
    {J : ZFSet.{u}} (other : GroundCumulativeHierarchyCode M T J)
    (ordinal : ordinalSetProperty T) : H = J :=
  OrdinalRecursionTrace.unique code other ordinal (fun _ hx => hx)
    (fun _ _ _ _ _ _ first second => first.trans second.symm)

end GroundCumulativeHierarchyCode

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundCumulativeHierarchy
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (ordinal : ordinalSetProperty T) :
    ∃ H ∈ M.sets, GroundCumulativeHierarchyCode M T H ∧
      ∀ J, GroundCumulativeHierarchyCode M T J → J = H := by
  have closure : GroundOrdinalStepClosure M T cumulativeStepFormula Fin.elim0 := by
    intro a ha p hp _
    have haM := M.transitive hT ha
    have hy := M.cumulativeNext_mem unions powers separation haM hp
    refine ⟨M.cumulativeNext a p, hy,
      (M.realize_cumulativeStepFormula haM hp hy).2 rfl, ?_⟩
    intro z hz relation
    exact (M.realize_cumulativeStepFormula haM hp hz).1 relation
  obtain ⟨H, hH, trace, _, _⟩ := M.exists_unique_ordinalRecursionTrace
    pairing unions separation collection hT ordinal cumulativeStepFormula Fin.elim0
    (fun i => Fin.elim0 i) closure
  have code : GroundCumulativeHierarchyCode M T H := by
    refine ⟨trace.1, ?_⟩
    intro a ha v entry
    have step := trace.2 a ha v entry
    exact (M.realize_cumulativeStepFormula (M.transitive hT ha) step.1 step.2.1).1 step.2.2
  exact ⟨H, hH, code, fun J other => other.unique code ordinal⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundCumulativeHierarchyCode
open SetRealization
open scoped ZFSet
universe u
variable {M : TransitiveGround.{u}} {T H : ZFSet.{u}}
variable (code : GroundCumulativeHierarchyCode M T H) (ordinal : ordinalSetProperty T)
include code ordinal

theorem mem_iff_rank_lt {a v : ZFSet.{u}} (ha : a ∈ T)
    (entry : ZFSet.pair a v ∈ H) (x : ZFSet.{u}) :
    x ∈ v ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank a := by
  have all : ∀ a ∈ T, ∀ v, ZFSet.pair a v ∈ H → ∀ x,
      x ∈ v ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank a := by
    intro a
    induction a using ZFSet.inductionOn with
    | h a ih =>
      intro ha v entry x
      rw [code.entry_iff ha entry x]
      constructor
      · rintro ⟨hx, b, hb, w, edge, subset⟩
        have hbT := ordinal.1 a ha b hb
        have rankLe : ZFSet.rank x ≤ ZFSet.rank b := ZFSet.rank_le_iff.2
          (fun z hz => ((ih b hb hbT w edge z).1 (subset hz)).2)
        exact ⟨hx, rankLe.trans_lt (ZFSet.rank_lt_of_mem hb)⟩
      · rintro ⟨hx, rankLt⟩
        let b := ordinalCode (ZFSet.rank x)
        have hb : b ∈ a := by
          rw [ordinalSetProperty_eq_code_rank a (ordinalSetProperty_member ordinal ha)]
          exact (mem_ordinalCode_iff _ _).2 rankLt
        have hbT := ordinal.1 a ha b hb
        obtain ⟨w, edge⟩ := code.function.total hbT
        refine ⟨hx, b, hb, w, edge, ?_⟩
        intro z hz
        apply (ih b hb hbT w edge z).2
        refine ⟨M.transitive hx hz, ?_⟩
        simpa only [b, rank_ordinalCode] using ZFSet.rank_lt_of_mem hz
  exact all a ha v entry x

theorem value_transitive {a v : ZFSet.{u}} (ha : a ∈ T)
    (entry : ZFSet.pair a v ∈ H) : setTransitive v := by
  intro x hx z hz
  obtain ⟨hxM, rankX⟩ := (code.mem_iff_rank_lt ordinal ha entry x).1 hx
  exact (code.mem_iff_rank_lt ordinal ha entry z).2
    ⟨M.transitive hxM hz, (ZFSet.rank_lt_of_mem hz).trans rankX⟩

theorem value_rank {a v : ZFSet.{u}} (ha : a ∈ T)
    (entry : ZFSet.pair a v ∈ H) (haM : a ∈ M.sets) : ZFSet.rank v = ZFSet.rank a := by
  apply le_antisymm
  · exact ZFSet.rank_le_iff.2 (fun x hx => ((code.mem_iff_rank_lt ordinal ha entry x).1 hx).2)
  · apply ZFSet.rank_le_iff.2
    intro b hb
    exact ZFSet.rank_lt_of_mem ((code.mem_iff_rank_lt ordinal ha entry b).2
      ⟨M.transitive haM hb, ZFSet.rank_lt_of_mem hb⟩)

end PartitionPilot.Forcing.GroundCumulativeHierarchyCode

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCumulativeHierarchyCode
variable {M : TransitiveGround.{u}} {T H : ZFSet.{u}}

theorem value_mem (_code : GroundCumulativeHierarchyCode M T H)
    (hH : H ∈ M.sets) {a v : ZFSet.{u}} (entry : ZFSet.pair a v ∈ H) : v ∈ M.sets :=
  M.pair_right (M.transitive hH entry)

theorem ground_trace_iff
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (hT : T ∈ M.sets) (hH : H ∈ M.sets) :
    OrdinalRecursionTrace (groundRecursionStep M cumulativeStepFormula Fin.elim0) T H ↔
      GroundCumulativeHierarchyCode M T H := by
  constructor
  · intro trace
    refine ⟨trace.1, ?_⟩
    intro a ha v entry
    have step := trace.2 a ha v entry
    exact (M.realize_cumulativeStepFormula (M.transitive hT ha) step.1 step.2.1).1 step.2.2
  · intro code
    refine ⟨code.1, ?_⟩
    intro a ha v entry
    have haM := M.transitive hT ha
    have hp := M.graphRestriction_mem unions separation haM hH
    have hv := code.value_mem hH entry
    exact ⟨hp, hv, (M.realize_cumulativeStepFormula haM hp hv).2 (code.2 a ha v entry)⟩

end GroundCumulativeHierarchyCode

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundCumulativeLevel
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {a : ZFSet.{u}} (ha : a ∈ M.sets) (ordinal : ordinalSetProperty a) :
    ∃ H ∈ M.sets, ∃ V ∈ M.sets,
      GroundCumulativeHierarchyCode M (insert a a) H ∧ ZFSet.pair a V ∈ H ∧
      (∀ x, x ∈ V ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank a) ∧
      setTransitive V ∧ ZFSet.rank V = ZFSet.rank a := by
  have hs := M.insert_mem pairing unions ha ha
  have ordinalS := ordinalSetProperty_succ ordinal
  obtain ⟨H, hH, code, _⟩ := M.exists_groundCumulativeHierarchy pairing unions powers
    separation collection hs ordinalS
  obtain ⟨V, entry⟩ := code.function.total (ZFSet.mem_insert a a)
  exact ⟨H, hH, V, code.value_mem hH entry, code, entry,
    code.mem_iff_rank_lt ordinalS (ZFSet.mem_insert a a) entry,
    code.value_transitive ordinalS (ZFSet.mem_insert a a) entry,
    code.value_rank ordinalS (ZFSet.mem_insert a a) entry ha⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRegularFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_cumulativeLevelFormula_iff_graph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n} (a v : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeLevelFormula a v) env ↔
      ∃ H ∈ M.sets, GroundCumulativeHierarchyCode M (insert (env a) (env a)) H ∧
        ZFSet.pair (env a) (env v) ∈ H := by
  rw [cumulativeLevelFormula, realize_ex]
  have hS := M.insert_mem pairing unions (members a) (members a)
  constructor
  · rintro ⟨H, hH, trace, entry⟩
    rw [realize_reindex, map_extend, map_extend] at trace
    have empty : (fun i : Fin 0 => extend H env (Fin.elim0 i)) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    rw [empty] at trace
    have code := (M.realize_ordinalSuccessorTraceFormula pairing unions cumulativeStepFormula
      Fin.elim0 (fun i => Fin.elim0 i) (members a) hH).1 trace
    exact ⟨H, hH, (GroundCumulativeHierarchyCode.ground_trace_iff unions separation hS hH).1 code,
      (BoundedFormula.truth_pairMembershipFormula a.succ v.succ 0 _).1
        ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hH members)).1 entry)⟩
  · rintro ⟨H, hH, code, entry⟩
    refine ⟨H, hH, ?_, (BoundedFormula.realize_toFormula M _ _ (Fin.cases hH members)).2
      ((BoundedFormula.truth_pairMembershipFormula a.succ v.succ 0 _).2 entry)⟩
    rw [realize_reindex, map_extend, map_extend]
    have empty : (fun i : Fin 0 => extend H env (Fin.elim0 i)) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    rw [empty]
    exact (M.realize_ordinalSuccessorTraceFormula pairing unions cumulativeStepFormula
      Fin.elim0 (fun i => Fin.elim0 i) (members a) hH).2
        ((GroundCumulativeHierarchyCode.ground_trace_iff unions separation hS hH).2 code)

theorem realize_cumulativeLevelFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n} (a v : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (ordinal : ordinalSetProperty (env a)) :
    Realize M.sets (cumulativeLevelFormula a v) env ↔
      ∀ x, x ∈ env v ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank (env a) := by
  rw [M.realize_cumulativeLevelFormula_iff_graph pairing unions separation a v env members]
  constructor
  · rintro ⟨H, _, code, entry⟩
    exact code.mem_iff_rank_lt (ordinalSetProperty_succ ordinal) (ZFSet.mem_insert _ _) entry
  · intro property
    obtain ⟨H, hH, V, _, code, entry, exactV, _, _⟩ := M.exists_groundCumulativeLevel
      pairing unions powers separation collection (members a) ordinal
    have equal : env v = V := ZFSet.ext (fun x => (property x).trans (exactV x).symm)
    exact ⟨H, hH, code, equal ▸ entry⟩

theorem realize_cumulativeRankLtFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n} (x a : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (ordinal : ordinalSetProperty (env a)) :
    Realize M.sets (cumulativeRankLtFormula x a) env ↔
      ZFSet.rank (env x) < ZFSet.rank (env a) := by
  rw [cumulativeRankLtFormula, realize_ex]
  constructor
  · rintro ⟨V, hV, level, member⟩
    have exactV := (M.realize_cumulativeLevelFormula pairing unions powers separation collection
      a.succ 0 (extend V env) (Fin.cases hV members) ordinal).1 level
    exact ((exactV (env x)).1 member).2
  · intro bound
    obtain ⟨_, _, V, hV, _, _, exactV, _, _⟩ := M.exists_groundCumulativeLevel
      pairing unions powers separation collection (members a) ordinal
    exact ⟨V, hV, (M.realize_cumulativeLevelFormula pairing unions powers separation collection
      a.succ 0 (extend V env) (Fin.cases hV members) ordinal).2 exactV,
      (exactV (env x)).2 ⟨members x, bound⟩⟩

end TransitiveGround

end

section
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_cumulativeRankValueFormula {n} (x b : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeRankValueFormula x b) env ↔
      env b = ordinalCode (ZFSet.rank (env x)) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula b).toFormula env ∧
    Realize M.sets (ex _) env) ↔ _
  rw [BoundedFormula.realize_ordinalFormula M b env members, ← ordinalSetProperty_iff,
    realize_ex]
  constructor
  · rintro ⟨ordinal, s, hs, successor, first, second⟩
    have eqS := (BoundedFormula.truth_successorFormula 0 b.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hs members)).1 successor)
    change s = insert (env b) (env b) at eqS
    have ordinalS : ordinalSetProperty s := eqS ▸ ordinalSetProperty_succ ordinal
    have upper := (M.realize_cumulativeRankLtFormula pairing unions powers separation collection
      x.succ 0 (extend s env) (Fin.cases hs members) ordinalS).1 first
    change ZFSet.rank (env x) < ZFSet.rank s at upper
    have lower : ¬ ZFSet.rank (env x) < ZFSet.rank (env b) := by
      intro less
      exact second ((M.realize_cumulativeRankLtFormula pairing unions powers separation collection
        x.succ b.succ (extend s env) (Fin.cases hs members) ordinal).2 less)
    have rankS : ZFSet.rank s = Order.succ (ZFSet.rank (env b)) := by
      rw [eqS, ZFSet.rank_insert, max_eq_left (Order.le_succ _)]
    rw [rankS, Order.lt_succ_iff] at upper
    have equal := le_antisymm upper (le_of_not_gt lower)
    exact (ordinalSetProperty_eq_code_rank (env b) ordinal).trans (congrArg ordinalCode equal.symm)
  · intro equal
    have ordinal : ordinalSetProperty (env b) := equal ▸ ordinalSetProperty_ordinalCode _
    have hs := M.insert_mem pairing unions (members b) (members b)
    have mem2 : ∀ i, extend (insert (env b) (env b)) env i ∈ M.sets := Fin.cases hs members
    have ranks : ZFSet.rank (env b) = ZFSet.rank (env x) := by rw [equal, rank_ordinalCode]
    refine ⟨ordinal, insert (env b) (env b), hs,
      (BoundedFormula.realize_toFormula M _ _ mem2).2
        ((BoundedFormula.truth_successorFormula 0 b.succ _).2 rfl), ?_, ?_⟩
    · apply (M.realize_cumulativeRankLtFormula pairing unions powers separation collection
        x.succ 0 _ mem2 (ordinalSetProperty_succ ordinal)).2
      change ZFSet.rank (env x) < ZFSet.rank (insert (env b) (env b))
      rw [ZFSet.rank_insert, max_eq_left (Order.le_succ _), ranks]
      exact Order.lt_succ _
    · intro property
      have less := (M.realize_cumulativeRankLtFormula pairing unions powers separation collection
        x.succ b.succ _ mem2 ordinal).1 property
      exact (lt_irrefl (ZFSet.rank (env x))) (ranks ▸ less)

theorem realize_cumulativeRankEntryFormula {n} (z a k : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeRankEntryFormula z a k) env ↔
      ∃ x ∈ env a, ∃ b ∈ env k,
        env z = ZFSet.pair x b ∧ b = ordinalCode (ZFSet.rank x) := by
  simp only [cumulativeRankEntryFormula, realize_ex, Realize]
  constructor
  · rintro ⟨x, hxM, hx, b, hbM, hb, pairCode, rankCode⟩
    have mem2 : ∀ i, extend b (extend x env) i ∈ M.sets := Fin.cases hbM (Fin.cases hxM members)
    exact ⟨x, hx, b, hb,
      (BoundedFormula.truth_orderedPairFormula z.succ.succ 1 0 _).1
        ((BoundedFormula.realize_toFormula M _ _ mem2).1 pairCode),
      (M.realize_cumulativeRankValueFormula pairing unions powers separation collection 1 0 _ mem2).1
        rankCode⟩
  · rintro ⟨x, hx, b, hb, equal, rankValue⟩
    have hxM := M.transitive (members a) hx
    have hbM := M.transitive (members k) hb
    have mem2 : ∀ i, extend b (extend x env) i ∈ M.sets := Fin.cases hbM (Fin.cases hxM members)
    exact ⟨x, hxM, hx, b, hbM, hb,
      (BoundedFormula.realize_toFormula M _ _ mem2).2
        ((BoundedFormula.truth_orderedPairFormula z.succ.succ 1 0 _).2 equal),
      (M.realize_cumulativeRankValueFormula pairing unions powers separation collection 1 0 _ mem2).2
        rankValue⟩

end TransitiveGround

end

open SetFormula SetRealization
universe u

theorem pair_mem_cumulativeRankGraph (A K x b : ZFSet.{u}) :
    ZFSet.pair x b ∈ cumulativeRankGraph A K ↔
      x ∈ A ∧ b ∈ K ∧ b = ordinalCode (ZFSet.rank x) := by
  rw [cumulativeRankGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hy, c, hc, equal, value⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hy, hc, value⟩
  · rintro ⟨hx, hb, value⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hb⟩, x, hx, b, hb, rfl, value⟩

theorem cumulativeRankGraph_function {A K : ZFSet.{u}}
    (ordinal : ordinalSetProperty K) (ranks : ∀ x ∈ A, ZFSet.rank x < ZFSet.rank K) :
    ZFSet.IsFunc A K (cumulativeRankGraph A K) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  have hb : ordinalCode (ZFSet.rank x) ∈ K := by
    rw [ordinalSetProperty_eq_code_rank K ordinal]
    exact (mem_ordinalCode_iff _ _).2 (ranks x hx)
  exact ⟨ordinalCode (ZFSet.rank x),
    (pair_mem_cumulativeRankGraph A K x _).2 ⟨hx, hb, rfl⟩,
    fun b entry => ((pair_mem_cumulativeRankGraph A K x b).1 entry).2.2⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem cumulativeRankGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {A K : ZFSet.{u}} (hA : A ∈ M.sets) (hK : K ∈ M.sets) :
    cumulativeRankGraph A K ∈ M.sets := by
  let params := extend A (extend K Fin.elim0)
  have members : ∀ i, params i ∈ M.sets := Fin.cases hA (Fin.cases hK (fun i => Fin.elim0 i))
  have hBound := M.prod_mem pairing unions powers separation hA hK
  have selected := M.separation_mem separation (cumulativeRankEntryFormula 0 1 2) params members hBound
  have equal : ZFSet.sep (fun z => Realize M.sets (cumulativeRankEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod A K) = cumulativeRankGraph A K := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, cumulativeRankGraph, ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, formula⟩
      exact ⟨hz, (M.realize_cumulativeRankEntryFormula pairing unions powers separation collection
        0 1 2 _ (Fin.cases (M.transitive hBound hz) members)).1 formula⟩
    · rintro ⟨hz, value⟩
      exact ⟨hz, (M.realize_cumulativeRankEntryFormula pairing unions powers separation collection
        0 1 2 _ (Fin.cases (M.transitive hBound hz) members)).2 value⟩
  exact equal ▸ selected

end TransitiveGround

namespace GroundRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}} (regular : GroundRegular M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include regular pairing unions powers separation collection

theorem bound_rank_family {A : ZFSet.{u}} (hA : A ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (small : GroundBelow M A K)
    (ranks : ∀ x ∈ A, ZFSet.rank x < ZFSet.rank K) :
    ∃ b ∈ K, ∀ x ∈ A, ZFSet.rank x < ZFSet.rank b := by
  have ground := M.cumulativeRankGraph_mem pairing unions powers separation collection hA hK
  have function := cumulativeRankGraph_function ordinal ranks
  obtain ⟨b, hb, bounded⟩ := regular.bound_small_domain pairing unions powers separation
    hA hK ground small function
  refine ⟨b, hb, ?_⟩
  intro x hx
  obtain ⟨c, entry, _⟩ := function.2 x hx
  have value := ((pair_mem_cumulativeRankGraph A K x c).1 entry).2.2
  have bound := ZFSet.rank_lt_of_mem (bounded x c entry)
  simpa only [value, rank_ordinalCode] using bound

theorem rank_lt_of_small {A : ZFSet.{u}} (hA : A ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (small : GroundBelow M A K)
    (ranks : ∀ x ∈ A, ZFSet.rank x < ZFSet.rank K) : ZFSet.rank A < ZFSet.rank K := by
  obtain ⟨b, hb, bounded⟩ := regular.bound_rank_family pairing unions powers separation collection
    hA hK ordinal small ranks
  exact (ZFSet.rank_le_iff.2 (fun x hx => bounded x hx)).trans_lt (ZFSet.rank_lt_of_mem hb)

end GroundRegular

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCantorDiagonal
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem truth_injectionDiagonalFormula {n} (x p f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (injectionDiagonalFormula x p f) env ↔
      ∃ X ∈ env p, ZFSet.pair X (env x) ∈ env f ∧ env x ∉ X := by
  simp only [injectionDiagonalFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_injectionDiagonal (A f x : ZFSet.{u}) :
    x ∈ M.injectionDiagonal A f ↔
      x ∈ A ∧ ∃ X ∈ M.groundPower A, ZFSet.pair X x ∈ f ∧ x ∉ X := ZFSet.mem_sep

theorem injectionDiagonal_mem
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    M.injectionDiagonal A f ∈ M.sets := by
  let params := extend (M.groundPower A) (extend f Fin.elim0)
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases (M.groundPower_mem powers hA) (Fin.cases hf (fun i => Fin.elim0 i))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.injectionDiagonalFormula 0 1 2) params members hA
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.injectionDiagonalFormula 0 1 2) (extend x params)) A =
      M.injectionDiagonal A f := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, M.mem_injectionDiagonal, BoundedFormula.truth_injectionDiagonalFormula]
    rfl
  exact eq ▸ selected

theorem groundPower_not_embeddable_self
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : ¬ M.groundEmbeddable (M.groundPower A) A := by
  classical
  rintro ⟨f, hf, code⟩
  let D := M.injectionDiagonal A f
  have hD : D ∈ M.groundPower A := (M.mem_groundPower A D).2
    ⟨M.injectionDiagonal_mem powers separation hA hf,
      fun _ hx => (M.mem_injectionDiagonal A f _).1 hx |>.1⟩
  obtain ⟨y, entry, _⟩ := code.function.2 D hD
  have hy : y ∈ A := (ZFSet.pair_mem_prod.1 (code.function.1 entry)).2
  have outside : y ∉ D := by
    intro inside
    obtain ⟨_, X, _, image, missing⟩ := (M.mem_injectionDiagonal A f y).1 inside
    have same : X = D := code.injective X D y image entry
    exact missing (same.symm ▸ inside)
  exact outside ((M.mem_injectionDiagonal A f y).2 ⟨hy, D, hD, entry, outside⟩)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFilterCopies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem meetFilter_copyPullback {A L rA rL μA μL e F : ZFSet.{u}}
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (nonempty : (copyPullback A L e F).Nonempty) :
    MeetFilterCode A rA μA (copyPullback A L e F) where
  subset := fun x hx => ((mem_copyPullback A L e F x).1 hx).1
  nonempty := nonempty
  upward := by
    intro x hx y hy lower
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨y', yy', _⟩ := embedding.injection.function.2 y hy
    have hyL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 yy')).2
    have hyF := target.upward x' hxF y' hyL (embedding.monotone x y x' y' lower xx' yy')
    exact (mem_copyPullback A L e F y).2 ⟨hy, y', hyF, hyL, yy'⟩
  closed_meet := by
    intro x hx y hy z meetXY
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨_, y', hyF, _, yy'⟩ := (mem_copyPullback A L e F y).1 hy
    have hzA := (ZFSet.pair_mem_prod.1 (source.operation.1 meetXY)).2
    obtain ⟨z', zz', _⟩ := embedding.injection.function.2 z hzA
    have hzL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 zz')).2
    have hzF := target.closed_meet x' hxF y' hyF z'
      (embedding.map_meet x y z x' y' z' meetXY xx' yy' zz')
    exact (mem_copyPullback A L e F z).2 ⟨hzA, z', hzF, hzL, zz'⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem internalCountableBelow_copy_of_all_filters
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L rA rL μA μL e F : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (he : e ∈ M.sets) (hF : F ∈ M.sets)
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (earlier : ∀ P ∈ M.sets, MeetFilterCode A rA μA P → M.InternalCountableBelow rA P P) :
    M.InternalCountableBelow rL F (F ∩ relationImage A L e) := by
  classical
  by_cases nonempty : (copyPullback A L e F).Nonempty
  · have pullbackMember := M.copyPullback_mem pairing unions powers separation hA hL he hF
    have pullbackFilter := meetFilter_copyPullback source target embedding nonempty
    exact M.internalCountableBelow_copy_pullback pairing unions powers separation infinite hL he
      embedding.injection embedding.monotone
      (earlier (copyPullback A L e F) pullbackMember pullbackFilter)
  · refine ⟨∅, M.empty_mem ⟨F, hF⟩, M.empty_groundEmbeddable ZFSet.omega ⟨F, hF⟩,
      ZFSet.empty_subset F, ?_⟩
    intro x hx
    obtain ⟨hxF, image⟩ := ZFSet.mem_inter.1 hx
    obtain ⟨hxL, y, hyA, yx⟩ := (mem_relationImage A L e x).1 image
    exact False.elim (nonempty ⟨y,
      (mem_copyPullback A L e F y).2 ⟨hyA, x, hxF, hxL, yx⟩⟩)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskRepresentativeCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula
universe u

theorem truth_meetFilterFormula {n} (P r μ F : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (meetFilterFormula P r μ F) env ↔
      MeetFilterCode (env P) (env r) (env μ) (env F) := by
  simp only [meetFilterFormula, Truth, truth_exMem, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨subset, ⟨x, hx, _⟩, upward, closed⟩
    exact ⟨subset, ⟨x, hx⟩, upward, fun x hx y hy z entry =>
      closed x hx y hy z (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2 entry⟩
  · intro filter
    obtain ⟨x, hx⟩ := filter.nonempty
    exact ⟨filter.subset, ⟨x, hx, trivial⟩, filter.upward,
      fun x hx y hy z _ entry => filter.closed_meet x hx y hy z entry⟩

theorem truth_restrictedActionFormula {n} (P r A g source target base : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (restrictedActionFormula P r A g source target base) env ↔
      RestrictedActionCode (env P) (env r) (env A) (env g) (env source) (env target) (env base) := by
  simp only [restrictedActionFormula, Truth, truth_relationBetweenFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_imp, ← iff_def]
  exact ⟨fun ⟨shape, target, entries⟩ => ⟨shape, target, entries⟩,
    fun code => ⟨code.shape, code.target_entry, code.entries⟩⟩

end BoundedFormula

universe u

namespace BoundedFormula

open SetFormula

theorem truth_eligibleTaskFormula {n} (P G r μ A source target base separator F : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (eligibleTaskFormula P G r μ A source target base separator F) env ↔
      EligibleTaskCode (env P) (env G) (env r) (env μ) (env A)
        (env source) (env target) (env base) (env separator) (env F) := by
  simp only [eligibleTaskFormula, Truth, truth_pairMembershipFormula, truth_exMem,
    truth_restrictedActionFormula, truth_meetFilterFormula P r μ F env meet]
  constructor
  · rintro ⟨hs, ht, he, filter, lower, strict, upper, representative⟩
    exact ⟨hs, ht, he, filter, lower, strict, upper, representative⟩
  · intro code
    exact ⟨code.source_mem, code.target_mem, code.separator_mem, code.filter,
      code.lower, code.strict, code.upper, code.representative⟩

end BoundedFormula

theorem literalTaskCode_mem_eligibleTaskSet (P G r μ A R U Labels a c base e F label : ZFSet.{u}) :
    literalTaskCode a c base e F label ∈ eligibleTaskSet P G r μ A R U Labels ↔
      a ∈ P ∧ c ∈ P ∧ base ∈ R ∧ e ∈ P ∧ F ∈ U ∧ label ∈ Labels ∧
        EligibleTaskCode P G r μ A a c base e F := by
  rw [mem_eligibleTaskSet]
  constructor
  · rintro ⟨a', ha, c', hc, base', hBase, e', he, F', hF, label', hLabel, equal, code⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := literalTaskCode_inj.1 equal
    exact ⟨ha, hc, hBase, he, hF, hLabel, code⟩
  · rintro ⟨ha, hc, hBase, he, hF, hLabel, code⟩
    exact ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩

namespace BoundedFormula

open SetFormula

theorem truth_eligibleTaskEntryFormula {n} (z P G r μ A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (eligibleTaskEntryFormula z P G r μ A R U Labels) env ↔
      env z ∈ eligibleTaskSet (env P) (env G) (env r) (env μ) (env A) (env R) (env U) (env Labels) := by
  rw [mem_eligibleTaskSet]
  simp only [eligibleTaskEntryFormula, truth_exMem, Truth, truth_literalTaskFormula]
  refine exists_congr fun a => and_congr_right fun _ =>
    exists_congr fun c => and_congr_right fun _ =>
    exists_congr fun base => and_congr_right fun _ =>
    exists_congr fun e => and_congr_right fun _ =>
    exists_congr fun F => and_congr_right fun _ =>
    exists_congr fun label => and_congr_right fun _ => ?_
  exact and_congr Iff.rfl (truth_eligibleTaskFormula _ _ _ _ _ _ _ _ _ _
    (extend label (extend F (extend e (extend base (extend c (extend a env)))))) meet)

end BoundedFormula

namespace BoundedFormula

open SetFormula

theorem truth_taskRepresentativeFormula {n} (task g P r A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskRepresentativeFormula task g P r A R U Labels) env ↔
      TaskRepresentative (env P) (env r) (env A) (env R) (env U) (env Labels) (env task) (env g) := by
  simp only [taskRepresentativeFormula, truth_exMem, Truth, truth_literalTaskFormula,
    truth_restrictedActionFormula, TaskRepresentative]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundOmegaOneRowModel
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)

theorem groundOmegaOne_successor {A : ZFSet.{u}}
    (hA : A ∈ M.groundOmegaOne pairing unions powers separation collection infinite) :
    insert A A ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨hAM, ordinal, small⟩ := (spec.2.2.1 A).1 hA
  exact (spec.2.2.1 _).2 ⟨M.insert_mem pairing unions hAM hAM,
    ordinalSetProperty_succ ordinal,
    M.groundEmbeddable_insert pairing unions powers separation infinite hAM hAM small⟩

theorem groundOmegaOne_countable_bound
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets)
    (subset : R ⊆ M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.groundEmbeddable R ZFSet.omega) :
    ∃ B ∈ M.groundOmegaOne pairing unions powers separation collection infinite,
      ∀ A ∈ R, A ∈ B := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have ordinals : ∀ A ∈ R, ordinalSetProperty A := fun A hA => ((spec.2.2.1 A).1 (subset hA)).2.1
  have membersSmall : ∀ A ∈ R, M.groundEmbeddable A ZFSet.omega :=
    fun A hA => ((spec.2.2.1 A).1 (subset hA)).2.2
  have hU := M.union_mem unions hR
  have ordU := ordinalSetProperty_sUnion ordinals
  have smallU := M.groundCountable_family_union pairing unions powers separation infinite choice
    hR small membersSmall
  have uC := (spec.2.2.1 (⋃₀ R)).2 ⟨hU, ordU, smallU⟩
  refine ⟨insert (⋃₀ R) (⋃₀ R),
    M.groundOmegaOne_successor pairing unions powers separation collection infinite uC, ?_⟩
  intro A hA
  have included : A ⊆ ⋃₀ R := fun x hx => ZFSet.mem_sUnion.2 ⟨A, hA, hx⟩
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff A).1 (ordinals A hA)
  obtain ⟨b, eqB⟩ := (ordinalSetProperty_iff (⋃₀ R)).1 ordU
  rw [eqA, eqB] at included ⊢
  rw [← ordinalCode_succ, mem_ordinalCode_iff]
  exact Order.lt_succ_iff.2 ((ordinalCode_subset_iff a b).1 included)

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundOrdinalPartitionInjectionAssembly
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pair_mem_definableRelation {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A B x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.definableRelation φ params A B ↔
      x ∈ A ∧ y ∈ B ∧ Realize M.sets φ (extend x (extend y params)) := by
  rw [definableRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, equal, relation⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, relation⟩
  · rintro ⟨hx, hy, relation⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, relation⟩

theorem realize_definableRelationEntryFormula {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets (definableRelationEntryFormula φ) (extend z (extend A (extend B params))) ↔
      ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair x y ∧ Realize M.sets φ (extend x (extend y params)) := by
  simp only [definableRelationEntryFormula, realize_ex, Realize]
  constructor
  · rintro ⟨x, hx, inA, y, hy, inB, pair, relation⟩
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hy (Fin.cases hx (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    have exactPair := (BoundedFormula.truth_orderedPairFormula 2 1 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ ground).1 pair)
    exact ⟨x, inA, y, inB, exactPair, (realize_binaryApplication M.sets φ _ _ _ _).1 relation⟩
  · rintro ⟨x, hx, y, hy, pair, relation⟩
    have hxM := M.transitive hA hx
    have hyM := M.transitive hB hy
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases hxM (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    exact ⟨x, hxM, hx, y, hyM, hy,
      (BoundedFormula.realize_toFormula M _ _ ground).2
        ((BoundedFormula.truth_orderedPairFormula 2 1 0 _).2 pair),
      (realize_binaryApplication M.sets φ _ _ _ _).2 relation⟩

theorem definableRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    M.definableRelation φ params A B ∈ M.sets := by
  have hProd := M.prod_mem pairing unions powers separation hA hB
  have selected := M.separation_mem separation (definableRelationEntryFormula φ)
    (extend A (extend B params)) (Fin.cases hA (Fin.cases hB members)) hProd
  have equal : ZFSet.sep (fun z => Realize M.sets (definableRelationEntryFormula φ)
      (extend z (extend A (extend B params)))) (ZFSet.prod A B) = M.definableRelation φ params A B := by
    apply ZFSet.ext
    intro z
    rw [definableRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_definableRelationEntryFormula φ params members hA hB z (M.transitive hProd hz)
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStandardInaccessible
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)

theorem groundOmegaOne_subset_of_not_countable {α : ZFSet.{u}}
    (ordinal : ordinalSetProperty α) (uncountable : ¬ M.groundEmbeddable α ZFSet.omega) :
    M.groundOmegaOne pairing unions powers separation collection infinite ⊆ α := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff α).1 ordinal
  obtain ⟨c, eqC⟩ := (ordinalSetProperty_iff _).1 spec.2.1
  by_cases lower : a < c
  · have inside : α ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
      rw [eqA, eqC, mem_ordinalCode_iff]
      exact lower
    exact False.elim (uncountable ((spec.2.2.1 α).1 inside).2.2)
  · rw [eqC, eqA, ordinalCode_subset_iff]
    exact le_of_not_gt lower

end TransitiveGround

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (hK : K ∈ M.sets)
include conditions hK

theorem groundOmegaOne_bound :
    ∃ α ∈ K, M.groundOmegaOne pairing unions powers separation collection infinite ⊆ α := by
  have hOmega := M.omega_mem separation infinite
  have hPower := M.groundPower_mem powers hOmega
  obtain ⟨α, hα, f, hf, injection⟩ := conditions.2.2.2 ZFSet.omega conditions.2.1
  have hAlpha := M.transitive hK hα
  have uncountable : ¬ M.groundEmbeddable α ZFSet.omega := by
    rintro ⟨g, hg, countable⟩
    apply M.groundPower_not_embeddable_self powers separation hOmega
    exact ⟨relationCompose (M.groundPower ZFSet.omega) α ZFSet.omega f g,
      M.relationCompose_mem pairing unions powers separation hPower hAlpha hOmega hf hg,
      injection.compose countable⟩
  exact ⟨α, hα, M.groundOmegaOne_subset_of_not_countable pairing unions powers separation
    collection infinite (ordinalSetProperty_member conditions.1 hα) uncountable⟩

theorem groundOmegaOne_mem :
    M.groundOmegaOne pairing unions powers separation collection infinite ∈ K := by
  obtain ⟨α, hα, subset⟩ := conditions.groundOmegaOne_bound pairing unions powers separation
    collection infinite hK
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨c, eqC⟩ := (ordinalSetProperty_iff _).1 spec.2.1
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff α).1 (ordinalSetProperty_member conditions.1 hα)
  have bound : c ≤ a := by
    rw [eqC, eqA] at subset
    exact (ordinalCode_subset_iff c a).1 subset
  rcases lt_or_eq_of_le bound with lower | same
  · apply conditions.1.1 α hα
    rw [eqC, eqA, mem_ordinalCode_iff]
    exact lower
  · rw [eqC, same, ← eqA]
    exact hα

end GroundInaccessibleConditions




end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundTestedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem mem_groundMeetFilters (P r μ F : ZFSet.{u}) :
    F ∈ M.groundMeetFilters P r μ ↔ F ∈ M.sets ∧ MeetFilterCode P r μ F := by
  rw [groundMeetFilters, ZFSet.mem_sep, M.mem_groundPower]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.subset⟩, h.2⟩⟩

theorem groundMeetFilters_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets)
    {P r μ : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundMeetFilters P r μ ∈ M.sets := by
  let params := extend P (extend r (extend μ Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.meetFilterFormula 1 2 3 0) params
    (Fin.cases hP (Fin.cases hr (Fin.cases hμ (fun i => Fin.elim0 i))))
    (M.groundPower_mem powers hP)
  have equal : ZFSet.sep (fun F => BoundedFormula.Truth
      (BoundedFormula.meetFilterFormula 1 2 3 0) (extend F params)) (M.groundPower P) =
      M.groundMeetFilters P r μ := by
    apply ZFSet.ext
    intro F
    rw [ZFSet.mem_sep, groundMeetFilters, ZFSet.mem_sep]
    exact and_congr_right (fun _ =>
      BoundedFormula.truth_meetFilterFormula 1 2 3 0 (extend F params) meet)
  exact equal ▸ selected

end TransitiveGround

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundEligibleCaps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundEligibleTasks_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundEligibleTasks P G r μ A Labels ∈ M.sets := by
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  have hR : R ∈ M.sets := M.groundRelations_mem pairing unions powers separation hP hP
  have hU : U ∈ M.sets := M.groundMeetFilters_mem powers separation hP hr hμ meet
  let params := extend P (extend G (extend r (extend μ (extend A
    (extend R (extend U (extend Labels Fin.elim0)))))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hP (Fin.cases hG (Fin.cases hr (Fin.cases hμ (Fin.cases hA
      (Fin.cases hR (Fin.cases hU (Fin.cases hLabels (fun i => Fin.elim0 i))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.eligibleTaskEntryFormula 0 1 2 3 4 5 6 7 8) params members
    (M.literalTaskBound_mem pairing unions powers separation hP hR hU hLabels)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.eligibleTaskEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (literalTaskBound P R U Labels) = M.groundEligibleTasks P G r μ A Labels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_eligibleTaskEntryFormula _ _ _ _ _ _ _ _ _ _ meet]
    exact ⟨And.right, fun hz => ⟨eligibleTaskSet_subset P G r μ A R U Labels hz, hz⟩⟩
  exact equal ▸ selected

theorem literalTaskCode_mem_groundEligibleTasks
    (P G r μ A Labels a c base e F label : ZFSet.{u}) :
    literalTaskCode a c base e F label ∈ M.groundEligibleTasks P G r μ A Labels ↔
      label ∈ Labels ∧ base ∈ M.sets ∧ F ∈ M.sets ∧ EligibleTaskCode P G r μ A a c base e F := by
  rw [groundEligibleTasks, literalTaskCode_mem_eligibleTaskSet,
    M.mem_groundRelations, M.mem_groundMeetFilters]
  constructor
  · rintro ⟨_, _, ⟨hBase, _⟩, _, ⟨hF, _⟩, hLabel, code⟩
    exact ⟨hLabel, hBase, hF, code⟩
  · rintro ⟨hLabel, hBase, hF, code⟩
    obtain ⟨g, _, represented⟩ := code.representative
    exact ⟨code.source_mem, code.target_mem, ⟨hBase, represented.shape⟩,
      code.separator_mem, ⟨hF, code.filter⟩, hLabel, code⟩






end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem groundPower_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {A : ZFSet.{u}} (bound : ZFSet.rank A < o) : ZFSet.rank (M.groundPower A) < o := by
  have subset : M.groundPower A ⊆ ZFSet.powerset A := fun _ hz => (ZFSet.mem_sep.1 hz).1
  have rankBound := ZFSet.rank_mono subset
  rw [ZFSet.rank_powerset] at rankBound
  exact rankBound.trans_lt (limit.succ_lt bound)

theorem groundRelations_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {A B : ZFSet.{u}} (source : ZFSet.rank A < o) (target : ZFSet.rank B < o) :
    ZFSet.rank (M.groundRelations A B) < o :=
  M.groundPower_rank_lt limit (rank_product_lt limit source target)

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundEligibleTaskSetRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundEligibleTaskElementFormula {n} (z P G r μ A Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundEligibleTaskElementFormula z P G r μ A Labels) env ↔
      env z ∈ M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels) := by
  rw [groundEligibleTaskElementFormula, realize_exBlock]
  constructor
  · rintro ⟨fields, fieldMembers, label, tuple, eligible⟩
    have bounds := extendMany_members 6 fields env fieldMembers members
    have code := (BoundedFormula.realize_toFormula M _ _ bounds).1 tuple
    rw [BoundedFormula.truth_literalTaskFormula] at code
    simp only [extendMany_prefix, extendMany_suffix] at code label
    have task := (BoundedFormula.realize_toFormula M _ _ bounds).1 eligible
    have taskMeaning := (BoundedFormula.truth_eligibleTaskFormula
      (suffixIndex n 6 P) (suffixIndex n 6 G) (suffixIndex n 6 r)
      (suffixIndex n 6 μ) (suffixIndex n 6 A) (prefixIndex n 6 0) (prefixIndex n 6 1)
      (prefixIndex n 6 2) (prefixIndex n 6 3) (prefixIndex n 6 4)
      (extendMany 6 fields env) meet).1 task
    simp only [extendMany_prefix, extendMany_suffix] at taskMeaning
    rw [code, M.literalTaskCode_mem_groundEligibleTasks]
    exact ⟨label, fieldMembers 2, fieldMembers 4, taskMeaning⟩
  · intro member
    obtain ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, equal, eligible⟩ :=
      (mem_eligibleTaskSet _ _ _ _ _ _ _ _ _).1 member
    have baseGround := ((M.mem_groundRelations _ _ base).1 hBase).1
    have filterGround := ((M.mem_groundMeetFilters _ _ _ F).1 hF).1
    let fields := literalTaskField a c base e F label
    have fieldMembers : ∀ j, fields j ∈ M.sets :=
      Fin.cases (M.transitive (members P) ha) (Fin.cases (M.transitive (members P) hc)
        (Fin.cases baseGround (Fin.cases (M.transitive (members P) he)
          (Fin.cases filterGround (Fin.cases (M.transitive (members Labels) hLabel)
            (fun i => Fin.elim0 i))))))
    have bounds := extendMany_members 6 fields env fieldMembers members
    refine ⟨fields, fieldMembers, ?_, ?_, ?_⟩
    · exact hLabel
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      rw [BoundedFormula.truth_literalTaskFormula]
      exact equal
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      exact (BoundedFormula.truth_eligibleTaskFormula
        (suffixIndex n 6 P) (suffixIndex n 6 G) (suffixIndex n 6 r)
        (suffixIndex n 6 μ) (suffixIndex n 6 A) (prefixIndex n 6 0) (prefixIndex n 6 1)
        (prefixIndex n 6 2) (prefixIndex n 6 3) (prefixIndex n 6 4)
        (extendMany 6 fields env) meet).2 eligible

theorem realize_groundEligibleTasksFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (output P G r μ A Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundEligibleTasksFormula output P G r μ A Labels) env ↔
      env output = M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => M.transitive (M.groundEligibleTasks_mem pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A) (members Labels) meet) hz)
  intro z hz
  exact M.realize_groundEligibleTaskElementFormula 0 P.succ G.succ r.succ μ.succ A.succ Labels.succ
    (extend z env) (Fin.cases hz members) meet

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GrowthLayerSourceCongruence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

namespace CodedGrowthLayer

open SetFormula

theorem internal_countable_essentials
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L F T r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hL : L ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (ht : t ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (earlier : ∀ s ∈ t, Space s ∈ M.sets ∧
      MeetOrderCode (Space s) (sourceOrder s) (sourceMeet s) ∧
      ∀ P ∈ M.sets, MeetFilterCode (Space s) (sourceOrder s) (sourceMeet s) P →
        M.InternalCountableBelow (sourceOrder s) P P) :
    M.InternalCountableBelow r F (essentialBirthFiber F T r birth t) := by
  classical
  have groundFiber := M.essentialBirthFiber_mem separation hF hT hr hBirth ht
  have positive : essentialBirthFiber F T r birth t ⊆ F :=
    fun _ hx => birthEssentialSet_subset F T r birth
      (essentialBirthFiber_subset F T r birth t hx)
  have points : essentialBirthFiber F T r birth t ⊆ L := fun _ hx => filter.subset (positive hx)
  cases layer with
  | countablePoints D _ small cover =>
    have subset : essentialBirthFiber F T r birth t ⊆ D := by
      intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    have countableFiber := M.groundEmbeddable_restrict separation groundFiber
      (M.omega_mem separation infinite) subset small
    exact M.internalCountableBelow_of_countable groundFiber countableFiber positive
      (fun x hx => meet.order.refl x (points hx))
  | copies I parts groundI small groundParts index e previous groundCopy embedding cover inCopy =>
    apply M.internalCountableBelow_indexed_union pairing unions powers separation infinite choice
      groundI hr hF groundFiber groundParts small
    · intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    · intro i hi
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i hi)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i hi) hF source filter (embedding i hi) sourceBases
      apply basis.mono
      intro x hx
      obtain ⟨hxFiber, part⟩ := (mem_relationFiber (essentialBirthFiber F T r birth t) parts i x).1 hx
      exact ZFSet.mem_inter.2 ⟨positive hxFiber, inCopy i hi x (points hxFiber) part⟩
  | separated I index e previous groundCopy embedding component cover separated =>
    by_cases inhabited : (essentialBirthFiber F T r birth t).Nonempty
    · obtain ⟨x, hx⟩ := inhabited
      let representative : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨x, points hx, ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2⟩
      let i := component representative
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i) hF source filter (embedding i) sourceBases
      apply basis.mono
      intro y hy
      let current : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨y, points hy, ((mem_essentialBirthFiber F T r birth t y).1 hy).2.2⟩
      have same : component current = i := by
        by_contra different
        exact birthEssentials_no_oldBridge meet filter born
          (essentialBirthFiber_subset F T r birth t hy)
          (essentialBirthFiber_subset F T r birth t hx)
          current.property.2 representative.property.2 (separated current representative different)
      have inside := cover current
      rw [same] at inside
      exact ZFSet.mem_inter.2 ⟨positive hy, inside⟩
    · have empty : essentialBirthFiber F T r birth t = ∅ := by
        apply ZFSet.ext
        intro x
        exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
          fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
      rw [empty]
      exact M.internalCountableBelow_empty ⟨F, hF⟩ r F

end CodedGrowthLayer

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableLayerCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem truth_countableLayerFormula {n} (L birth t D N injection : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (countableLayerFormula L birth t D N injection) env ↔
      CountableLayerCode (env L) (env birth) (env t) (env D) (env N) (env injection) := by
  simp only [countableLayerFormula, Truth, truth_injectionFormula, truth_imp,
    truth_pairMembershipFormula]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.small, h.cover⟩⟩

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLayerBirthFibers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem truth_layerBirthFiberFormula {n} (F L birth t : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (layerBirthFiberFormula F L birth t) env ↔
      env F = layerBirthFiber (env L) (env birth) (env t) := by
  simp only [layerBirthFiberFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change ((∀ x ∈ env F, x ∈ env L) ∧ ∀ x ∈ env L,
    (x ∈ env F → ZFSet.pair x (env t) ∈ env birth) ∧
      (ZFSet.pair x (env t) ∈ env birth → x ∈ env F)) ↔ _
  constructor
  · rintro ⟨subset, spec⟩
    apply ZFSet.ext
    intro x
    rw [mem_layerBirthFiber]
    exact ⟨fun hx => ⟨subset x hx, (spec x (subset x hx)).1 hx⟩,
      fun ⟨hx, born⟩ => (spec x hx).2 born⟩
  · intro eq
    rw [eq]
    exact ⟨fun _ hx => (mem_layerBirthFiber _ _ _ _).1 hx |>.1,
      fun x hx => ⟨fun born => (mem_layerBirthFiber _ _ _ _).1 born |>.2,
        fun born => (mem_layerBirthFiber _ _ _ _).2 ⟨hx, born⟩⟩⟩

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedGrowthLayerFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_oldBridgeFormula {n} (L r μ birth t x y : Fin n) (env : Fin n → ZFSet.{u})
    (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Truth (oldBridgeFormula L r μ birth t x y) env ↔
      OldBridgeCode (env L) (env r) (env μ) (env birth) (env t) (env x) (env y) := by
  simp only [oldBridgeFormula, truth_disj, truth_exMem, Truth,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, OldBridgeCode]
  constructor
  · rintro (⟨z, _, a, ha, entry, born⟩ | ⟨z, hz, a, ha, born, bridge⟩)
    · exact Or.inl ⟨z, a, entry, born, ha⟩
    · exact Or.inr ⟨z, hz, a, born, ha, bridge⟩
  · rintro (⟨z, a, entry, born, ha⟩ | ⟨z, hz, a, born, ha, bridge⟩)
    · exact Or.inl ⟨z, (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2, a, ha, entry, born⟩
    · exact Or.inr ⟨z, hz, a, ha, born, bridge⟩

theorem truth_meetEmbeddingFormula {n} (P L rP rL μP μL e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (meetEmbeddingFormula P L rP rL μP μL e) env ↔
      MeetEmbeddingCode (env P) (env L) (env rP) (env rL) (env μP) (env μL) (env e) := by
  simp only [meetEmbeddingFormula, Truth, truth_injectionFormula, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨injection, monotone, meet⟩
    have bounds {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env e) :
        x ∈ env P ∧ y ∈ env L := ZFSet.pair_mem_prod.1 (injection.function.1 entry)
    refine ⟨injection, ?_, ?_⟩
    · intro x y x' y' lower first second
      exact monotone x (bounds first).1 y (bounds second).1
        x' (bounds first).2 y' (bounds second).2 ⟨lower, first, second⟩
    · intro x y z x' y' z' output first second third
      exact meet x (bounds first).1 y (bounds second).1 z (bounds third).1
        x' (bounds first).2 y' (bounds second).2 z' (bounds third).2
        ⟨output, first, second, third⟩
  · intro code
    exact ⟨code.injection,
      fun x _ y _ x' _ y' _ h => code.monotone x y x' y' h.1 h.2.1 h.2.2,
      fun x _ y _ z _ x' _ y' _ z' _ h =>
        code.map_meet x y z x' y' z' h.1 h.2.1 h.2.2.1 h.2.2.2⟩

theorem truth_groupEmbeddingFormula {n} (G H mG mH oneG oneH e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (groupEmbeddingFormula G H mG mH oneG oneH e) env ↔
      GroupEmbeddingCode (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env e) := by
  simp only [groupEmbeddingFormula, Truth, truth_injectionFormula, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨injection, one, mul⟩
    have bounds {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env e) :
        x ∈ env G ∧ y ∈ env H := ZFSet.pair_mem_prod.1 (injection.function.1 entry)
    refine ⟨injection, one, ?_⟩
    intro a b c a' b' c' product first second third
    exact mul a (bounds first).1 b (bounds second).1 c (bounds third).1
      a' (bounds first).2 b' (bounds second).2 c' (bounds third).2
      ⟨product, first, second, third⟩
  · intro code
    exact ⟨code.injection, code.one, fun a _ b _ c _ a' _ b' _ c' _ h =>
      code.mul a b c a' b' c' h.1 h.2.1 h.2.2.1 h.2.2.2⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_doubleUnionMemberFormula {n} (x f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (doubleUnionMemberFormula x f) env ↔ env x ∈ ⋃₀ ⋃₀ env f := by
  simp only [doubleUnionMemberFormula, truth_exMem, Truth]
  change (∃ a ∈ env f, ∃ b ∈ a, env x ∈ b) ↔ _
  constructor
  · rintro ⟨a, ha, b, hb, hx⟩
    exact ZFSet.mem_sUnion.2 ⟨b, ZFSet.mem_sUnion.2 ⟨a, ha, hb⟩, hx⟩
  · intro hx
    obtain ⟨b, hb, hx⟩ := ZFSet.mem_sUnion.1 hx
    obtain ⟨a, ha, hb⟩ := ZFSet.mem_sUnion.1 hb
    exact ⟨a, ha, b, hb, hx⟩

theorem truth_doubleUnionEquationFormula {n} (B f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (doubleUnionEquationFormula B f) env ↔ env B = ⋃₀ ⋃₀ env f := by
  simp only [doubleUnionEquationFormula, Truth, truth_doubleUnionMemberFormula]
  change ((∀ x ∈ env B, x ∈ ⋃₀ ⋃₀ env f) ∧
    ∀ a ∈ env f, ∀ b ∈ a, ∀ x ∈ b, x ∈ env B) ↔ _
  constructor
  · rintro ⟨subset, cover⟩
    apply ZFSet.ext
    intro x
    refine ⟨subset x, ?_⟩
    intro hx
    obtain ⟨b, hb, hx⟩ := ZFSet.mem_sUnion.1 hx
    obtain ⟨a, ha, hb⟩ := ZFSet.mem_sUnion.1 hb
    exact cover a ha b hb x hx
  · intro equal
    rw [equal]
    exact ⟨fun _ hx => hx, fun a ha b hb x hx =>
      ZFSet.mem_sUnion.2 ⟨b, ZFSet.mem_sUnion.2 ⟨a, ha, hb⟩, hx⟩⟩

theorem truth_copyEmbeddingFamilyFormula {n}
    (Qs rs μs L r μ t I Indices Maps W QB RB MB : Fin n) (env : Fin n → ZFSet.{u})
    (maps : ZFSet.IsFunc (env I) (env W) (env Maps))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) (eqR : env RB = ⋃₀ ⋃₀ env rs)
    (eqM : env MB = ⋃₀ ⋃₀ env μs) :
    Truth (copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB) env ↔
      CopyEmbeddingFamilyCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env t) (env I) (env Indices) (env Maps) := by
  simp only [copyEmbeddingFamilyFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_meetEmbeddingFormula]
  constructor
  · intro property i hi s hs e P R V index map qField rField mField
    have hP : P ∈ env QB := eqQ.symm ▸ pair_second_mem_doubleUnion qField
    have hR : R ∈ env RB := eqR.symm ▸ pair_second_mem_doubleUnion rField
    have hV : V ∈ env MB := eqM.symm ▸ pair_second_mem_doubleUnion mField
    exact property i hi s hs e (ZFSet.pair_mem_prod.1 (maps.1 map)).2
      P hP R hR V hV ⟨index, map, qField, rField, mField⟩
  · intro code i hi s hs e _ P _ R _ V _ condition
    exact code i hi s hs e P R V condition.1 condition.2.1 condition.2.2.1
      condition.2.2.2.1 condition.2.2.2.2

theorem truth_copyImageCoverFormula {n} (Qs L t I parts Indices Maps W QB : Fin n)
    (env : Fin n → ZFSet.{u}) (maps : ZFSet.IsFunc (env I) (env W) (env Maps))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) :
    Truth (copyImageCoverFormula Qs L t I parts Indices Maps W QB) env ↔
      CopyImageCoverCode (env Qs) (env L) (env t) (env I) (env parts) (env Indices) (env Maps) := by
  simp only [copyImageCoverFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_imageMemberFormula]
  constructor
  · intro property i hi s hs e P x hx index map qField part
    have hP : P ∈ env QB := eqQ.symm ▸ pair_second_mem_doubleUnion qField
    exact (mem_relationImage P (env L) e x).2 ⟨hx,
      property i hi s hs e (ZFSet.pair_mem_prod.1 (maps.1 map)).2
        P hP x hx ⟨index, map, qField, part⟩⟩
  · intro code i hi s hs e _ P _ x hx condition
    exact ((mem_relationImage P (env L) e x).1
      (code i hi s hs e P x hx condition.1 condition.2.1 condition.2.2.1 condition.2.2.2)).2

end BoundedFormula





namespace BoundedFormula

theorem truth_copyLayerFormula {n}
    (Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (copyLayerFormula Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB) env ↔
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth) (env t)
        (env I) (env parts) (env Indices) (env Maps) (env W) (env N) (env injection) := by
  simp only [copyLayerFormula, Truth, truth_doubleUnionEquationFormula, truth_injectionFormula,
    truth_functionFormula, truth_imp, truth_pairMembershipFormula, truth_exMem]
  constructor
  · rintro ⟨eqQ, eqR, eqM, small, indices, maps, embedding, cover, inCopy⟩
    exact ⟨eqQ, eqR, eqM, small, indices, maps,
      (truth_copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB
        env maps eqQ eqR eqM).1 embedding,
      cover, (truth_copyImageCoverFormula Qs L t I parts Indices Maps W QB env maps eqQ).1 inCopy⟩
  · rintro ⟨eqQ, eqR, eqM, code⟩
    exact ⟨eqQ, eqR, eqM, code.small, code.indices, code.maps,
      (truth_copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB
        env code.maps eqQ eqR eqM).2 code.embedding,
      code.cover, (truth_copyImageCoverFormula Qs L t I parts Indices Maps W QB env code.maps eqQ).2
        code.inCopy⟩

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_componentImageCoverFormula {n}
    (Qs L t I Components Indices Maps W QB : Fin n) (env : Fin n → ZFSet.{u})
    (maps : ZFSet.IsFunc (env I) (env W) (env Maps)) (eqQ : env QB = ⋃₀ ⋃₀ env Qs) :
    Truth (componentImageCoverFormula Qs L t I Components Indices Maps W QB) env ↔
      ComponentImageCoverCode (env Qs) (env L) (env t) (env I)
        (env Components) (env Indices) (env Maps) := by
  simp only [componentImageCoverFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_imageMemberFormula]
  constructor
  · intro property i hi s hs e P x hx index map qField part
    have hP : P ∈ env QB := eqQ.symm ▸ pair_second_mem_doubleUnion qField
    exact (mem_relationImage P (env L) e x).2 ⟨hx,
      property i hi s hs e (ZFSet.pair_mem_prod.1 (maps.1 map)).2
        P hP x hx ⟨index, map, qField, part⟩⟩
  · intro code i hi s hs e _ P _ x hx condition
    exact ((mem_relationImage P (env L) e x).1
      (code i hi s hs e P x hx condition.1 condition.2.1 condition.2.2.1 condition.2.2.2)).2

theorem truth_componentSeparationFormula {n} (L r μ birth t F I Components : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Truth (componentSeparationFormula L r μ birth t F I Components) env ↔
      ComponentSeparationCode (env L) (env r) (env μ) (env birth)
        (env t) (env F) (env I) (env Components) := by
  simp only [componentSeparationFormula, Truth, truth_imp, truth_pairMembershipFormula]
  constructor
  · intro property x hx y hy i hi j hj first second different
    exact (truth_oldBridgeFormula L.succ.succ.succ.succ r.succ.succ.succ.succ
      μ.succ.succ.succ.succ birth.succ.succ.succ.succ t.succ.succ.succ.succ 3 2
      (extend j (extend i (extend y (extend x env)))) meet).1
      (property x hx y hy i hi j hj ⟨first, second, different⟩)
  · intro code x hx y hy i hi j hj condition
    exact (truth_oldBridgeFormula L.succ.succ.succ.succ r.succ.succ.succ.succ
      μ.succ.succ.succ.succ birth.succ.succ.succ.succ t.succ.succ.succ.succ 3 2
      (extend j (extend i (extend y (extend x env)))) meet).2
      (code x hx y hy i hi j hj condition.1 condition.2.1 condition.2.2)

theorem truth_separatedLayerFormula {n}
    (Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u})
    (meet : MeetOrderCode (env L) (env r) (env μ))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) (eqR : env RB = ⋃₀ ⋃₀ env rs)
    (eqM : env MB = ⋃₀ ⋃₀ env μs) :
    Truth (separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB) env ↔
      SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env birth) (env t) (env I) (env Indices) (env Maps) (env W) (env Components) (env F) := by
  simp only [separatedLayerFormula, Truth, truth_functionFormula, truth_layerBirthFiberFormula]
  constructor
  · rintro ⟨indices, maps, fiber, components, embeddings, cover, separated⟩
    exact ⟨indices, maps, fiber, components,
      (truth_copyEmbeddingFamilyFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ env maps eqQ eqR eqM).1 embeddings,
      (truth_componentImageCoverFormula _ _ _ _ _ _ _ _ _ env maps eqQ).1 cover,
      (truth_componentSeparationFormula _ _ _ _ _ _ _ _ env meet).1 separated⟩
  · intro code
    exact ⟨code.indices, code.maps, code.fiber, code.components,
      (truth_copyEmbeddingFamilyFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ env code.maps eqQ eqR eqM).2 code.embedding,
      (truth_componentImageCoverFormula _ _ _ _ _ _ _ _ _ env code.maps eqQ).2 code.cover,
      (truth_componentSeparationFormula _ _ _ _ _ _ _ _ env meet).2 code.separated⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem copyLayerWitness_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {I parts Indices Maps W injection : ZFSet.{u}}
    (hI : I ∈ M.sets) (hParts : parts ∈ M.sets) (hIndices : Indices ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hW : W ∈ M.sets) (hInjection : injection ∈ M.sets) :
    copyLayerWitness I parts Indices Maps W injection ∈ M.sets := by
  have zero := M.empty_mem ⟨I, hI⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  exact M.nonemptyTupleCode_mem pairing 6 _
    (Fin.cases one (Fin.cases hI (Fin.cases hParts (Fin.cases hIndices
      (Fin.cases hMaps (Fin.cases hW (fun _ => hInjection)))))))

theorem separatedLayerWitness_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {I Indices Maps W Components F : ZFSet.{u}}
    (hI : I ∈ M.sets) (hIndices : Indices ∈ M.sets) (hMaps : Maps ∈ M.sets)
    (hW : W ∈ M.sets) (hComponents : Components ∈ M.sets) (hF : F ∈ M.sets) :
    separatedLayerWitness I Indices Maps W Components F ∈ M.sets := by
  have zero := M.empty_mem ⟨I, hI⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  have two : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions one one
  exact M.nonemptyTupleCode_mem pairing 6 _
    (Fin.cases two (Fin.cases hI (Fin.cases hIndices (Fin.cases hMaps
      (Fin.cases hW (Fin.cases hComponents (fun _ => hF)))))))
end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_growthTagFormula (k : Nat) {n} (z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (growthTagFormula k z) env ↔ env z = natSetCode k := by
  induction k generalizing n with
  | zero => exact truth_emptyFormula z env
  | succ k ih =>
    simp only [growthTagFormula, truth_exMem, Truth, truth_successorFormula, ih]
    change (∃ x ∈ env z, env z = insert x x ∧ x = natSetCode k) ↔ _
    constructor
    · rintro ⟨x, _, equal, rfl⟩
      exact equal
    · intro equal
      exact ⟨natSetCode k, equal.symm ▸ (show natSetCode k ∈ natSetCode (k + 1) from by
        rw [natSetCode_succ]; exact ZFSet.mem_insert _ _), equal, rfl⟩

theorem truth_countableTaggedLayerFormula {n} (z tag D injection L birth t N : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (countableTaggedLayerFormula z tag D injection L birth t N) env ↔
      env tag = natSetCode 0 ∧ env z = countableLayerWitness (env D) (env injection) ∧
        CountableLayerCode (env L) (env birth) (env t) (env D) (env N) (env injection) := by
  simp only [countableTaggedLayerFormula, Truth, truth_growthTagFormula,
    truth_nonemptyTupleFormula, truth_countableLayerFormula]
  constructor
  · rintro ⟨tagged, tuple, code⟩
    refine ⟨tagged, ?_, code⟩
    simpa only [countableLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
  · rintro ⟨tagged, tuple, code⟩
    refine ⟨tagged, ?_, code⟩
    simpa only [countableLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple

theorem truth_copyTaggedLayerFormula {n}
    (z tag I parts Indices Maps W injection Qs rs μs L r μ birth t N QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (copyTaggedLayerFormula z tag I parts Indices Maps W injection Qs rs μs L r μ birth t N QB RB MB) env ↔
      env tag = natSetCode 1 ∧ env z = copyLayerWitness (env I) (env parts) (env Indices)
        (env Maps) (env W) (env injection) ∧
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
        (env t) (env I) (env parts) (env Indices) (env Maps) (env W) (env N) (env injection) := by
  simp only [copyTaggedLayerFormula, Truth, truth_growthTagFormula,
    truth_nonemptyTupleFormula, truth_copyLayerFormula]
  constructor
  · rintro ⟨tagged, tuple, rest⟩
    refine ⟨tagged, ?_, rest⟩
    simpa only [copyLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
  · rintro ⟨tagged, tuple, rest⟩
    refine ⟨tagged, ?_, rest⟩
    simpa only [copyLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple

theorem truth_separatedTaggedLayerFormula {n}
    (z tag I Indices Maps W Components F Qs rs μs L r μ birth t QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Truth (separatedTaggedLayerFormula z tag I Indices Maps W Components F Qs rs μs L r μ birth t QB RB MB) env ↔
      env tag = natSetCode 2 ∧ env z = separatedLayerWitness (env I) (env Indices)
        (env Maps) (env W) (env Components) (env F) ∧
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
        (env t) (env I) (env Indices) (env Maps) (env W) (env Components) (env F) := by
  simp only [separatedTaggedLayerFormula, Truth, truth_growthTagFormula,
    truth_nonemptyTupleFormula, truth_doubleUnionEquationFormula]
  constructor
  · rintro ⟨tagged, tuple, eqQ, eqR, eqM, recognized⟩
    refine ⟨tagged, ?_, eqQ, eqR, eqM, ?_⟩
    · simpa only [separatedLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
    · exact (truth_separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB
        env meet eqQ eqR eqM).1 recognized
  · rintro ⟨tagged, tuple, eqQ, eqR, eqM, code⟩
    refine ⟨tagged, ?_, eqQ, eqR, eqM, ?_⟩
    · simpa only [separatedLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
    · exact (truth_separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB
        env meet eqQ eqR eqM).2 code

end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_LiteralQuotientRankBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem rank_natSetCode_lt (n : Nat) : ZFSet.rank (natSetCode n) < o := by
  induction n with
  | zero => simpa only [natSetCode_zero, ZFSet.rank_empty] using limit.pos
  | succ n ih =>
    rw [natSetCode_succ, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt ih) ih

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TaggedGrowthLayerRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem countableLayerWitness_rank_lt {D injection : ZFSet.{u}}
    (hD : ZFSet.rank D < o) (hInjection : ZFSet.rank injection < o) :
    ZFSet.rank (countableLayerWitness D injection) < o :=
  rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases (rank_natSetCode_lt limit 0) (Fin.cases hD (fun _ => hInjection)))

theorem copyLayerWitness_rank_lt {I parts Indices Maps W injection : ZFSet.{u}}
    (hI : ZFSet.rank I < o) (hParts : ZFSet.rank parts < o)
    (hIndices : ZFSet.rank Indices < o) (hMaps : ZFSet.rank Maps < o)
    (hW : ZFSet.rank W < o) (hInjection : ZFSet.rank injection < o) :
    ZFSet.rank (copyLayerWitness I parts Indices Maps W injection) < o :=
  rank_nonemptyTupleCode_lt limit 6 _ (Fin.cases (rank_natSetCode_lt limit 1)
    (Fin.cases hI (Fin.cases hParts (Fin.cases hIndices
      (Fin.cases hMaps (Fin.cases hW (fun _ => hInjection)))))))

theorem separatedLayerWitness_rank_lt {I Indices Maps W Components F : ZFSet.{u}}
    (hI : ZFSet.rank I < o) (hIndices : ZFSet.rank Indices < o)
    (hMaps : ZFSet.rank Maps < o) (hW : ZFSet.rank W < o)
    (hComponents : ZFSet.rank Components < o) (hF : ZFSet.rank F < o) :
    ZFSet.rank (separatedLayerWitness I Indices Maps W Components F) < o :=
  rank_nonemptyTupleCode_lt limit 6 _ (Fin.cases (rank_natSetCode_lt limit 2)
    (Fin.cases hI (Fin.cases hIndices (Fin.cases hMaps
      (Fin.cases hW (Fin.cases hComponents (fun _ => hF)))))))

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_StrictLexHeightFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_strictLexHeightFormula {n} (P C D r height rD : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (strictLexHeightFormula P C D r height rD) env ↔
      StrictLexHeightCode (env P) (env C) (env D) (env r) (env height) (env rD) := by
  simp only [strictLexHeightFormula, Truth, truth_functionToProductFormula, truth_imp,
    truth_disj, truth_pairMembershipFormula, truth_rightTripleMembershipFormula]
  constructor
  · rintro ⟨function, strict⟩
    refine ⟨function, ?_⟩
    intro x hx y hy c q d v lower different first second
    have firstBounds := ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 first)).2
    have secondBounds := ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 second)).2
    exact strict x hx y hy c firstBounds.1 q firstBounds.2 d secondBounds.1 v secondBounds.2
      ⟨lower, different, first, second⟩
  · intro code
    refine ⟨code.function, ?_⟩
    intro x hx y hy c _ q _ d _ v _ condition
    exact code.strict x hx y hy c q d v condition.1 condition.2.1
      condition.2.2.1 condition.2.2.2

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem internal_chronological_coinitiality
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (ordinal : ordinalSetProperty T)
    (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets,
      InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
        ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ r := by
  have descent := essentialHeightDescent_of_chronological_laws meet filter born oldMeet strictHeight
  have small := M.essentialBirthIndices_countable pairing unions powers separation infinite choice
    hF hT hr hBirth hC hQ hHeight filter.subset ordinal strictHeight.function smallQ irreflexive descent
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    M.internal_countable_basis_of_birth_layers pairing unions powers separation infinite choice
      hF hT hr hBirth meet.order filter.subset born small localBases
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_chronologyPointFormula {n} (T C D rD s L r μ birth height : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyPointFormula T C D rD s L r μ birth height) env ↔
      ChronologyPointCode (env T) (env C) (env D) (env rD) (env s)
        (env L) (env r) (env μ) (env birth) (env height) := by
  simp only [chronologyPointFormula, Truth, truth_meetOrderFormula,
    truth_functionFormula, truth_strictLexHeightFormula]
  constructor
  · rintro ⟨meet, function, bound, old, strict⟩
    exact ⟨meet, function, (truth_birthBoundFormula L T birth s env function).1 bound,
      (truth_oldMeetFormula L T r μ birth env function).1 old, strict⟩
  · intro code
    exact ⟨code.meet, code.birth_function,
      (truth_birthBoundFormula L T birth s env code.birth_function).2 code.birth_bound,
      (truth_oldMeetFormula L T r μ birth env code.birth_function).2 code.old_meet,
      code.strict_height⟩

end BoundedFormula





namespace GroundChronologicalHistory

variable {M : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

theorem all_filters_internal_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt) :
    ∀ cutoff ∈ T, ∀ F ∈ M.sets,
      MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F →
        M.InternalCountableBelow (history.order cutoff) F F := by
  intro cutoff
  induction cutoff using ZFSet.inductionOn with
  | h cutoff ih =>
    intro hc F hF filter
    have localBases : ∀ t ∈ essentialBirthIndices F T (history.order cutoff) (history.birth cutoff),
        M.InternalCountableBelow (history.order cutoff) F
          (essentialBirthFiber F T (history.order cutoff) (history.birth cutoff) t) := by
      intro t ht
      obtain ⟨htT, x, hx, xt⟩ :=
        (mem_essentialBirthIndices F T (history.order cutoff) (history.birth cutoff) t).1 ht
      have bounded := history.birth_bound cutoff hc x
        (filter.subset (birthEssentialSet_subset F T (history.order cutoff) (history.birth cutoff) hx)) t xt
      apply (history.layer cutoff hc t htT bounded).internal_countable_essentials
        pairing unions powers separation infinite choice (history.space_mem cutoff hc)
        (history.order_mem cutoff hc) (history.birth_mem cutoff hc) hF hT (M.transitive hT htT)
        (history.meet_order cutoff hc) filter (history.birth_function cutoff hc)
      intro s hs
      have hsT : s ∈ T := ordinal.1 t htT s hs
      have before : s ∈ cutoff := bounded.elim
        (fun equal => equal ▸ hs) (fun earlier => ordinal.2 cutoff hc t earlier s hs)
      exact ⟨history.space_mem s hsT, history.meet_order s hsT, ih s before hsT⟩
    obtain ⟨B, hB, f, hf, injection, positive, below⟩ :=
      M.internal_chronological_coinitiality pairing unions powers separation infinite choice
        hF hT (history.order_mem cutoff hc) (history.birth_mem cutoff hc)
        hC hQ (history.height_mem cutoff hc) (history.meet_order cutoff hc) filter
        (history.birth_function cutoff hc) ordinal (history.old_meet cutoff hc)
        (history.strict_height cutoff hc) smallQ irreflexive localBases
    exact ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩

theorem exists_internal_basis
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ M.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff := by
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    history.all_filters_internal_countable pairing unions powers separation infinite choice
      hT hC hQ ordinal smallQ irreflexive cutoff hc F hF filter
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end GroundChronologicalHistory





namespace BoundedFormula

theorem truth_chronologyFunctionsFormula {n} (T V : Fin n) (graphs : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyFunctionsFormula T V graphs) env ↔
      ∀ j, ZFSet.IsFunc (env T) (env V) (env (graphs j)) := by
  simp only [chronologyFunctionsFormula, Truth, truth_functionFormula]
  exact ⟨fun ⟨a, b, c, d, e⟩ => Fin.cases a (Fin.cases b (Fin.cases c
      (Fin.cases d (Fin.cases e (fun i => Fin.elim0 i))))),
    fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩⟩

theorem truth_chronologyCoreFormula {n} (T V C D rD : Fin n) (graphs : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyCoreFormula T V C D rD graphs) env ↔
      ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j)) := by
  simp only [chronologyCoreFormula, Truth, truth_chronologyFunctionsFormula,
    chronologyPointsFormula, truth_imp, truth_pairMembershipFormula, truth_chronologyPointFormula]
  constructor
  · rintro ⟨function, point⟩
    refine ⟨function, ?_⟩
    intro s hs L r μ birth height eL er eμ eb eh
    exact point s hs L (ZFSet.pair_mem_prod.1 ((function 0).1 eL)).2
      r (ZFSet.pair_mem_prod.1 ((function 1).1 er)).2
      μ (ZFSet.pair_mem_prod.1 ((function 2).1 eμ)).2
      birth (ZFSet.pair_mem_prod.1 ((function 3).1 eb)).2
      height (ZFSet.pair_mem_prod.1 ((function 4).1 eh)).2 ⟨eL, er, eμ, eb, eh⟩
  · intro code
    exact ⟨code.function, fun s hs L _ r _ μ _ birth _ height _ ⟨eL, er, eμ, eb, eh⟩ =>
      code.point s hs L r μ birth height eL er eμ eb eh⟩

theorem realize_chronologyCoreFormula (M : TransitiveGround.{u}) {n}
    (T V C D rD : Fin n) (graphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyCoreFormula T V C D rD graphs).toFormula env ↔
      ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j)) :=
  (realize_toFormula M _ env members).trans (truth_chronologyCoreFormula T V C D rD graphs env)

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologicalHistory

open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

theorem exists_extension_basis
    (includes : M.sets ⊆ N.sets)
    (pairing : Realize N.sets SetFormula.pairing Fin.elim0)
    (unions : Realize N.sets SetFormula.union Fin.elim0)
    (powers : Realize N.sets powerSet Fin.elim0) (separation : SeparationSchema N.sets)
    (infinite : Realize N.sets SetFormula.infinity Fin.elim0)
    (choice : Realize N.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ N.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff :=
  (history.of_inclusion includes).exists_internal_basis pairing unions powers separation infinite
    choice (includes hT) (includes hC) (includes hQ) ordinal
    (M.groundEmbeddable_of_inclusion N includes smallQ) irreflexive hc hF filter

end PartitionPilot.Forcing.GroundChronologicalHistory



namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)

variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem attainedBound_rank_lt (graphs : ∀ j, ZFSet.rank (fields.graph j) < o) :
    ZFSet.rank fields.attainedBound < o :=
  (ZFSet.rank_sUnion_le _).trans_lt (rank_finiteRange_lt limit 5 _
    (fun j => (functionGraphRange_rank_le T (fields.graph j)).trans_lt (graphs j)))

theorem normalizeBound_code_rank_lt (time : ZFSet.rank T < o)
    (graphs : ∀ j, ZFSet.rank (fields.graph j) < o) :
    ZFSet.rank (fields.normalizeBound pairing unions separation).code < o :=
  rank_nonemptyTupleCode_lt limit 6 _
    (Fin.cases time (Fin.cases (fields.attainedBound_rank_lt limit graphs) graphs))

end PartitionPilot.Forcing.GroundChronologyFields



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSerializedCodeRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

theorem time_rank_le_code : ZFSet.rank T ≤ ZFSet.rank fields.code :=
  rank_nonemptyTupleCode_field_le 6 fields.codeFields 0

theorem graph_rank_le_code (j : Fin 5) : ZFSet.rank (fields.graph j) ≤ ZFSet.rank fields.code :=
  rank_nonemptyTupleCode_field_le 6 fields.codeFields j.succ.succ

end GroundChronologyFields

namespace GroundSerializedChronology
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)

theorem fieldsCode_rank_le_code : ZFSet.rank serial.fields.code ≤ ZFSet.rank serial.code :=
  rank_nonemptyTupleCode_field_le 2 serial.codeFields 0

theorem time_rank_le_code : ZFSet.rank T ≤ ZFSet.rank serial.code :=
  serial.fields.time_rank_le_code.trans serial.fieldsCode_rank_le_code

theorem fieldGraph_rank_le_code (j : Fin 5) :
    ZFSet.rank (serial.fields.graph j) ≤ ZFSet.rank serial.code :=
  (serial.fields.graph_rank_le_code j).trans serial.fieldsCode_rank_le_code

theorem layers_rank_le_code : ZFSet.rank serial.layers ≤ ZFSet.rank serial.code :=
  rank_nonemptyTupleCode_field_le 2 serial.codeFields 2

theorem layerWitness_rank_lt_code {s t : ZFSet.{u}} (hs : s ∈ T) (ht : t ∈ T)
    (earlier : t = s ∨ t ∈ s) :
    ZFSet.rank (serial.layerWitness s t) < ZFSet.rank serial.code :=
  (ZFSet.rank_lt_of_mem (pair_second_mem_doubleUnion (serial.layerWitness_entry hs ht earlier))).trans_le
    (((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans serial.layers_rank_le_code)

end GroundSerializedChronology
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IndexedMixedOperationLiftCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem indexedMixedBinaryLift_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (T UG UP A JG JP : ZFSet.{u}) {G P : ZFSet.{u}}
    (actors : ZFSet.rank G < o) (points : ZFSet.rank P < o) :
    ZFSet.rank (indexedMixedBinaryLift T UG UP G P A JG JP) < o :=
  (ZFSet.rank_mono (indexedMixedBinaryLift_subset T UG UP G P A JG JP)).trans_lt
    (rank_product_lt limit (rank_product_lt limit actors points) points)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IndexedOperationLiftCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
open scoped ZFSet
universe u

theorem indexedRelationLift_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (T U R J : ZFSet.{u}) {Q : ZFSet.{u}} (rank : ZFSet.rank Q < o) :
    ZFSet.rank (indexedRelationLift T U Q R J) < o :=
  (ZFSet.rank_mono (indexedRelationLift_subset T U Q R J)).trans_lt
    (rank_product_lt limit rank rank)

theorem indexedBinaryLift_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (T U B J : ZFSet.{u}) {Q : ZFSet.{u}} (rank : ZFSet.rank Q < o) :
    ZFSet.rank (indexedBinaryLift T U Q B J) < o :=
  (ZFSet.rank_mono (indexedBinaryLift_subset T U Q B J)).trans_lt
    (rank_product_lt limit (rank_product_lt limit rank rank) rank)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_NonzeroLimitOrdinalCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem not_nonzeroLimitOrdinalCode_successor (b : ZFSet.{u}) :
    ¬ NonzeroLimitOrdinalCode (insert b b) := by
  intro limit
  obtain ⟨c, member, later⟩ := limit.2 b (ZFSet.mem_insert b b)
  rcases ZFSet.mem_insert_iff.1 member with equal | earlier
  · subst c
    exact (lt_irrefl (ZFSet.rank b)) (ZFSet.rank_lt_of_mem later)
  · exact (lt_irrefl (ZFSet.rank b))
      ((ZFSet.rank_lt_of_mem later).trans (ZFSet.rank_lt_of_mem earlier))

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundHeightPushforward
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
theorem pushedHeightGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B H e h : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hH : H ∈ M.sets)
    (he : e ∈ M.sets) (hh : h ∈ M.sets) : pushedHeightGraph A B H e h ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation
    (M.relationImage_mem separation hA hB he) hA hH
    (M.relationConverse_mem pairing unions powers separation hA hB he) hh
end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.PosetActionCode
universe u
variable {G P m one r A g v : ZFSet.{u}}

theorem agreement_identity_iff_fixes (action : PosetActionCode G P m one r A) :
    ActionAgreementBelow P r A g one v ↔
      ∀ x ∈ P, ZFSet.pair x v ∈ r → ZFSet.pair (ZFSet.pair g x) x ∈ A := by
  constructor
  · intro agree x hx lower
    exact (agree x hx x hx lower).2 (action.one x hx)
  · intro fixes x hx y _ lower
    have fixed := fixes x hx lower
    have identity := action.one x hx
    have function : FunctionGraphOn (ZFSet.prod G P) A := ⟨P, action.function⟩
    exact ⟨fun entry => (function.unique entry fixed).symm ▸ identity,
      fun entry => (function.unique entry identity).symm ▸ fixed⟩

end PartitionPilot.Forcing.PosetActionCode



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RectangleFulfillmentAtBound
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

theorem truth_actionAgreementBelowFormula {n} (P r A g h w : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionAgreementBelowFormula P r A g h w) env ↔
      ActionAgreementBelow (env P) (env r) (env A) (env g) (env h) (env w) := by
  simp only [actionAgreementBelowFormula, ActionAgreementBelow, Truth, truth_imp, iff_def,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor <;> exact fun h => h

theorem truth_externalRectangleFormula {n} (P G r μ A c b d g h : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalRectangleFormula P G r μ A c b d g h) env ↔
      ExternalRectangleCode (env P) (env G) (env r) (env μ) (env A)
        (env c) (env b) (env d) (env g) (env h) := by
  simp only [externalRectangleFormula, ExternalRectangleCode, rectangleSeparatedFormula,
    Truth, truth_exMem, truth_imp, truth_actionAgreementBelowFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula





namespace BoundedFormula

theorem truth_compressionActorFormula {n}
    (P G Q H R B e a Sources Reps top Caps i k : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (compressionActorFormula P G Q H R B e a Sources Reps top Caps i k) env ↔
      CompressionActorCode (env P) (env G) (env Q) (env H) (env R) (env B)
        (env e) (env a) (env Sources) (env Reps) (env top) (env Caps) (env i) (env k) := by
  simp only [compressionActorFormula, CompressionActorCode, Truth, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula,
    truth_actionAgreementBelowFormula, iff_def]
  constructor <;> exact fun h => h

theorem truth_compressionActorFulfillmentFormula {n}
    (I P G Q H R B e a Sources Reps top Caps : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (compressionActorFulfillmentFormula I P G Q H R B e a Sources Reps top Caps) env ↔
      CompressionActorFulfillmentCode (env I) (env P) (env G) (env Q) (env H) (env R)
        (env B) (env e) (env a) (env Sources) (env Reps) (env top) (env Caps) := by
  simp only [compressionActorFulfillmentFormula, Truth, truth_exMem, truth_compressionActorFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula

theorem truth_rectangleIdealFormula {n} (Q H R B e a c b g h k l : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleIdealFormula Q H R B e a c b g h k l) env ↔ RectangleIdealCode (env Q) (env H) (env R) (env B) (env e) (env a) (env c) (env b) (env g) (env h) (env k) (env l) := by
  simp only [rectangleIdealFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_actionAgreementBelowFormula]
  rfl

theorem truth_rectangleRootMeetFormula {n} (P μ A Q ν B e c d g k : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleRootMeetFormula P μ A Q ν B e c d g k) env ↔ RectangleRootMeetCode (env P) (env μ) (env A) (env Q) (env ν) (env B) (env e) (env c) (env d) (env g) (env k) := by
  simp only [rectangleRootMeetFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

theorem truth_rectangleCrossMeetFormula {n} (Q ν B e b d k l : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleCrossMeetFormula Q ν B e b d k l) env ↔ RectangleCrossMeetCode (env Q) (env ν) (env B) (env e) (env b) (env d) (env k) (env l) := by
  simp only [rectangleCrossMeetFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

theorem truth_rectangleActorPairFormula {n} (P μ A Q H R ν B e a c b d g h k l : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleActorPairFormula P μ A Q H R ν B e a c b d g h k l) env ↔ RectangleActorPairCode (env P) (env μ) (env A) (env Q) (env H) (env R) (env ν) (env B) (env e) (env a) (env c) (env b) (env d) (env g) (env h) (env k) (env l) := by
  simp only [rectangleActorPairFormula, Truth, truth_rectangleIdealFormula,
    truth_rectangleRootMeetFormula, truth_rectangleCrossMeetFormula]
  rfl

theorem truth_rectangleFulfillmentFormula {n} (P G r μ A Q H R ν B e a : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleFulfillmentFormula P G r μ A Q H R ν B e a) env ↔ RectangleFulfillmentCode (env P) (env G) (env r) (env μ) (env A) (env Q) (env H) (env R) (env ν) (env B) (env e) (env a) := by
  simp only [rectangleFulfillmentFormula, Truth, truth_imp, truth_exMem,
    truth_externalRectangleFormula, truth_rectangleActorPairFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

theorem MeetOrderCode.meet_entry_of_lower {P r μ x y : ZFSet.{u}}
    (meet : MeetOrderCode P r μ) (hx : x ∈ P) (hy : y ∈ P)
    (lower : ZFSet.pair x y ∈ r) : ZFSet.pair (ZFSet.pair x y) x ∈ μ := by
  obtain ⟨z, entry, _⟩ := meet.operation.2 (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2
  have equal : z = x := meet.order.antisymm z hz x hx (meet.lower_left x y z entry)
    (meet.greatest x y z x hx entry (meet.order.refl x hx) lower)
  exact equal ▸ entry

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundMainTransition
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}
variable (transition : GroundMainTransition source target)

theorem rectangle_at_bound
    (fulfills : RectangleFulfillmentCode source.carrier source.actors source.order
      source.meetGraph source.action target.carrier target.actors target.order target.meetGraph
      target.action transition.points transition.actors)
    {c b d g h X c' b' d' g' h' X' : ZFSet.{u}}
    (rectangle : ExternalRectangleCode source.carrier source.actors source.order
      source.meetGraph source.action c b d g h) (hX : X ∈ source.carrier)
    (firstUpper : ∀ y ∈ source.carrier, ZFSet.pair (ZFSet.pair g d) y ∈ source.action →
      ZFSet.pair y X ∈ source.order)
    (secondUpper : ∀ y ∈ source.carrier, ZFSet.pair (ZFSet.pair h d) y ∈ source.action →
      ZFSet.pair y X ∈ source.order)
    (imageC : ZFSet.pair c c' ∈ transition.points)
    (imageB : ZFSet.pair b b' ∈ transition.points)
    (imageD : ZFSet.pair d d' ∈ transition.points)
    (imageX : ZFSet.pair X X' ∈ transition.points)
    (imageG : ZFSet.pair g g' ∈ transition.actors)
    (imageH : ZFSet.pair h h' ∈ transition.actors) :
    ∃ k ∈ target.actors, ∃ l ∈ target.actors,
      RectangleAtBoundCode target.carrier target.order target.meetGraph target.action
        c' b' d' g' h' X' k l := by
  have rectangleData := rectangle
  obtain ⟨hc, hb, hd, hg, hh, cd, _, _⟩ := rectangleData
  obtain ⟨k, hk, l, hl, ideals, rootG, rootH, cross⟩ := fulfills c hc b hb d hd g hg h hh rectangle
  have hc' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageC)).2
  have hb' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageB)).2
  have hd' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageD)).2
  have hX' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageX)).2
  have hg' := (ZFSet.pair_mem_prod.1 (transition.group_embedding.injection.function.1 imageG)).2
  have hh' := (ZFSet.pair_mem_prod.1 (transition.group_embedding.injection.function.1 imageH)).2
  obtain ⟨v, gv, _⟩ := source.action_code.function.2 (ZFSet.pair g c) (ZFSet.pair_mem_prod.2 ⟨hg, hc⟩)
  obtain ⟨w, hwAction, _⟩ := source.action_code.function.2 (ZFSet.pair h c) (ZFSet.pair_mem_prod.2 ⟨hh, hc⟩)
  obtain ⟨gd, gD, _⟩ := source.action_code.function.2 (ZFSet.pair g d) (ZFSet.pair_mem_prod.2 ⟨hg, hd⟩)
  obtain ⟨hdv, hD, _⟩ := source.action_code.function.2 (ZFSet.pair h d) (ZFSet.pair_mem_prod.2 ⟨hh, hd⟩)
  have hv := (ZFSet.pair_mem_prod.1 (source.action_code.function.1 gv)).2
  have hw := (ZFSet.pair_mem_prod.1 (source.action_code.function.1 hwAction)).2
  have hgd := (ZFSet.pair_mem_prod.1 (source.action_code.function.1 gD)).2
  have hhd := (ZFSet.pair_mem_prod.1 (source.action_code.function.1 hD)).2
  have vX := source.meet.order.trans v hv gd hgd X hX
    (source.action_code.monotone g hg c hc d hd v hv gd hgd gv gD cd) (firstUpper gd hgd gD)
  have wX := source.meet.order.trans w hw hdv hhd X hX
    (source.action_code.monotone h hh c hc d hd w hw hdv hhd hwAction hD cd) (secondUpper hdv hhd hD)
  have meetV := source.meet.meet_entry_of_lower hv hX vX
  have meetW := source.meet.meet_entry_of_lower hw hX wX
  obtain ⟨v', vv', _⟩ := transition.point_embedding.injection.function.2 v hv
  obtain ⟨w', ww', _⟩ := transition.point_embedding.injection.function.2 w hw
  have hv' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 vv')).2
  have hw' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 ww')).2
  obtain ⟨y, ky, _⟩ := target.action_code.function.2 (ZFSet.pair k d') (ZFSet.pair_mem_prod.2 ⟨hk, hd'⟩)
  obtain ⟨z, lz, _⟩ := target.action_code.function.2 (ZFSet.pair l d') (ZFSet.pair_mem_prod.2 ⟨hl, hd'⟩)
  obtain ⟨t, kt, _⟩ := target.action_code.function.2 (ZFSet.pair k b') (ZFSet.pair_mem_prod.2 ⟨hk, hb'⟩)
  have hy := (ZFSet.pair_mem_prod.1 (target.action_code.function.1 ky)).2
  have hz := (ZFSet.pair_mem_prod.1 (target.action_code.function.1 lz)).2
  have ht := (ZFSet.pair_mem_prod.1 (target.action_code.function.1 kt)).2
  have agree := ideals.1 c' hc' g' hg' h' hh' imageC imageG imageH
  have meets := cross b' hb' d' hd' y hy z hz t ht imageB imageD ky lz kt
  refine ⟨k, hk, l, hl, agree.1, agree.2, ideals.2 b' hb' imageB,
    v', hv', w', hw', y, hy, z, hz, t, ht, ?_, ?_, ky, lz, kt, meets.2, ?_, ?_, meets.1⟩
  · exact transition.equivariant g g' c v c' v' imageG imageC vv' gv
  · exact transition.equivariant h h' c w c' w' imageH imageC ww' hwAction
  · exact rootG X hX v hv v hv d' hd' X' hX' v' hv' y hy gv meetV imageD imageX vv' ky
  · exact rootH X hX w hw w hw d' hd' X' hX' w' hw' z hz hwAction meetW imageD imageX ww' lz

end PartitionPilot.Forcing.GroundMainTransition

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainTransitionValidityCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem truth_mainTransitionLawsFormula {n}
    (P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mainTransitionLawsFormula P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors) env ↔
    MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H)
      (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ)
      (env heightP) (env heightQ) (env points) (env actors) := by
  simp only [mainTransitionLawsFormula, transitionOrderFormula, transitionEquivarianceFormula,
    transitionHeightFormula, transitionAgreementFormula, Truth, truth_meetEmbeddingFormula,
    truth_groupEmbeddingFormula, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula, truth_graphFiberEqualityFormula, truth_actionAgreementBelowFormula]
  constructor
  · rintro ⟨point, order, group, equivariant, bottom, height, agreement⟩
    have pb {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env points) : x ∈ env P ∧ y ∈ env Q :=
      ZFSet.pair_mem_prod.1 (point.injection.function.1 entry)
    have ab {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env actors) : x ∈ env G ∧ y ∈ env H :=
      ZFSet.pair_mem_prod.1 (group.injection.function.1 entry)
    refine ⟨point, ?_, group, ?_, bottom, ?_, ?_⟩
    · intro x y x' y' xx yy
      have h := order x (pb xx).1 y (pb yy).1 x' (pb xx).2 y' (pb yy).2 ⟨xx, yy⟩
      exact ⟨h.1, h.2⟩
    · intro g g' x y x' y' gg xx yy act
      exact equivariant g (ab gg).1 g' (ab gg).2 x (pb xx).1 y (pb yy).1
        x' (pb xx).2 y' (pb yy).2 ⟨gg, xx, yy, act⟩
    · intro x y z entry
      exact height x (pb entry).1 y (pb entry).2 entry z
    · intro g h g' h' v v' gg hh vv agree
      exact agreement g (ab gg).1 h (ab hh).1 g' (ab gg).2 h' (ab hh).2
        v (pb vv).1 v' (pb vv).2 ⟨gg, hh, vv, agree⟩
  · intro code
    refine ⟨code.point_embedding, ?_, code.group_embedding, ?_, code.bottom, ?_, ?_⟩
    · intro x _ y _ x' _ y' _ h
      exact ⟨(code.order_iff x y x' y' h.1 h.2).1, (code.order_iff x y x' y' h.1 h.2).2⟩
    · intro g _ g' _ x _ y _ x' _ y' _ h
      exact code.equivariant g g' x y x' y' h.1 h.2.1 h.2.2.1 h.2.2.2
    · intro x _ y _ entry z
      exact code.height x y z entry
    · intro g _ h _ g' _ h' _ v _ v' _ entries
      exact code.agreement g h g' h' v v' entries.1 entries.2.1 entries.2.2.1 entries.2.2.2

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainTransitionValidity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem truth_validMainTransitionCodeFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors) env ↔
      env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H)
        (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ)
        (env heightP) (env heightQ) (env points) (env actors) := by
  simp only [validMainTransitionCodeFormula, Truth, truth_orderedPairFormula,
    truth_mainTransitionLawsFormula]

end BoundedFormula
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTaskRepresentativeRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundRelationsFormula {n} (output P Q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (groundRelationsFormula output P Q) env ↔
      env output = M.groundRelations (env P) (env Q) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => ((M.mem_groundRelations _ _ z).1 hz).1)
  intro z hz
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
    BoundedFormula.truth_relationBetweenFormula, M.mem_groundRelations]
  exact ⟨fun subset => ⟨hz, subset⟩, And.right⟩

theorem realize_groundMeetFiltersFormula {n} (output P r μ : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundMeetFiltersFormula output P r μ) env ↔
      env output = M.groundMeetFilters (env P) (env r) (env μ) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => ((M.mem_groundMeetFilters _ _ _ z).1 hz).1)
  intro z hz
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
    BoundedFormula.truth_meetFilterFormula P.succ r.succ μ.succ 0 (extend z env) meet, M.mem_groundMeetFilters]
  exact ⟨fun filter => ⟨hz, filter⟩, And.right⟩

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_groundLiteralTaskFieldFormula {n} (j : Fin 6) (output I P r μ Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundLiteralTaskFieldFormula j output I P r μ Labels) env ↔
      env output = literalTaskFieldGraph (env I) (env P)
        (M.groundRelations (env P) (env P)) (M.groundMeetFilters (env P) (env r) (env μ)) (env Labels) j := by
  simp only [groundLiteralTaskFieldFormula, realize_ex, Realize]
  constructor
  · rintro ⟨R, hR, U, hU, relations, filters, result⟩
    have bounds : ∀ i, (extend U (extend R env)) i ∈ M.sets := Fin.cases hU (Fin.cases hR members)
    have eqR := (M.realize_groundRelationsFormula 1 P.succ.succ P.succ.succ _ bounds).1 relations
    have eqU := (M.realize_groundMeetFiltersFormula 0 P.succ.succ r.succ.succ μ.succ.succ _ bounds meet).1 filters
    have outputEq := (M.realize_literalTaskFieldSetFormula pairing unions powers separation
      j output.succ.succ I.succ.succ P.succ.succ 1 0 Labels.succ.succ _ bounds).1 result
    change R = M.groundRelations (env P) (env P) at eqR
    change U = M.groundMeetFilters (env P) (env r) (env μ) at eqU
    change env output = literalTaskFieldGraph (env I) (env P) R U (env Labels) j at outputEq
    rwa [eqR, eqU] at outputEq
  · intro equal
    let R := M.groundRelations (env P) (env P)
    let U := M.groundMeetFilters (env P) (env r) (env μ)
    have hR : R ∈ M.sets := M.groundRelations_mem pairing unions powers separation (members P) (members P)
    have hU : U ∈ M.sets := M.groundMeetFilters_mem powers separation (members P) (members r) (members μ) meet
    have bounds : ∀ i, (extend U (extend R env)) i ∈ M.sets := Fin.cases hU (Fin.cases hR members)
    exact ⟨R, hR, U, hU,
      (M.realize_groundRelationsFormula 1 P.succ.succ P.succ.succ _ bounds).2 rfl,
      (M.realize_groundMeetFiltersFormula 0 P.succ.succ r.succ.succ μ.succ.succ _ bounds meet).2 rfl,
      (M.realize_literalTaskFieldSetFormula pairing unions powers separation
        j output.succ.succ I.succ.succ P.succ.succ 1 0 Labels.succ.succ _ bounds).2 equal⟩

end TransitiveGround

namespace BoundedFormula

theorem truth_taskRepresentativesFormula {n} (Reps I P G r A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskRepresentativesFormula Reps I P G r A R U Labels) env ↔
      TaskRepresentativesCode (env Reps) (env I) (env P) (env G) (env r)
        (env A) (env R) (env U) (env Labels) := by
  simp only [taskRepresentativesFormula, Truth, truth_functionFormula,
    truth_imp, truth_pairMembershipFormula, truth_taskRepresentativeFormula]
  change (_ ∧ ∀ i ∈ env I, ∀ g ∈ env G, ZFSet.pair i g ∈ env Reps →
    TaskRepresentative (env P) (env r) (env A) (env R) (env U) (env Labels) i g) ↔ _
  constructor
  · rintro ⟨function, valid⟩
    refine ⟨function, ?_⟩
    intro i g entry
    obtain ⟨hi, hg⟩ := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact valid i hi g hg entry
  · rintro ⟨function, valid⟩
    exact ⟨function, fun i _ g _ entry => valid i g entry⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundTaskRepresentativesFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (Reps P G r μ A Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundTaskRepresentativesFormula Reps P G r μ A Labels) env ↔
      TaskRepresentativesCode (env Reps)
        (M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels))
        (env P) (env G) (env r) (env A) (M.groundRelations (env P) (env P))
        (M.groundMeetFilters (env P) (env r) (env μ)) (env Labels) := by
  rw [groundTaskRepresentativesFormula, realize_exBlock]
  constructor
  · rintro ⟨fields, fieldMembers, tasks, relations, filters, selected⟩
    have bounds := extendMany_members 3 fields env fieldMembers members
    have tasksEq := (M.realize_groundEligibleTasksFormula pairing unions powers separation
      (prefixIndex n 3 0) (suffixIndex n 3 P) (suffixIndex n 3 G) (suffixIndex n 3 r)
      (suffixIndex n 3 μ) (suffixIndex n 3 A) (suffixIndex n 3 Labels) _ bounds
      (by simpa only [extendMany_suffix] using meet)).1 tasks
    have relationsEq := (M.realize_groundRelationsFormula (prefixIndex n 3 1)
      (suffixIndex n 3 P) (suffixIndex n 3 P) _ bounds).1 relations
    have filtersEq := (M.realize_groundMeetFiltersFormula (prefixIndex n 3 2)
      (suffixIndex n 3 P) (suffixIndex n 3 r) (suffixIndex n 3 μ) _ bounds
      (by simpa only [extendMany_suffix] using meet)).1 filters
    have represented := (BoundedFormula.truth_taskRepresentativesFormula
      (suffixIndex n 3 Reps) (prefixIndex n 3 0) (suffixIndex n 3 P) (suffixIndex n 3 G)
      (suffixIndex n 3 r) (suffixIndex n 3 A) (prefixIndex n 3 1) (prefixIndex n 3 2)
      (suffixIndex n 3 Labels) _).1 ((BoundedFormula.realize_toFormula M _ _ bounds).1 selected)
    simp only [extendMany_prefix, extendMany_suffix] at tasksEq relationsEq filtersEq represented
    rwa [tasksEq, relationsEq, filtersEq] at represented
  · intro selected
    let I := M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels)
    let R := M.groundRelations (env P) (env P)
    let U := M.groundMeetFilters (env P) (env r) (env μ)
    let fields : Fin 3 → ZFSet.{u} := Fin.cases I (Fin.cases R (fun _ => U))
    have fieldMembers : ∀ j, fields j ∈ M.sets :=
      Fin.cases (M.groundEligibleTasks_mem pairing unions powers separation
        (members P) (members G) (members r) (members μ) (members A) (members Labels) meet)
        (Fin.cases (M.groundRelations_mem pairing unions powers separation (members P) (members P))
          (fun _ => M.groundMeetFilters_mem powers separation (members P) (members r) (members μ) meet))
    have bounds := extendMany_members 3 fields env fieldMembers members
    refine ⟨fields, fieldMembers, ?_, ?_, ?_, ?_⟩
    · apply (M.realize_groundEligibleTasksFormula pairing unions powers separation
        (prefixIndex n 3 0) (suffixIndex n 3 P) (suffixIndex n 3 G) (suffixIndex n 3 r)
        (suffixIndex n 3 μ) (suffixIndex n 3 A) (suffixIndex n 3 Labels) _ bounds
        (by simpa only [extendMany_suffix] using meet)).2
      simp only [extendMany_prefix, extendMany_suffix]
      rfl
    · apply (M.realize_groundRelationsFormula (prefixIndex n 3 1)
        (suffixIndex n 3 P) (suffixIndex n 3 P) _ bounds).2
      simp only [extendMany_prefix, extendMany_suffix]
      rfl
    · apply (M.realize_groundMeetFiltersFormula (prefixIndex n 3 2)
        (suffixIndex n 3 P) (suffixIndex n 3 r) (suffixIndex n 3 μ) _ bounds
        (by simpa only [extendMany_suffix] using meet)).2
      simp only [extendMany_prefix, extendMany_suffix]
      rfl
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      apply (BoundedFormula.truth_taskRepresentativesFormula
        (suffixIndex n 3 Reps) (prefixIndex n 3 0) (suffixIndex n 3 P) (suffixIndex n 3 G)
        (suffixIndex n 3 r) (suffixIndex n 3 A) (prefixIndex n 3 1) (prefixIndex n 3 2)
        (suffixIndex n 3 Labels) _).2
      simp only [extendMany_prefix, extendMany_suffix]
      exact selected

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyFieldAppend
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (newValues : Fin 5 → ZFSet.{u}) (ground : ∀ j, newValues j ∈ M.sets)

theorem appendTime_value_at (j : Fin 5) :
    (fields.appendTime pairing unions newValues ground).value j T = newValues j := by
  apply GroundChronologyFields.value_eq_of_entry
  exact ZFSet.mem_insert _ _

theorem appendTime_graph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (time : ZFSet.rank T < o) (graphs : ∀ j, ZFSet.rank (fields.graph j) < o)
    (values : ∀ j, ZFSet.rank (newValues j) < o) (j : Fin 5) :
    ZFSet.rank ((fields.appendTime pairing unions newValues ground).graph j) < o := by
  rw [appendTime_graph, ZFSet.rank_insert]
  exact max_lt (limit.succ_lt (rank_orderedPair_lt limit time (values j))) (graphs j)

end PartitionPilot.Forcing.GroundChronologyFields

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTwoStageMainDiagram
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace BoundedFormula

theorem truth_graphCutoffEqualityFormula {n} (cutoff source target : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (graphCutoffEqualityFormula cutoff source target) env ↔
      ∀ s, s = env cutoff ∨ s ∈ env cutoff → ∀ x,
        ZFSet.pair s x ∈ env source ↔ ZFSet.pair s x ∈ env target := by
  simp only [graphCutoffEqualityFormula, Truth, truth_graphFiberEqualityFormula]
  constructor
  · rintro ⟨terminal, earlier⟩ s (rfl | hs) x
    · exact terminal x
    · exact earlier s hs x
  · intro h
    exact ⟨h _ (Or.inl rfl), fun s hs => h s (Or.inr hs)⟩

theorem truth_chronologyGraphPrefixFormula {n} (cutoff : Fin n) (source target : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyGraphPrefixFormula cutoff source target) env ↔
      ChronologyGraphPrefixCode (env cutoff) (fun j => env (source j)) (fun j => env (target j)) := by
  simp only [chronologyGraphPrefixFormula, Truth, truth_graphCutoffEqualityFormula]
  exact ⟨fun ⟨a, b, c, d, e⟩ => Fin.cases a (Fin.cases b (Fin.cases c
      (Fin.cases d (Fin.cases e (fun i => Fin.elim0 i))))),
    fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩⟩

theorem truth_chronologicalTransitionExtraFormula {n}
    (P Q points sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u})
    (shape : env points ⊆ ZFSet.prod (env P) (env Q)) :
    Truth (chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs) env ↔
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j)) := by
  simp only [chronologicalTransitionExtraFormula, Truth, truth_disj, transitionHeightFormula,
    truth_imp, truth_pairMembershipFormula, truth_graphFiberEqualityFormula,
    truth_chronologyGraphPrefixFormula]
  constructor
  · rintro ⟨cutoff, birth, history⟩
    refine ⟨cutoff, ?_, history⟩
    intro x y t entry
    have bounds := ZFSet.pair_mem_prod.1 (shape entry)
    exact birth x bounds.1 y bounds.2 entry t
  · intro h
    exact ⟨h.cutoff_le, fun x _ y _ entry t => h.birth x y t entry, h.history_prefix⟩

theorem truth_oldBirthFiberCoverageFormula {n} (P points birth cutoff : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (oldBirthFiberCoverageFormula P points birth cutoff) env ↔
      OldBirthFiberCoverageCode (env P) (env points) (env birth) (env cutoff) := by
  simp only [oldBirthFiberCoverageFormula, Truth, truth_imp, truth_orderedPairFormula,
    truth_disj, truth_exMem, truth_pairMembershipFormula]
  change (∀ p ∈ env birth, ∀ a ∈ p, ∀ y ∈ a, ∀ b ∈ p, ∀ t ∈ b,
    (p = ZFSet.pair y t ∧ (t = env cutoff ∨ t ∈ env cutoff)) →
      ∃ x ∈ env P, ZFSet.pair x y ∈ env points) ↔ _
  constructor
  · intro h y t entry before
    exact h (ZFSet.pair y t) entry {y, t} (ZFSet.mem_pair.2 (Or.inr rfl)) y
      (ZFSet.mem_pair.2 (Or.inl rfl)) {y, t} (ZFSet.mem_pair.2 (Or.inr rfl)) t
      (ZFSet.mem_pair.2 (Or.inr rfl)) ⟨rfl, before⟩
  · intro h p hp a _ y _ b _ t _ data
    exact h y t (data.1 ▸ hp) data.2

end BoundedFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRawLayerPushforward
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_mapFamilyDiagonal (I i k : ZFSet.{u}) :
    ZFSet.pair i k ∈ mapFamilyDiagonal I ↔ i ∈ I ∧ k = ZFSet.pair i i := by
  constructor
  · intro entry
    obtain ⟨j, hj, a, _, b, _, equal, first, second⟩ := (mem_pairedGraph _ _ _ _ _ _).1 entry
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    have fa := (pair_mem_identityFunctionGraph I i a).1 first
    have fb := (pair_mem_identityFunctionGraph I i b).1 second
    exact ⟨hj, congrArg₂ ZFSet.pair fa.1.symm fb.1.symm⟩
  · rintro ⟨hi, rfl⟩
    exact (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2 ⟨hi, hi, hi,
      (pair_mem_identityFunctionGraph I i i).2 ⟨rfl, hi⟩,
      (pair_mem_identityFunctionGraph I i i).2 ⟨rfl, hi⟩⟩

theorem mapFamilyDiagonal_function (I : ZFSet.{u}) :
    ZFSet.IsFunc I (ZFSet.prod I I) (mapFamilyDiagonal I) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, a, ha, b, hb, rfl, _, _⟩ := (mem_pairedGraph _ _ _ _ _ _).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hi, ZFSet.pair_mem_prod.2 ⟨ha, hb⟩⟩
  intro i hi
  exact ⟨ZFSet.pair i i, (pair_mem_mapFamilyDiagonal I i _).2 ⟨hi, rfl⟩,
    fun k hk => ((pair_mem_mapFamilyDiagonal I i k).1 hk).2⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mapFamilyPushforward_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I U A B Maps e : ZFSet.{u}}
    (hI : I ∈ M.sets) (hU : U ∈ M.sets) (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (he : e ∈ M.sets) (maps : FunctionGraphOn I Maps) :
    M.mapFamilyPushforward I U A B Maps e ∈ M.sets ∧
      ZFSet.IsFunc I (M.groundRelations U B) (M.mapFamilyPushforward I U A B Maps e) ∧
      ∀ i f c, ZFSet.pair i f ∈ Maps →
        (ZFSet.pair i c ∈ M.mapFamilyPushforward I U A B Maps e ↔
          c = relationCompose U A B f e) := by
  have hII := M.prod_mem pairing unions powers separation hI hI
  have hW := M.groundRelations_mem pairing unions powers separation hU hB
  have hConst := M.constantFamilyGraph_mem pairing unions powers separation hI he
  have composed := M.groundPairCompositions_spec pairing unions powers separation
    hII hI hI hU hA hB hMaps hConst maps
    ⟨{e}, constantFamilyGraph_function I e⟩ (fun _ hx => hx)
  have hId := M.identityFunctionGraph_mem pairing unions powers separation hI
  have hDelta := M.pairedGraph_mem pairing unions powers separation hI hI hI hId hId
  refine ⟨M.relationCompose_mem pairing unions powers separation hI hII hW hDelta composed.1,
    relationCompose_function_of_subset (mapFamilyDiagonal_function I) composed.2.1 (fun _ hx => hx), ?_⟩
  intro i f c entry
  have hi := maps.pair_source entry
  have constant := (pair_mem_constantFamilyGraph I e i e).2 ⟨hi, rfl⟩
  have atDiagonal := composed.2.2 i i f e c entry constant
  constructor
  · intro copied
    obtain ⟨_, _, k, _, diagonal, output⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 copied
    have equal := ((pair_mem_mapFamilyDiagonal I i k).1 diagonal).2
    rw [equal] at output
    exact (atDiagonal.1 output).2
  · intro equal
    have output := atDiagonal.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hi⟩, equal⟩
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi,
      (ZFSet.pair_mem_prod.1 (composed.2.1.1 output)).2,
      ZFSet.pair i i, ZFSet.pair_mem_prod.2 ⟨hi, hi⟩,
      (pair_mem_mapFamilyDiagonal I i _).2 ⟨hi, rfl⟩, output⟩

end TransitiveGround

theorem relationImage_compose_bound {P U A B f e x y : ZFSet.{u}}
    (subset : P ⊆ U) (image : x ∈ relationImage P A f)
    (hy : y ∈ B) (copied : ZFSet.pair x y ∈ e) :
    y ∈ relationImage P B (relationCompose U A B f e) := by
  obtain ⟨hx, p, hp, entry⟩ := (mem_relationImage _ _ _ _).1 image
  exact (mem_relationImage _ _ _ _).2 ⟨hy, p, hp,
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨subset hp, hy, x, hx, entry, copied⟩⟩

namespace CopyEmbeddingFamilyCode

theorem pushforward
    {Qs rs μs A B rA rB μA μB t I Indices Maps Maps' U e : ZFSet.{u}}
    (code : CopyEmbeddingFamilyCode Qs rs μs A rA μA t I Indices Maps)
    (maps : FunctionGraphOn I Maps)
    (entries : ∀ i f c, ZFSet.pair i f ∈ Maps →
      (ZFSet.pair i c ∈ Maps' ↔ c = relationCompose U A B f e))
    (bound : ∀ s P, ZFSet.pair s P ∈ Qs → P ⊆ U)
    (embedding : MeetEmbeddingCode A B rA rB μA μB e) :
    CopyEmbeddingFamilyCode Qs rs μs B rB μB t I Indices Maps' := by
  intro i hi s hs c P R V index map qField rField mField
  obtain ⟨f, oldMap⟩ := maps.total hi
  have original := code i hi s hs f P R V index oldMap qField rField mField
  rw [(entries i f c oldMap).1 map,
    relationCompose_domain_eq (bound s P qField) original.injection.function.1]
  exact original.compose embedding
end CopyEmbeddingFamilyCode

namespace CountableLayerCode

theorem ground_pushforward
    {M : TransitiveGround.{u}} {A B old born t D N injection e : ZFSet.{u}}
    (code : CountableLayerCode A old t D N injection)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets) (he : e ∈ M.sets)
    (hD : D ∈ M.sets) (hInjection : injection ∈ M.sets)
    (embedding : InjectionCode A B e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    ∃ D' ∈ M.sets, ∃ injection' ∈ M.sets, CountableLayerCode B born t D' N injection' := by
  let D0 := ZFSet.sep (fun x => x ∈ A) D
  let f0 := ZFSet.sep (fun z => z ∈ ZFSet.prod D0 N) injection
  let e0 := ZFSet.sep (fun z => z ∈ ZFSet.prod D0 B) e
  have hD0 : D0 ∈ M.sets := M.bounded_separation_mem separation (.mem 0 1)
    (extend A Fin.elim0) (Fin.cases hA (fun i => Fin.elim0 i)) hD
  have hf0 : f0 ∈ M.sets := M.injection_restriction_mem separation hD0 hN hInjection
  have he0 : e0 ∈ M.sets := M.injection_restriction_mem separation hD0 hB he
  have fcode : InjectionCode D0 N f0 := code.small.restrict (fun _ hx => (ZFSet.mem_sep.1 hx).1)
  have ecode : InjectionCode D0 B e0 := embedding.restrict (fun _ hx => (ZFSet.mem_sep.1 hx).2)
  refine ⟨relationImage D0 B e0, M.relationImage_mem separation hD0 hB he0,
    pushedHeightGraph D0 B N e0 f0,
    M.pushedHeightGraph_mem pairing unions powers separation hD0 hB hN he0 hf0,
    ecode.converse_image.compose fcode, ?_⟩
  intro y hy yt
  obtain ⟨x, hx, copied⟩ := noNew y hy yt
  have hD0x : x ∈ D0 := ZFSet.mem_sep.2 ⟨code.cover x hx ((preserves x y t copied).1 yt), hx⟩
  exact (mem_relationImage _ _ _ _).2 ⟨hy, x, hD0x,
    ZFSet.mem_sep.2 ⟨copied, ZFSet.pair_mem_prod.2 ⟨hD0x, hy⟩⟩⟩
end CountableLayerCode

namespace CopyLayerCode

theorem ground_pushforward
    {M : TransitiveGround.{u}}
    {Qs rs μs A B rA rB μA μB old born t I parts Indices Maps W N injection e : ZFSet.{u}}
    (code : CopyLayerCode Qs rs μs A rA μA old t I parts Indices Maps W N injection)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hI : I ∈ M.sets) (hParts : parts ∈ M.sets) (hMaps : Maps ∈ M.sets)
    (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    let U := familyPointBound Qs
    let Maps' := M.mapFamilyPushforward I U A B Maps e
    let W' := M.groundRelations U B
    let parts' := relationCompose I A B parts e
    Maps' ∈ M.sets ∧ W' ∈ M.sets ∧ parts' ∈ M.sets ∧
      CopyLayerCode Qs rs μs B rB μB born t I parts' Indices Maps' W' N injection := by
  dsimp only
  have hU := M.familyPointBound_mem unions hQs
  have maps : FunctionGraphOn I Maps := ⟨W, code.maps⟩
  have pushed := M.mapFamilyPushforward_spec pairing unions powers separation hI hU hA hB hMaps he maps
  have bound : ∀ s P, ZFSet.pair s P ∈ Qs → P ⊆ familyPointBound Qs :=
    fun _ _ entry _ hp => mem_familyPointBound_of_entry entry hp
  refine ⟨pushed.1, M.groundRelations_mem pairing unions powers separation hU hB,
    M.relationCompose_mem pairing unions powers separation hI hA hB hParts he,
    code.small, code.indices, pushed.2.1,
    code.embedding.pushforward maps pushed.2.2 bound embedding, ?_, ?_⟩
  · intro y hy yt
    obtain ⟨x, hx, copied⟩ := noNew y hy yt
    obtain ⟨i, hi, part⟩ := code.cover x hx ((preserves x y t copied).1 yt)
    exact ⟨i, hi, (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi, hy, x, hx, part, copied⟩⟩
  · intro i hi s hs c P y hy index map qField part
    obtain ⟨f, oldMap⟩ := maps.total hi
    rw [(pushed.2.2 i f c oldMap).1 map]
    obtain ⟨_, _, x, hx, original, copied⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 part
    exact relationImage_compose_bound (bound s P qField)
      (code.inCopy i hi s hs f P x hx index oldMap qField original) hy copied
end CopyLayerCode

namespace SeparatedLayerCode

theorem ground_pushforward
    {M : TransitiveGround.{u}}
    {Qs rs μs A B rA rB μA μB old born t I Indices Maps W Components F e : ZFSet.{u}}
    (code : SeparatedLayerCode Qs rs μs A rA μA old t I Indices Maps W Components F)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hI : I ∈ M.sets) (hMaps : Maps ∈ M.sets) (hComponents : Components ∈ M.sets) (hF : F ∈ M.sets)
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    let U := familyPointBound Qs
    let Maps' := M.mapFamilyPushforward I U A B Maps e
    let W' := M.groundRelations U B
    let eF := layerFiberEmbedding F B e
    let F' := relationImage F B eF
    let Components' := pushedHeightGraph F B I eF Components
    Maps' ∈ M.sets ∧ W' ∈ M.sets ∧ Components' ∈ M.sets ∧ F' ∈ M.sets ∧
      SeparatedLayerCode Qs rs μs B rB μB born t I Indices Maps' W' Components' F' := by
  dsimp only
  have hU := M.familyPointBound_mem unions hQs
  have maps : FunctionGraphOn I Maps := ⟨W, code.maps⟩
  have pushed := M.mapFamilyPushforward_spec pairing unions powers separation hI hU hA hB hMaps he maps
  have bound : ∀ s P, ZFSet.pair s P ∈ Qs → P ⊆ familyPointBound Qs :=
    fun _ _ entry _ hp => mem_familyPointBound_of_entry entry hp
  have fiberPoint : ∀ x ∈ F, x ∈ A ∧ ZFSet.pair x t ∈ old := by
    intro x hx
    exact (mem_layerBirthFiber A old t x).1 (code.fiber ▸ hx)
  have ecode : InjectionCode F B (layerFiberEmbedding F B e) :=
    embedding.injection.restrict (fun x hx => (fiberPoint x hx).1)
  have heF : layerFiberEmbedding F B e ∈ M.sets := M.injection_restriction_mem separation hF hB he
  have fiberEq : relationImage F B (layerFiberEmbedding F B e) = layerBirthFiber B born t := by
    apply ZFSet.ext
    intro y
    rw [mem_relationImage, mem_layerBirthFiber]
    constructor
    · rintro ⟨hy, x, hx, copied⟩
      exact ⟨hy, (preserves x y t (ZFSet.mem_sep.1 copied).1).2 (fiberPoint x hx).2⟩
    · rintro ⟨hy, yt⟩
      obtain ⟨x, hx, copied⟩ := noNew y hy yt
      have hFx : x ∈ F := code.fiber.symm ▸
        (mem_layerBirthFiber A old t x).2 ⟨hx, (preserves x y t copied).1 yt⟩
      exact ⟨hy, x, hFx, ZFSet.mem_sep.2 ⟨copied, ZFSet.pair_mem_prod.2 ⟨hFx, hy⟩⟩⟩
  refine ⟨pushed.1, M.groundRelations_mem pairing unions powers separation hU hB,
    M.pushedHeightGraph_mem pairing unions powers separation hF hB hI heF hComponents,
    M.relationImage_mem separation hF hB heF,
    code.indices, pushed.2.1, fiberEq, pushedHeightGraph_function ecode code.components,
    code.embedding.pushforward maps pushed.2.2 bound embedding, ?_, ?_⟩
  · intro i hi s hs c P y hy index map qField component
    obtain ⟨f, oldMap⟩ := maps.total hi
    rw [(pushed.2.2 i f c oldMap).1 map]
    obtain ⟨_, _, x, hx, inverse, oldComponent⟩ :=
      (pair_mem_relationCompose _ _ _ _ _ _ _).1 component
    have copied := (pair_mem_relationConverse _ _ _ _ _).1 inverse
    exact relationImage_compose_bound (bound s P qField)
      (code.cover i hi s hs f P x (fiberPoint x hx).1 index oldMap qField oldComponent)
      hy (ZFSet.mem_sep.1 copied.2.2).1
  · intro y hy z hz i hi j hj yi zj different
    obtain ⟨_, x, hx, xy⟩ := (mem_relationImage _ _ _ _).1 hy
    obtain ⟨_, w, hw, wz⟩ := (mem_relationImage _ _ _ _).1 hz
    have xi := (pushedHeightGraph_entry ecode code.components xy).1 yi
    have wj := (pushedHeightGraph_entry ecode code.components wz).1 zj
    exact (code.separated x hx w hw i hi j hj xi wj different).map source embedding
      (fun a b s copied born => (preserves a b s copied).2 born)
      (ZFSet.mem_sep.1 xy).1 (ZFSet.mem_sep.1 wz).1
end SeparatedLayerCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedMainInvariantCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_linkedMainInvariantFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D P G cutoff serial : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainInvariantFormula K Labels C D P G cutoff serial) env ↔
      LinkedMainInvariantCode M (env K) (env Labels) (env C) (env D)
        (env P) (env G) (env cutoff) (env serial) := by
  change (Realize M.sets (groundBelowFormula P K) env ∧
    Realize M.sets (groundBelowFormula G K) env ∧
    Realize M.sets (groundBelowFormula Labels K) env ∧
    Realize M.sets (cumulativeRankLtFormula P K) env ∧
    Realize M.sets (cumulativeRankLtFormula G K) env ∧
    Realize M.sets (cumulativeRankLtFormula Labels K) env ∧ env cutoff ∈ env K ∧
    Realize M.sets (cumulativeRankLtFormula C K) env ∧
    Realize M.sets (cumulativeRankLtFormula D K) env ∧
    Realize M.sets (cumulativeRankLtFormula serial K) env) ↔ _
  rw [M.realize_groundBelowFormula P K env members,
    M.realize_groundBelowFormula G K env members,
    M.realize_groundBelowFormula Labels K env members,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection P K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection G K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection Labels K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection C K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection D K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection serial K env members ordinal]
  rfl

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundGrowthLayerRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

private theorem realize_boundedExBlock {n} (k : Nat) (φ : BoundedFormula (n + k))
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (exBlock k φ.toFormula) env ↔
      ∃ fields : Fin k → ZFSet.{u}, (∀ i, fields i ∈ M.sets) ∧
        BoundedFormula.Truth φ (extendMany k fields env) := by
  rw [realize_exBlock]
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (BoundedFormula.realize_toFormula M φ _
      (extendMany_members k fields env ground members)).1 recognized⟩
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (BoundedFormula.realize_toFormula M φ _
      (extendMany_members k fields env ground members)).2 recognized⟩

theorem realize_countableGrowthWitnessFormula {n} (z L birth t N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (countableGrowthWitnessFormula z L birth t N) env ↔
      ∃ D injection, env z = countableLayerWitness D injection ∧
        CountableLayerCode (env L) (env birth) (env t) D (env N) injection := by
  rw [countableGrowthWitnessFormula, M.realize_boundedExBlock _ _ env members]
  constructor
  · rintro ⟨fields, _, recognized⟩
    have meaning := (BoundedFormula.truth_countableTaggedLayerFormula
      (suffixIndex n 3 z) (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2)
      (suffixIndex n 3 L) (suffixIndex n 3 birth) (suffixIndex n 3 t) (suffixIndex n 3 N)
      (extendMany 3 fields env)).1 recognized
    simp only [extendMany_prefix, extendMany_suffix] at meaning
    exact ⟨fields 1, fields 2, meaning.2⟩
  · rintro ⟨D, injection, equal, code⟩
    let fields : Fin 3 → ZFSet.{u} := Fin.cases (natSetCode 0) (Fin.cases D (fun _ => injection))
    have hWitness : countableLayerWitness D injection ∈ M.sets := equal ▸ members z
    have ground : ∀ i, fields i ∈ M.sets :=
      M.nonemptyTupleCode_field_mem 2 fields hWitness
    refine ⟨fields, ground, ?_⟩
    apply (BoundedFormula.truth_countableTaggedLayerFormula
      (suffixIndex n 3 z) (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2)
      (suffixIndex n 3 L) (suffixIndex n 3 birth) (suffixIndex n 3 t) (suffixIndex n 3 N)
      (extendMany 3 fields env)).2
    simp only [extendMany_prefix, extendMany_suffix]
    exact ⟨rfl, equal, code⟩

theorem realize_copyGrowthWitnessFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (z Qs rs μs L r μ birth t N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (copyGrowthWitnessFormula z Qs rs μs L r μ birth t N) env ↔
      ∃ I parts Indices Maps W injection,
        env z = copyLayerWitness I parts Indices Maps W injection ∧
        CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
          (env t) I parts Indices Maps W (env N) injection := by
  rw [copyGrowthWitnessFormula, M.realize_boundedExBlock _ _ env members]
  constructor
  · rintro ⟨fields, _, recognized⟩
    have meaning := (BoundedFormula.truth_copyTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (suffixIndex n 10 N) (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env)).1 recognized
    simp only [extendMany_prefix, extendMany_suffix] at meaning
    exact ⟨fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
      meaning.2.1, meaning.2.2.2.2.2⟩
  · rintro ⟨I, parts, Indices, Maps, W, injection, equal, code⟩
    let stored : Fin 7 → ZFSet.{u} := Fin.cases (natSetCode 1) (Fin.cases I (Fin.cases parts
      (Fin.cases Indices (Fin.cases Maps (Fin.cases W (fun _ => injection))))))
    have hWitness : nonemptyTupleCode 6 stored ∈ M.sets := by
      change copyLayerWitness I parts Indices Maps W injection ∈ M.sets
      exact equal ▸ members z
    have storedGround := M.nonemptyTupleCode_field_mem 6 stored hWitness
    let fields : Fin 10 → ZFSet.{u} := Fin.cases (natSetCode 1) (Fin.cases I (Fin.cases parts
      (Fin.cases Indices (Fin.cases Maps (Fin.cases W (Fin.cases injection
        (Fin.cases (⋃₀ ⋃₀ env Qs) (Fin.cases (⋃₀ ⋃₀ env rs) (fun _ => ⋃₀ ⋃₀ env μs)))))))))
    have ground : ∀ i, fields i ∈ M.sets :=
      (Fin.cases (storedGround 0) (Fin.cases (storedGround 1) (Fin.cases (storedGround 2) (Fin.cases (storedGround 3) (Fin.cases (storedGround 4) (Fin.cases (storedGround 5) (Fin.cases (storedGround 6) (Fin.cases (M.union_mem unions (M.union_mem unions (members Qs))) (Fin.cases (M.union_mem unions (M.union_mem unions (members rs))) (fun _ => (M.union_mem unions (M.union_mem unions (members μs)))))))))))))
    refine ⟨fields, ground, ?_⟩
    apply (BoundedFormula.truth_copyTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (suffixIndex n 10 N) (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env)).2
    simp only [extendMany_prefix, extendMany_suffix]
    exact ⟨rfl, equal, rfl, rfl, rfl, code⟩

theorem realize_separatedGrowthWitnessFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (z Qs rs μs L r μ birth t : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Realize M.sets (separatedGrowthWitnessFormula z Qs rs μs L r μ birth t) env ↔
      ∃ I Indices Maps W Components F,
        env z = separatedLayerWitness I Indices Maps W Components F ∧
        SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
          (env t) I Indices Maps W Components F := by
  rw [separatedGrowthWitnessFormula, M.realize_boundedExBlock _ _ env members]
  constructor
  · rintro ⟨fields, _, recognized⟩
    have liftedMeet : MeetOrderCode
        (extendMany 10 fields env (suffixIndex n 10 L))
        (extendMany 10 fields env (suffixIndex n 10 r))
        (extendMany 10 fields env (suffixIndex n 10 μ)) := by
      simpa only [extendMany_suffix] using meet
    have meaning := (BoundedFormula.truth_separatedTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env) liftedMeet).1 recognized
    simp only [extendMany_prefix, extendMany_suffix] at meaning
    exact ⟨fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
      meaning.2.1, meaning.2.2.2.2.2⟩
  · rintro ⟨I, Indices, Maps, W, Components, F, equal, code⟩
    let stored : Fin 7 → ZFSet.{u} := Fin.cases (natSetCode 2) (Fin.cases I (Fin.cases Indices
      (Fin.cases Maps (Fin.cases W (Fin.cases Components (fun _ => F))))))
    have hWitness : nonemptyTupleCode 6 stored ∈ M.sets := by
      change separatedLayerWitness I Indices Maps W Components F ∈ M.sets
      exact equal ▸ members z
    have storedGround := M.nonemptyTupleCode_field_mem 6 stored hWitness
    let fields : Fin 10 → ZFSet.{u} := Fin.cases (natSetCode 2) (Fin.cases I (Fin.cases Indices
      (Fin.cases Maps (Fin.cases W (Fin.cases Components (Fin.cases F
        (Fin.cases (⋃₀ ⋃₀ env Qs) (Fin.cases (⋃₀ ⋃₀ env rs) (fun _ => ⋃₀ ⋃₀ env μs)))))))))
    have ground : ∀ i, fields i ∈ M.sets :=
      (Fin.cases (storedGround 0) (Fin.cases (storedGround 1) (Fin.cases (storedGround 2) (Fin.cases (storedGround 3) (Fin.cases (storedGround 4) (Fin.cases (storedGround 5) (Fin.cases (storedGround 6) (Fin.cases (M.union_mem unions (M.union_mem unions (members Qs))) (Fin.cases (M.union_mem unions (M.union_mem unions (members rs))) (fun _ => (M.union_mem unions (M.union_mem unions (members μs)))))))))))))
    refine ⟨fields, ground, ?_⟩
    have liftedMeet : MeetOrderCode
        (extendMany 10 fields env (suffixIndex n 10 L))
        (extendMany 10 fields env (suffixIndex n 10 r))
        (extendMany 10 fields env (suffixIndex n 10 μ)) := by
      simpa only [extendMany_suffix] using meet
    apply (BoundedFormula.truth_separatedTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env) liftedMeet).2
    simp only [extendMany_prefix, extendMany_suffix]
    exact ⟨rfl, equal, rfl, rfl, rfl, code⟩

theorem realize_growthLayerWitnessFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (z Qs rs μs L r μ birth t N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Realize M.sets (growthLayerWitnessFormula z Qs rs μs L r μ birth t N) env ↔
      GrowthLayerWitnessCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env birth) (env t) (env N) (env z) := by
  rw [growthLayerWitnessFormula, realize_disj, realize_disj,
    M.realize_countableGrowthWitnessFormula z L birth t N env members,
    M.realize_copyGrowthWitnessFormula unions z Qs rs μs L r μ birth t N env members,
    M.realize_separatedGrowthWitnessFormula unions z Qs rs μs L r μ birth t env members meet]
  rfl

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SerializedChronologyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace ChronologyCoreCode
theorem meet_of_entries {T V C D rD s L r μ birth : ZFSet.{u}}
    {graphs : Fin 5 → ZFSet.{u}} (core : ChronologyCoreCode T V C D rD graphs)
    (hs : s ∈ T) (eL : ZFSet.pair s L ∈ graphs 0) (er : ZFSet.pair s r ∈ graphs 1)
    (eμ : ZFSet.pair s μ ∈ graphs 2) (eb : ZFSet.pair s birth ∈ graphs 3) :
    MeetOrderCode L r μ := by
  obtain ⟨height, entry, _⟩ := (core.function 4).2 s hs
  exact (core.point s hs L r μ birth height eL er eμ eb entry).meet
end ChronologyCoreCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SerializedChronologyFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_chronologyLayerLookupFormula {n} (T : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyLayerLookupFormula T graphs layers s t L r μ birth z) env ↔
      ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
        (env s) (env t) (env L) (env r) (env μ) (env birth) (env z) := by
  simp only [chronologyLayerLookupFormula, Truth, truth_disj, truth_pairMembershipFormula,
    truth_tripleMembershipFormula, ChronologyLayerLookup]
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_chronologyLayerClause
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (T V C D rD N : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets)
    (core : ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j))) :
    Realize M.sets (chronologyLayerClause T N graphs layers s t L r μ birth z) env ↔
      (ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
        (env s) (env t) (env L) (env r) (env μ) (env birth) (env z) →
        GrowthLayerWitnessCode (env (graphs 0)) (env (graphs 1)) (env (graphs 2))
          (env L) (env r) (env μ) (env birth) (env t) (env N) (env z)) := by
  rw [chronologyLayerClause, realize_imp]
  have lookup := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_chronologyLayerLookupFormula T graphs layers s t L r μ birth z env)
  have recognized (h : ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
      (env s) (env t) (env L) (env r) (env μ) (env birth) (env z)) :=
    M.realize_growthLayerWitnessFormula unions z (graphs 0) (graphs 1) (graphs 2)
      L r μ birth t N env members
      (core.meet_of_entries h.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1)
  exact ⟨fun h actual => (recognized actual).1 (h (lookup.2 actual)),
    fun h actual => (recognized (lookup.1 actual)).2 (h (lookup.1 actual))⟩

theorem realize_chronologyLayerEntriesFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (T V C D rD N : Fin n) (graphs : Fin 5 → Fin n) (layers : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (core : ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j))) :
    Realize M.sets (chronologyLayerEntriesFormula T N graphs layers) env ↔
      ChronologyLayerEntries (env T) (env N) (fun j => env (graphs j)) (env layers) := by
  let old := suffixIndex n 7
  let field := prefixIndex n 7
  let body := chronologyLayerClause (old T) (old N) (fun j => old (graphs j))
    (old layers) (field 0) (field 1) (field 2) (field 3) (field 4) (field 5) (field 6)
  have clause (values : Fin 7 → ZFSet.{u}) (ground : ∀ i, values i ∈ M.sets) :
      Realize M.sets body (extendMany 7 values env) ↔
        (ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
          (values 0) (values 1) (values 2) (values 3) (values 4) (values 5) (values 6) →
          GrowthLayerWitnessCode (env (graphs 0)) (env (graphs 1)) (env (graphs 2))
            (values 2) (values 3) (values 4) (values 5) (values 1) (env N) (values 6)) := by
    have lifted : ChronologyCoreCode ((extendMany 7 values env) (old T))
        ((extendMany 7 values env) (old V)) ((extendMany 7 values env) (old C))
        ((extendMany 7 values env) (old D)) ((extendMany 7 values env) (old rD))
        (fun j => (extendMany 7 values env) (old (graphs j))) := by
      simpa only [old, extendMany_suffix] using core
    simpa only [body, old, field, extendMany_prefix, extendMany_suffix] using
      M.realize_chronologyLayerClause unions (old T) (old V) (old C) (old D) (old rD)
        (old N) (fun j => old (graphs j)) (old layers) (field 0) (field 1) (field 2)
        (field 3) (field 4) (field 5) (field 6) (extendMany 7 values env)
        (extendMany_members 7 values env ground members) lifted
  change Realize M.sets (allBlock 7 body) env ↔ _
  rw [realize_allBlock]
  constructor
  · intro recognized s hs t ht earlier L r μ birth z eL er eμ eb entry
    let values : Fin 7 → ZFSet.{u} := Fin.cases s (Fin.cases t (Fin.cases L
      (Fin.cases r (Fin.cases μ (Fin.cases birth (fun _ => z))))))
    have ground : ∀ i, values i ∈ M.sets :=
      Fin.cases (M.transitive (members T) hs) (Fin.cases (M.transitive (members T) ht)
        (Fin.cases (M.pair_right (M.transitive (members (graphs 0)) eL))
          (Fin.cases (M.pair_right (M.transitive (members (graphs 1)) er))
            (Fin.cases (M.pair_right (M.transitive (members (graphs 2)) eμ))
              (Fin.cases (M.pair_right (M.transitive (members (graphs 3)) eb))
                (fun _ => M.pair_right (M.transitive (members layers) entry)))))))
    exact (clause values ground).1 (recognized values ground) ⟨hs, ht, earlier, eL, er, eμ, eb, entry⟩
  · intro code values ground
    apply (clause values ground).2
    rintro ⟨hs, ht, earlier, eL, er, eμ, eb, entry⟩
    exact code _ hs _ ht earlier _ _ _ _ _ eL er eμ eb entry

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_chronologyLayerFunctionFormula {n} (T W layers : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyLayerFunctionFormula T W layers) env ↔
      ZFSet.IsFunc (chronologyPairs (env T)) (env W) (env layers) := by
  rw [chronologyLayerFunctionFormula, realize_ex]
  constructor
  · rintro ⟨J, hJ, recognized, function⟩
    have equal := (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
      (extend J env) (Fin.cases hJ members)).1 recognized
    have actual := (BoundedFormula.realize_toFormula M _ (extend J env) (Fin.cases hJ members)).1 function
    have code := (BoundedFormula.truth_functionFormula 0 W.succ layers.succ (extend J env)).1 actual
    exact equal ▸ code
  · intro function
    have hJ := M.chronologyPairs_mem pairing unions powers separation (members T)
    exact ⟨chronologyPairs (env T), hJ,
      (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
        (extend (chronologyPairs (env T)) env) (Fin.cases hJ members)).2 rfl,
      (BoundedFormula.realize_toFormula M _ _ (Fin.cases hJ members)).2
        ((BoundedFormula.truth_functionFormula 0 W.succ layers.succ _).2 function)⟩

theorem realize_serializedChronologyFormula {n} (T V C D rD N : Fin n)
    (graphs : Fin 5 → Fin n) (W layers : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (serializedChronologyFormula T V C D rD N graphs W layers) env ↔
      SerializedChronologyCode (env T) (env V) (env C) (env D) (env rD) (env N)
        (fun j => env (graphs j)) (env W) (env layers) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula T).toFormula env ∧
    Realize M.sets (BoundedFormula.chronologyCoreFormula T V C D rD graphs).toFormula env ∧
    Realize M.sets (chronologyLayerFunctionFormula T W layers) env ∧
    Realize M.sets (chronologyLayerEntriesFormula T N graphs layers) env) ↔ _
  rw [BoundedFormula.realize_ordinalFormula M T env members, ← ordinalSetProperty_iff,
    BoundedFormula.realize_chronologyCoreFormula M T V C D rD graphs env members,
    M.realize_chronologyLayerFunctionFormula pairing unions powers separation T W layers env members]
  constructor
  · rintro ⟨ordinal, core, function, entries⟩
    exact ⟨ordinal, core, function,
      (M.realize_chronologyLayerEntriesFormula unions T V C D rD N graphs layers env members core).1 entries⟩
  · intro code
    exact ⟨code.ordinal, code.core, code.function,
      (M.realize_chronologyLayerEntriesFormula unions T V C D rD N graphs layers env members code.core).2 code.entries⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageCandidates
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_bottomFormula {n} (P r b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (bottomFormula P r b) env ↔
      env b ∈ env P ∧ ∀ x ∈ env P, ZFSet.pair (env b) x ∈ env r := by
  simp only [bottomFormula, Truth, truth_pairMembershipFormula]
  rfl

theorem truth_productEquationFormula {n} (B C D : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productEquationFormula B C D) env ↔ env B = ZFSet.prod (env C) (env D) := by
  simp only [productEquationFormula, Truth, truth_productElementFormula,
    truth_pairMembershipFormula]
  change ((∀ z ∈ env B, z ∈ ZFSet.prod (env C) (env D)) ∧
    ∀ c ∈ env C, ∀ d ∈ env D, ZFSet.pair c d ∈ env B) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro z
    refine ⟨subset z, ?_⟩
    rintro hz
    obtain ⟨c, hc, d, hd, rfl⟩ := ZFSet.mem_prod.1 hz
    exact covers c hc d hd
  · rintro equal
    rw [equal]
    exact ⟨fun _ h => h, fun _ hc _ hd => ZFSet.pair_mem_prod.2 ⟨hc, hd⟩⟩

theorem truth_mainStageLawsFormula {n}
    (P r μ G m inv one A b t height C D rD : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainStageLawsFormula P r μ G m inv one A b t height C D rD) env ↔
      MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) := by
  simp only [mainStageLawsFormula, Truth, truth_meetOrderFormula, truth_groupFormula,
    truth_posetActionFormula, truth_bottomFormula, truth_topFormula, truth_strictLexHeightFormula]
  exact ⟨fun ⟨meet, group, action, ⟨hb, least⟩, ⟨ht, greatest⟩, height⟩ =>
    ⟨meet, group, action, hb, least, ht, greatest, height⟩,
    fun h => ⟨h.meet, h.group, h.action, ⟨h.bottom_mem, h.least⟩,
      ⟨h.top_mem, h.greatest⟩, h.height_code⟩⟩

theorem truth_mainStageWitnessFormula {n}
    (P r μ G m inv one A b t height C D rD B R N f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainStageWitnessFormula P r μ G m inv one A b t height C D rD B R N f) env ↔
      MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) ∧
      env B = ZFSet.prod (env C) (env D) ∧
      env R = relationImage (env P) (env B) (env height) ∧
      InjectionCode (env R) (env N) (env f) := by
  simp only [mainStageWitnessFormula, Truth, truth_mainStageLawsFormula,
    truth_productEquationFormula, truth_imageSetFormula, truth_injectionFormula]

theorem realize_mainStageWitnessFormula (M : TransitiveGround.{u}) {n}
    (P r μ G m inv one A b t height C D rD B R N f : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets
      (mainStageWitnessFormula P r μ G m inv one A b t height C D rD B R N f).toFormula env ↔
      MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) ∧
      env B = ZFSet.prod (env C) (env D) ∧
      env R = relationImage (env P) (env B) (env height) ∧
      InjectionCode (env R) (env N) (env f) :=
  (realize_toFormula M _ env members).trans
    (truth_mainStageWitnessFormula P r μ G m inv one A b t height C D rD B R N f env)

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
  (unions : Realize M.sets SetFormula.union Fin.elim0)
  (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_mainStageValidityFormula {n}
    (P r μ G m inv one A b t height C D rD N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega) :
    Realize M.sets (mainStageValidityFormula P r μ G m inv one A b t height C D rD N) env ↔
      MainStageValidity M (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) := by
  simp only [mainStageValidityFormula, realize_ex]
  constructor
  · rintro ⟨B, hB, R, hR, f, hf, realized⟩
    have code := (BoundedFormula.realize_mainStageWitnessFormula M
      P.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ G.succ.succ.succ
      m.succ.succ.succ inv.succ.succ.succ one.succ.succ.succ A.succ.succ.succ
      b.succ.succ.succ t.succ.succ.succ height.succ.succ.succ C.succ.succ.succ
      D.succ.succ.succ rD.succ.succ.succ 2 1 N.succ.succ.succ 0
      (extend f (extend R (extend B env)))
      (Fin.cases hf (Fin.cases hR (Fin.cases hB members)))).1 realized
    change MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
      (env A) (env b) (env t) (env height) (env C) (env D) (env rD) ∧
      B = ZFSet.prod (env C) (env D) ∧
      R = relationImage (env P) B (env height) ∧ InjectionCode R (env N) f at code
    obtain ⟨laws, rfl, rfl, injection⟩ := code
    rw [omega] at injection
    exact ⟨laws, f, hf, injection⟩
  · rintro ⟨laws, f, hf, injection⟩
    let B := ZFSet.prod (env C) (env D)
    let R := relationImage (env P) B (env height)
    have hB : B ∈ M.sets := M.prod_mem pairing unions powers separation (members C) (members D)
    have hR : R ∈ M.sets := M.relationImage_mem separation (members P) hB (members height)
    refine ⟨B, hB, R, hR, f, hf, ?_⟩
    apply (BoundedFormula.realize_mainStageWitnessFormula M
      P.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ G.succ.succ.succ
      m.succ.succ.succ inv.succ.succ.succ one.succ.succ.succ A.succ.succ.succ
      b.succ.succ.succ t.succ.succ.succ height.succ.succ.succ C.succ.succ.succ
      D.succ.succ.succ rD.succ.succ.succ 2 1 N.succ.succ.succ 0
      (extend f (extend R (extend B env)))
      (Fin.cases hf (Fin.cases hR (Fin.cases hB members)))).2
    refine ⟨laws, rfl, rfl, ?_⟩
    change InjectionCode R (env N) f
    rw [omega]
    exact injection

theorem realize_validMainStageCodeFormula {n}
    (z P r μ G m inv one A b t height C D rD N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega) :
    Realize M.sets (validMainStageCodeFormula z P r μ G m inv one A b t height C D rD N) env ↔
      env z = mainStageCode (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) ∧
      MainStageValidity M (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) :=
  and_congr (BoundedFormula.realize_mainStageFormula M z P r μ G m inv one A b t height env members)
    (M.realize_mainStageValidityFormula pairing unions powers separation
      P r μ G m inv one A b t height C D rD N env members omega)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CodedMainPrefixSystems
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem stageGraph_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.stageGraph ↔ z = (run.linked i).code :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

end GroundMainPrefix

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace BoundedFormula

theorem truth_serializedChronologyTupleFormula {n} (z history T V : Fin n)
    (graphs : Fin 5 → Fin n) (W layers : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (serializedChronologyTupleFormula z history T V graphs W layers) env ↔
      env history = nonemptyTupleCode 6 (Fin.cases (env T) (Fin.cases (env V) (fun j => env (graphs j)))) ∧
        env z = serializedChronologyCode (env T) (env V) (fun j => env (graphs j)) (env W) (env layers) := by
  simp only [serializedChronologyTupleFormula, Truth, truth_nonemptyTupleFormula]
  have map2 {k : Nat} (a : Fin n) (f : Fin k → Fin n) :
      (fun j => env (Fin.cases a f j)) = Fin.cases (env a) (fun j => env (f j)) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp only [map2]
  constructor
  · rintro ⟨history, code⟩
    rw [history] at code
    exact ⟨history, code⟩
  · rintro ⟨history, code⟩
    unfold serializedChronologyCode at code
    rw [← history] at code
    exact ⟨history, code⟩

end BoundedFormula

end

section
open SetFormula
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

omit pairing unions powers separation in
theorem mem_serializedChronologyCandidates (B C D rD z : ZFSet.{u}) :
    z ∈ M.serializedChronologyCandidates B C D rD ↔
      z ∈ B ∧ ∃ T, ∃ serial : GroundSerializedChronology M T C D rD, serial.code = z := ZFSet.mem_sep

omit pairing unions powers separation in
theorem serializedChronology_code_mem_candidates {B T C D rD : ZFSet.{u}}
    (serial : GroundSerializedChronology M T C D rD) (bound : serial.code ∈ B) :
    serial.code ∈ M.serializedChronologyCandidates B C D rD :=
  (M.mem_serializedChronologyCandidates B C D rD serial.code).2 ⟨bound, T, serial, rfl⟩

end TransitiveGround

namespace BoundedFormula

theorem truth_linkedMainStageTupleFormula {n} (z a t h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (linkedMainStageTupleFormula z a t h) env ↔
      env z = linkedMainStageCode (env a) (env t) (env h) := by
  rw [linkedMainStageTupleFormula, truth_nonemptyTupleFormula]
  have map : (fun j : Fin 3 => env (Fin.cases a (Fin.cases t (fun _ => h)) j)) =
      Fin.cases (env a) (Fin.cases (env t) (fun _ => env h)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) j
  rw [map]
  rfl

theorem truth_linkedTerminalFormula {n} (t T P r μ h : Fin n) (graphs : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (linkedTerminalFormula t T P r μ h graphs) env ↔
      ordinalSetProperty (env t) ∧ env T = insert (env t) (env t) ∧
      ZFSet.pair (env t) (env P) ∈ env (graphs 0) ∧
      ZFSet.pair (env t) (env r) ∈ env (graphs 1) ∧
      ZFSet.pair (env t) (env μ) ∈ env (graphs 2) ∧
      ZFSet.pair (env t) (env h) ∈ env (graphs 4) := by
  simp only [linkedTerminalFormula, Truth, truth_ordinalFormula, truth_successorFormula,
    truth_pairMembershipFormula, ← ordinalSetProperty_iff]
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_linkedMainStageRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N z : Fin n)
    (f : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainStageRawFormula K Labels C D rD N z f) env ↔
      LinkedMainStageRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N) (env z)
        (fun j => env (f j)) := by
  have outer := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_linkedMainStageTupleFormula z (f 22) (f 11) (f 23) env)
  have stage := M.realize_validMainStageCodeFormula pairing unions powers separation
    (f 22) (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) C D rD N env members omega
  have tuple := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_serializedChronologyTupleFormula (f 23) (f 21) (f 12) (f 13)
      (linkedChronologyGraphs f) (f 19) (f 20) env)
  have serial := M.realize_serializedChronologyFormula pairing unions powers separation
    (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20) env members
  have terminal := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_linkedTerminalFormula (f 11) (f 12) (f 0) (f 1) (f 2) (f 10)
      (linkedChronologyGraphs f) env)
  have invariant := M.realize_linkedMainInvariantFormula pairing unions powers separation collection
    K Labels C D (f 0) (f 3) (f 11) (f 23) env members ordinal
  have map : (fun j => env (linkedChronologyGraphs f j)) = linkedChronologyGraphs (fun j => env (f j)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  change (Realize M.sets (BoundedFormula.linkedMainStageTupleFormula z (f 22) (f 11) (f 23)).toFormula env ∧
    Realize M.sets (validMainStageCodeFormula (f 22) (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
      (f 7) (f 8) (f 9) (f 10) C D rD N) env ∧
    Realize M.sets (BoundedFormula.serializedChronologyTupleFormula (f 23) (f 21) (f 12) (f 13)
      (linkedChronologyGraphs f) (f 19) (f 20)).toFormula env ∧
    Realize M.sets (serializedChronologyFormula (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20)) env ∧
    Realize M.sets (BoundedFormula.linkedTerminalFormula (f 11) (f 12) (f 0) (f 1) (f 2) (f 10)
      (linkedChronologyGraphs f)).toFormula env ∧
    Realize M.sets (linkedMainInvariantFormula K Labels C D (f 0) (f 3) (f 11) (f 23)) env) ↔ _
  rw [outer, stage, tuple, serial, terminal, invariant, map]
  simp only [LinkedMainStageRawCode, and_assoc]
  rfl

end TransitiveGround

end

section
open SetFormula
universe u

namespace LinkedMainStageRawCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N z : ZFSet.{u}} {f : Fin 24 → ZFSet.{u}}

theorem exists_linked
    (raw : LinkedMainStageRawCode M K Labels C D rD N z f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : ∀ j, f j ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (omega : N = ZFSet.omega) :
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z := by
  obtain ⟨outer, stageEq, valid, _, serialEq, code, ordinal, domain, eP, er, eμ, eh, inv⟩ := raw
  let stage := GroundMainStage.ofValidity pairing unions powers separation
    (ground 0) (ground 1) (ground 2) (ground 3) (ground 4) (ground 5) (ground 7) (ground 10) hC hD hrD valid
  have code' : SerializedChronologyCode (insert (f 11) (f 11)) (f 13) C D rD N
      (linkedChronologyGraphs f) (f 19) (f 20) := domain ▸ code
  have graphsGround : ∀ j, linkedChronologyGraphs f j ∈ M.sets :=
    Fin.cases (ground 14) (Fin.cases (ground 15) (Fin.cases (ground 16)
      (Fin.cases (ground 17) (fun _ => ground 18))))
  let serial := code'.toGround (domain ▸ ground 12) (ground 13) graphsGround (ground 19) (ground 20) omega
  let main : GroundChronologicalMainStage M C D rD :=
    { stage := stage
      cutoff := f 11
      cutoff_ground := ground 11
      cutoff_ordinal := ordinal
      history := serial.toHistory
      carrier_eq := serial.fields.value_eq_of_entry 0 eP
      order_eq := serial.fields.value_eq_of_entry 1 er
      meet_eq := serial.fields.value_eq_of_entry 2 eμ
      height_eq := serial.fields.value_eq_of_entry 4 eh }
  have serialCode : serial.code = f 23 := by
    change serializedChronologyCode (insert (f 11) (f 11)) (f 13) (linkedChronologyGraphs f) (f 19) (f 20) = f 23
    rw [← domain]
    exact serialEq.symm
  obtain ⟨ps, gs, ls, pr, gr, lr, tm, cr, dr, sr⟩ := inv
  let linked : GroundLinkedMainStage M K Labels C D rD :=
    { main := main
      serial := serial
      agreement := fun j _ _ => Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j
      invariant := ⟨ps, gs, ls, pr, gr, lr, tm, cr, dr⟩
      serial_rank := serialCode ▸ sr }
  refine ⟨linked, ?_⟩
  change linkedMainStageCode stage.code (f 11) serial.code = z
  have scode : stage.code = f 22 := stageEq.symm
  rw [scode, serialCode]
  exact outer.symm

end LinkedMainStageRawCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem rawFields_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    ∀ j, linked.rawFields j ∈ M.sets :=
  (Fin.cases (linked.main.stage.carrier_ground) (Fin.cases (linked.main.stage.order_ground) (Fin.cases (linked.main.stage.meet_ground) (Fin.cases (linked.main.stage.actors_ground) (Fin.cases (linked.main.stage.multiplication_ground) (Fin.cases (linked.main.stage.inverse_ground) (Fin.cases (linked.main.stage.identity_ground) (Fin.cases (linked.main.stage.action_ground) (Fin.cases (linked.main.stage.bottom_ground) (Fin.cases (linked.main.stage.top_ground) (Fin.cases (linked.main.stage.height_ground) (Fin.cases (linked.main.cutoff_ground) (Fin.cases (linked.serial.fields.time_ground) (Fin.cases (linked.serial.fields.bound_ground) (Fin.cases (linked.serial.fields.graph_ground 0) (Fin.cases (linked.serial.fields.graph_ground 1) (Fin.cases (linked.serial.fields.graph_ground 2) (Fin.cases (linked.serial.fields.graph_ground 3) (Fin.cases (linked.serial.fields.graph_ground 4) (Fin.cases (linked.serial.layer_bound_ground) (Fin.cases (linked.serial.layers_ground) (Fin.cases (linked.serial.fields.code_ground pairing) (Fin.cases (linked.main.stage.code_mem pairing) (fun _ => linked.serial.code_ground pairing))))))))))))))))))))))))

end GroundLinkedMainStage

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedMainTransitionRawCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_chronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs) env ↔
      env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ) (env heightP) (env heightQ) (env points) (env actors) ∧
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j)) := by
  change (Truth (validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors) env ∧
    Truth (chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff sourceBirth targetBirth
      sourceGraphs targetGraphs) env) ↔ _
  rw [truth_validMainTransitionCodeFormula]
  constructor
  · rintro ⟨⟨encoded, laws⟩, chronological⟩
    exact ⟨encoded, laws, (truth_chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs env laws.point_embedding.injection.function.1).1 chronological⟩
  · rintro ⟨encoded, laws, chronological⟩
    exact ⟨⟨encoded, laws⟩, (truth_chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs env laws.point_embedding.injection.function.1).2 chronological⟩

theorem truth_coveredChronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (coveredChronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs) env ↔
      (env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ) (env heightP) (env heightQ) (env points) (env actors) ∧
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j))) ∧
      OldBirthFiberCoverageCode (env P) (env points) (env targetBirth) (env sourceCutoff) := by
  simp only [coveredChronologicalMainTransitionFormula, Truth,
    truth_chronologicalMainTransitionFormula, truth_oldBirthFiberCoverageFormula]

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_linkedTransitionLawsFormula {n} (z points actors sourceBirth targetBirth : Fin n)
    (f g : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (linkedTransitionLawsFormula z points actors sourceBirth targetBirth f g) env ↔
      LinkedTransitionLawsCode (env z) (env points) (env actors) (env sourceBirth) (env targetBirth)
        (fun j => env (f j)) (fun j => env (g j)) := by
  have map (h : Fin 24 → Fin n) : (fun j => env (linkedChronologyGraphs h j)) =
      linkedChronologyGraphs (fun j => env (h j)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  simp only [linkedTransitionLawsFormula, Truth, truth_pairMembershipFormula,
    truth_coveredChronologicalMainTransitionFormula, map, LinkedTransitionLawsCode]

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_linkedMainTransitionRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : Fin n)
    (source target : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainTransitionRawFormula K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth source target) env ↔
      LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env sourceCode) (env targetCode) (env z) (env points) (env actors) (env sourceBirth) (env targetBirth)
          (fun j => env (source j)) (fun j => env (target j)) := by
  have first := M.realize_linkedMainStageRawFormula pairing unions powers separation collection
    K Labels C D rD N sourceCode source env members omega ordinal
  have second := M.realize_linkedMainStageRawFormula pairing unions powers separation collection
    K Labels C D rD N targetCode target env members omega ordinal
  have laws := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_linkedTransitionLawsFormula z points actors sourceBirth targetBirth source target env)
  exact and_congr first (and_congr second laws)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixFieldFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem linkedCode_rank_lt_code (i : I) : ZFSet.rank (run.linked i).code < ZFSet.rank run.code :=
  (ZFSet.rank_lt_of_mem (pair_second_mem_doubleUnion ((run.stageGraph_entry i _).2 rfl))).trans_le
    (((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _)).trans run.stageGraph_rank_le_code)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mainPrefixCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {T S E : ZFSet.{u}} (hT : T ∈ M.sets) (hS : S ∈ M.sets) (hE : E ∈ M.sets) :
    mainPrefixCode T S E ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _ (Fin.cases hT (Fin.cases hS (fun _ => hE)))

theorem mainPrefixCode_fields_mem {T S E : ZFSet.{u}} (ground : mainPrefixCode T S E ∈ M.sets) :
    T ∈ M.sets ∧ S ∈ M.sets ∧ E ∈ M.sets := by
  let fields : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
  have encoded : nonemptyTupleCode 2 fields ∈ M.sets := ground
  have each := M.nonemptyTupleCode_field_mem 2 fields encoded
  exact ⟨each 0, each 1, each 2⟩

end TransitiveGround

namespace BoundedFormula

theorem truth_mainPrefixTupleFormula {n} (z T S E : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainPrefixTupleFormula z T S E) env ↔ env z = mainPrefixCode (env T) (env S) (env E) := by
  rw [mainPrefixTupleFormula, truth_nonemptyTupleFormula]
  have map : (fun j : Fin 3 => env (Fin.cases T (Fin.cases S (fun _ => E)) j)) =
      Fin.cases (env T) (Fin.cases (env S) (fun _ => env E)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) j
  rw [map]
  rfl

theorem realize_mainPrefixTupleFormula (M : TransitiveGround.{u}) {n}
    (z T S E : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixTupleFormula z T S E).toFormula env ↔
      env z = mainPrefixCode (env T) (env S) (env E) :=
  (realize_toFormula M _ env members).trans (truth_mainPrefixTupleFormula z T S E env)

end BoundedFormula

end

section
universe u

theorem MainPrefixExtends.refl (T S E : ZFSet.{u}) :
    MainPrefixExtends (mainPrefixCode T S E) (mainPrefixCode T S E) :=
  mainPrefixExtends_iff.2 ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem MainPrefixExtends.trans {a b c : ZFSet.{u}}
    (first : MainPrefixExtends a b) (second : MainPrefixExtends b c) : MainPrefixExtends a c := by
  obtain ⟨T, S, E, U, F, G, rfl, hb, indices, stages, transitions⟩ := first
  obtain ⟨U', F', G', V, H, J, hb', rfl, indices', stages', transitions'⟩ := second
  obtain ⟨rfl, rfl, rfl⟩ := mainPrefixCode_inj.1 (hb.symm.trans hb')
  exact mainPrefixExtends_iff.2 ⟨fun _ h => indices' (indices h),
    fun _ h => stages' (stages h), fun _ h => transitions' (transitions h)⟩

end

namespace MainPrefixGraphCode
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD T S E : ZFSet.{u}}
variable (raw : MainPrefixGraphCode M K Labels C D rD T S E)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hT : T ∈ M.sets) (hS : S ∈ M.sets) (hE : E ∈ M.sets)

theorem decodedPrefix_indices :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedPrefix pairing unions powers separation hT hS hE).indices = T :=
  ordinalMainIndex_key_range T

theorem decodedPrefix_stageGraph :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedPrefix pairing unions powers separation hT hS hE).stageGraph = S :=
  familyCodeGraph_eq_of_entries raw.stages _ _ (ordinalMainIndex_key_range T) raw.decodedLinked_entry

theorem decodedPrefix_transitionGraph :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedPrefix pairing unions powers separation hT hS hE).transitionGraph = E := by
  let := ordinalMainIndexPreorder raw.ordinal
  exact familyCodeGraph_eq_of_entries raw.transitions _ _ (ordinalMainTransitionIndex_range raw.ordinal)
    (fun p => raw.decodedTransition_entry p.val.1 p.val.2 p.property)

theorem decodedPrefix_code :
    letI := ordinalMainIndexPreorder raw.ordinal
    (raw.decodedPrefix pairing unions powers separation hT hS hE).code =
      nonemptyTupleCode 2 (Fin.cases T (Fin.cases S (fun _ => E))) := by
  let := ordinalMainIndexPreorder raw.ordinal
  unfold GroundMainPrefix.code
  rw [raw.decodedPrefix_indices, raw.decodedPrefix_stageGraph, raw.decodedPrefix_transitionGraph]

end MainPrefixGraphCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem serialFieldFamily_rank_le_code (j : Fin 5) :
    ZFSet.rank (run.serialFieldFamily j) ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono run.key _ (fun i => (run.linked i).code) ?_).trans
    run.stageGraph_rank_le_code
  intro i
  have serialBound : ZFSet.rank (run.linked i).serial.code ≤ ZFSet.rank (run.linked i).code := by
    simpa only [GroundLinkedMainStage.code, linkedMainStageCode, Fin.cases_zero, Fin.cases_succ] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases (run.linked i).main.stage.code
        (Fin.cases (run.linked i).main.cutoff (fun _ => (run.linked i).serial.code))) (0 : Fin 1).succ.succ)
  exact ((run.linked i).serial.fieldGraph_rank_le_code j).trans serialBound

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem cutoffSuccessorFamily_rank_le_code :
    ZFSet.rank run.cutoffSuccessorFamily ≤ ZFSet.rank run.code := by
  apply (familyCodeGraph_rank_mono run.key _ (fun i => (run.linked i).code) ?_).trans
    run.stageGraph_rank_le_code
  intro i
  have serialBound : ZFSet.rank (run.linked i).serial.code ≤ ZFSet.rank (run.linked i).code := by
    simpa only [GroundLinkedMainStage.code, linkedMainStageCode, Fin.cases_zero, Fin.cases_succ] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases (run.linked i).main.stage.code
        (Fin.cases (run.linked i).main.cutoff (fun _ => (run.linked i).serial.code))) (0 : Fin 1).succ.succ)
  simpa only [run.linked_main] using (run.linked i).serial.time_rank_le_code.trans serialBound

theorem cutoffLimit_rank_le_code : ZFSet.rank run.cutoffLimit ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueUnion_rank_le run.key _).trans run.cutoffSuccessorFamily_rank_le_code

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing
universe u v

namespace MainPrefixLimitStepCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N old next : ZFSet.{u}}
variable (code : MainPrefixLimitStepCode M K Labels C D rD N old next)
include code

theorem extension : MainPrefixExtends old next := by
  obtain ⟨w, _, raw⟩ := code
  exact raw.2.2.2.1

theorem indices_successor {T S E T' S' E' : ZFSet.{u}}
    (oldCode : old = mainPrefixCode T S E) (nextCode : next = mainPrefixCode T' S' E') :
    T' = insert T T := by
  obtain ⟨w, _, raw⟩ := code
  have oldFields := mainPrefixCode_inj.1 (oldCode.symm.trans raw.2.1)
  have nextFields := mainPrefixCode_inj.1 (nextCode.symm.trans raw.2.2.1)
  rw [nextFields.1, raw.1, ← oldFields.1]

end MainPrefixLimitStepCode

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskCapFamilyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_codedInsertionProfileFormula {n} (L r μ c E K F : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedInsertionProfileFormula L r μ c E K F) env ↔
      CodedInsertionProfile (env L) (env r) (env μ) (env c) (env E) (env K) (env F) := by
  simp only [codedInsertionProfileFormula, Truth, truth_imp, truth_exMem,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

theorem truth_codedCapProfileFormula {n} (L r μ c E K F : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedCapProfileFormula L r μ c E K F) env ↔
      CodedCapProfile (env L) (env r) (env μ) (env c) (env E) (env K) (env F) := by
  simp only [codedCapProfileFormula, Truth, truth_subsetFormula, truth_exMem,
    truth_codedInsertionProfileFormula, truth_pairMembershipFormula, and_true]
  constructor
  · rintro ⟨hc, hE, hK, subset, nonempty, profile, lower, strict, separated⟩
    exact ⟨hc, hE, hK, subset, nonempty, profile, lower, strict, separated⟩
  · intro code
    exact ⟨code.target_mem, code.separator_mem, code.cap_mem, code.filter_subset,
      code.nonempty, code.profile, code.target_below_cap, code.cap_not_below_target,
      code.separator_not_below_cap⟩

theorem truth_imageProfilePositiveFormula {n} (F Q e R x : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (imageProfilePositiveFormula F Q e R x) env ↔
      ∃ f ∈ relationImage (env F) (env Q) (env e), ZFSet.pair f (env x) ∈ env R := by
  simp only [imageProfilePositiveFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  constructor
  · rintro ⟨y, hy, ⟨f, hf, entry⟩, lower⟩
    exact ⟨y, (mem_relationImage _ _ _ _).2 ⟨hy, f, hf, entry⟩, lower⟩
  · rintro ⟨y, hy, lower⟩
    obtain ⟨hy, f, hf, entry⟩ := (mem_relationImage _ _ _ _).1 hy
    exact ⟨y, hy, ⟨f, hf, entry⟩, lower⟩

theorem truth_imageInsertionProfileFormula {n} (Q R ν c E K F e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (imageInsertionProfileFormula Q R ν c E K F e) env ↔
      CodedInsertionProfile (env Q) (env R) (env ν) (env c) (env E) (env K)
        (relationImage (env F) (env Q) (env e)) := by
  simp only [imageInsertionProfileFormula, Truth, truth_imp, truth_imageProfilePositiveFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

theorem truth_imageCapProfileFormula {n} (Q R ν c E K F e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (imageCapProfileFormula Q R ν c E K F e) env ↔
      CodedCapProfile (env Q) (env R) (env ν) (env c) (env E) (env K)
        (relationImage (env F) (env Q) (env e)) := by
  simp only [imageCapProfileFormula, Truth, truth_exMem, truth_pairMembershipFormula,
    truth_imageInsertionProfileFormula]
  constructor
  · rintro ⟨hc, hE, hK, ⟨y, hy, f, hf, entry⟩, profile, lower, strict, separated⟩
    exact ⟨hc, hE, hK, fun _ h => ((mem_relationImage _ _ _ _).1 h).1,
      ⟨y, (mem_relationImage _ _ _ _).2 ⟨hy, f, hf, entry⟩⟩,
      profile, lower, strict, separated⟩
  · intro code
    obtain ⟨y, hy⟩ := code.nonempty
    obtain ⟨hy, f, hf, entry⟩ := (mem_relationImage _ _ _ _).1 hy
    exact ⟨code.target_mem, code.separator_mem, code.cap_mem, ⟨y, hy, f, hf, entry⟩,
      code.profile, code.target_below_cap, code.cap_not_below_target,
      code.separator_not_below_cap⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

theorem truth_oldProfilePreservationFormula {n} (P r μ Q R ν e Filters : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (oldProfilePreservationFormula P r μ Q R ν e Filters) env ↔
      OldProfilePreservationCode (env P) (env r) (env μ) (env Q) (env R) (env ν)
        (env e) (env Filters) := by
  simp only [oldProfilePreservationFormula, Truth, truth_imp, truth_codedCapProfileFormula,
    truth_imageCapProfileFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace BoundedFormula

theorem truth_taskCapProfilesFormula {n}
    (I P Q R ν e Targets Separators Filters Families Caps : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (taskCapProfilesFormula I P Q R ν e Targets Separators Filters Families Caps) env ↔
      TaskCapProfilesCode (env I) (env P) (env Q) (env R) (env ν) (env e) (env Targets)
        (env Separators) (env Filters) (env Families) (env Caps) := by
  simp only [taskCapProfilesFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_imageCapProfileFormula]
  rfl

theorem truth_commonTargetCapMeetFormula {n} (I P Q ν e Targets Caps : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (commonTargetCapMeetFormula I P Q ν e Targets Caps) env ↔
      CommonTargetCapMeetCode (env I) (env P) (env Q) (env ν) (env e) (env Targets) (env Caps) := by
  simp only [commonTargetCapMeetFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

theorem truth_taskCapFamilyFormula {n}
    (I P Q R ν e Targets Separators Filters Families Caps : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (taskCapFamilyFormula I P Q R ν e Targets Separators Filters Families Caps) env ↔
      TaskCapFamilyCode (env I) (env P) (env Q) (env R) (env ν) (env e) (env Targets)
        (env Separators) (env Filters) (env Families) (env Caps) := by
  simp only [taskCapFamilyFormula, Truth, truth_functionFormula, truth_taskCapProfilesFormula,
    truth_commonTargetCapMeetFormula]
  exact ⟨fun ⟨f, p, c⟩ => ⟨f, p, c⟩, fun code => ⟨code.function, code.profiles, code.common_target⟩⟩

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalSeparatedActors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace GroundMainFinalGeometry
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem identity_ground : geometry.identity ∈ M.sets :=
  M.transitive geometry.actors_ground geometry.group_code.identity_mem

theorem bottom_ground : geometry.bottom ∈ M.sets :=
  M.transitive geometry.carrier_ground geometry.bottom_mem

theorem fields_ground : ∀ j, geometry.fields j ∈ M.sets :=
  Fin.cases geometry.carrier_ground (Fin.cases geometry.order_ground (Fin.cases geometry.meet_ground
    (Fin.cases geometry.actors_ground (Fin.cases geometry.multiplication_ground (Fin.cases geometry.inverse_ground
      (Fin.cases geometry.identity_ground (Fin.cases geometry.action_ground (Fin.cases geometry.bottom_ground
        (Fin.cases geometry.height_ground (Fin.cases geometry.birth_ground (fun _ => geometry.times_ground)))))))))))

theorem code_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    geometry.code ∈ M.sets := M.nonemptyTupleCode_mem pairing 11 geometry.fields geometry.fields_ground

end GroundMainFinalGeometry

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedValueLifts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem indexedValueLift_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (T U F J : ZFSet.{u}) {Q V : ZFSet.{u}}
    (hq : ZFSet.rank Q < o) (hv : ZFSet.rank V < o) :
    ZFSet.rank (indexedValueLift T U Q V F J) < o :=
  (ZFSet.rank_mono (indexedValueLift_subset T U Q V F J)).trans_lt (rank_product_lt limit hq hv)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitGroupLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem indexedClassInclusion_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {U L : ZFSet.{u}} (E i : ZFSet.{u})
    (points : ZFSet.rank U < o) (labels : ZFSet.rank L < o) :
    ZFSet.rank (indexedClassInclusion U L E i) < o :=
  (ZFSet.rank_mono (indexedRelationSection_subset U (equivalenceClasses L E)
    (equivalenceClassifier L E) i)).trans_lt
    (rank_product_lt limit points (equivalenceClasses_rank_lt limit E labels))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedClassInclusions_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {T U L : ZFSet.{u}} (E : ZFSet.{u}) (indices : ZFSet.rank T < o)
    (points : ZFSet.rank U < o) (labels : ZFSet.rank L < o) :
    ZFSet.rank (M.indexedClassInclusions T U L E) < o :=
  (ZFSet.rank_mono
    (show M.indexedClassInclusions T U L E ⊆
        ZFSet.prod T (M.groundRelations U (equivalenceClasses L E))
      from fun _ hz => by
        unfold indexedClassInclusions indexedRelationSections at hz
        exact (ZFSet.mem_sep.1 hz).1)).trans_lt
    (rank_product_lt limit indices
      (M.groundRelations_rank_lt limit points (equivalenceClasses_rank_lt limit E labels)))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitBottom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix

section
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank run.code < o)
include limit rank

theorem limitPointMap_rank_lt (i : I) : ZFSet.rank (run.limitPointMap i) < o :=
  indexedClassInclusion_rank_lt limit run.limitPointRelation (run.key i)
    (run.carrierUnion_rank_le_code.trans_lt rank) (run.limitPointLabels_rank_lt limit rank)

theorem limitPointInclusions_rank_lt : ZFSet.rank run.limitPointInclusions < o :=
  M.indexedClassInclusions_rank_lt limit run.limitPointRelation
    (run.indices_rank_le_code.trans_lt rank) (run.carrierUnion_rank_le_code.trans_lt rank)
    (run.limitPointLabels_rank_lt limit rank)

theorem limitActorMap_rank_lt (i : I) : ZFSet.rank (run.limitActorMap i) < o :=
  indexedClassInclusion_rank_lt limit run.limitActorRelation (run.key i)
    (run.actorUnion_rank_le_code.trans_lt rank) (run.limitActorLabels_rank_lt limit rank)

theorem limitActorInclusions_rank_lt : ZFSet.rank run.limitActorInclusions < o :=
  M.indexedClassInclusions_rank_lt limit run.limitActorRelation
    (run.indices_rank_le_code.trans_lt rank) (run.actorUnion_rank_le_code.trans_lt rank)
    (run.limitActorLabels_rank_lt limit rank)

end

section
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitMultiplication_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitMultiplication < o :=
  indexedBinaryLift_rank_lt limit _ _ _ _ (run.limitActors_rank_lt limit rank)

theorem limitInverse_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitInverse < o :=
  indexedRelationLift_rank_lt limit _ _ _ _ (run.limitActors_rank_lt limit rank)

end

open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitOrder_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitOrder < o :=
  indexedRelationLift_rank_lt limit _ _ _ _ (run.limitPoints_rank_lt limit rank)

theorem limitMeetGraph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitMeetGraph < o :=
  indexedBinaryLift_rank_lt limit _ _ _ _ (run.limitPoints_rank_lt limit rank)

theorem limitBottom_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) (i : I) : ZFSet.rank (run.limitBottom i) < o :=
  (ZFSet.rank_lt_of_mem (run.limitBottom_mem i)).trans (run.limitPoints_rank_lt limit rank)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainPrefixLimitActionLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitAction_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitAction < o :=
  indexedMixedBinaryLift_rank_lt limit _ _ _ _ _ _
    (run.limitActors_rank_lt limit rank) (run.limitPoints_rank_lt limit rank)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GrowthLayerWitnessRestrictions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace CopyEmbeddingFamilyCode

theorem restrict_sources_iff
    {Qs rs μs L r μ t I Indices Maps S : ZFSet.{u}} (before : t ⊆ S) :
    CopyEmbeddingFamilyCode (graphRestriction S Qs) (graphRestriction S rs)
      (graphRestriction S μs) L r μ t I Indices Maps ↔
    CopyEmbeddingFamilyCode Qs rs μs L r μ t I Indices Maps := by
  constructor
  · intro code i hi s hs e P R V index map qField rField mField
    exact code i hi s hs e P R V index map
      (pair_mem_graphRestriction.2 ⟨qField, before hs⟩)
      (pair_mem_graphRestriction.2 ⟨rField, before hs⟩)
      (pair_mem_graphRestriction.2 ⟨mField, before hs⟩)
  · intro code i hi s hs e P R V index map qField rField mField
    exact code i hi s hs e P R V index map
      (pair_mem_graphRestriction.1 qField).1 (pair_mem_graphRestriction.1 rField).1
      (pair_mem_graphRestriction.1 mField).1

end CopyEmbeddingFamilyCode

namespace CopyImageCoverCode

theorem restrict_sources_iff
    {Qs L t I parts Indices Maps S : ZFSet.{u}} (before : t ⊆ S) :
    CopyImageCoverCode (graphRestriction S Qs) L t I parts Indices Maps ↔
      CopyImageCoverCode Qs L t I parts Indices Maps := by
  constructor
  · intro code i hi s hs e P x hx index map qField part
    exact code i hi s hs e P x hx index map (pair_mem_graphRestriction.2 ⟨qField, before hs⟩) part
  · intro code i hi s hs e P x hx index map qField part
    exact code i hi s hs e P x hx index map (pair_mem_graphRestriction.1 qField).1 part

end CopyImageCoverCode

namespace ComponentImageCoverCode

theorem restrict_sources_iff
    {Qs L t I Components Indices Maps S : ZFSet.{u}} (before : t ⊆ S) :
    ComponentImageCoverCode (graphRestriction S Qs) L t I Components Indices Maps ↔
      ComponentImageCoverCode Qs L t I Components Indices Maps := by
  constructor
  · intro code i hi s hs e P x hx index map qField component
    exact code i hi s hs e P x hx index map
      (pair_mem_graphRestriction.2 ⟨qField, before hs⟩) component
  · intro code i hi s hs e P x hx index map qField component
    exact code i hi s hs e P x hx index map (pair_mem_graphRestriction.1 qField).1 component

end ComponentImageCoverCode

namespace CopyLayerCode

theorem restrict_sources_iff
    {Qs rs μs L r μ birth t I parts Indices Maps W N injection S : ZFSet.{u}}
    (before : t ⊆ S) :
    CopyLayerCode (graphRestriction S Qs) (graphRestriction S rs) (graphRestriction S μs)
      L r μ birth t I parts Indices Maps W N injection ↔
    CopyLayerCode Qs rs μs L r μ birth t I parts Indices Maps W N injection := by
  constructor
  · intro code
    exact ⟨code.small, code.indices, code.maps,
      (CopyEmbeddingFamilyCode.restrict_sources_iff before).1 code.embedding,
      code.cover, (CopyImageCoverCode.restrict_sources_iff before).1 code.inCopy⟩
  · intro code
    exact ⟨code.small, code.indices, code.maps,
      (CopyEmbeddingFamilyCode.restrict_sources_iff before).2 code.embedding,
      code.cover, (CopyImageCoverCode.restrict_sources_iff before).2 code.inCopy⟩

end CopyLayerCode

namespace SeparatedLayerCode

theorem restrict_sources_iff
    {Qs rs μs L r μ birth t I Indices Maps W Components F S : ZFSet.{u}}
    (before : t ⊆ S) :
    SeparatedLayerCode (graphRestriction S Qs) (graphRestriction S rs) (graphRestriction S μs)
      L r μ birth t I Indices Maps W Components F ↔
    SeparatedLayerCode Qs rs μs L r μ birth t I Indices Maps W Components F := by
  constructor
  · intro code
    exact ⟨code.indices, code.maps, code.fiber, code.components,
      (CopyEmbeddingFamilyCode.restrict_sources_iff before).1 code.embedding,
      (ComponentImageCoverCode.restrict_sources_iff before).1 code.cover, code.separated⟩
  · intro code
    exact ⟨code.indices, code.maps, code.fiber, code.components,
      (CopyEmbeddingFamilyCode.restrict_sources_iff before).2 code.embedding,
      (ComponentImageCoverCode.restrict_sources_iff before).2 code.cover, code.separated⟩

end SeparatedLayerCode

namespace GrowthLayerWitnessCode

theorem restrict_sources_iff {Qs rs μs L r μ birth t N z S : ZFSet.{u}}
    (before : t ⊆ S) :
    GrowthLayerWitnessCode (graphRestriction S Qs) (graphRestriction S rs) (graphRestriction S μs)
      L r μ birth t N z ↔ GrowthLayerWitnessCode Qs rs μs L r μ birth t N z := by
  simp only [GrowthLayerWitnessCode, CopyLayerCode.restrict_sources_iff before,
    SeparatedLayerCode.restrict_sources_iff before]

end GrowthLayerWitnessCode
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLayerSourceCongruence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem graphRestriction_eq_of_entries {S f g : ZFSet.{u}}
    (entries : ∀ s ∈ S, ∀ y, ZFSet.pair s y ∈ f ↔ ZFSet.pair s y ∈ g) :
    graphRestriction S f = graphRestriction S g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨s, hs, y, rfl, entry⟩ := mem_graphRestriction.1 member
    exact pair_mem_graphRestriction.2 ⟨(entries s hs y).1 entry, hs⟩
  · intro member
    obtain ⟨s, hs, y, rfl, entry⟩ := mem_graphRestriction.1 member
    exact pair_mem_graphRestriction.2 ⟨(entries s hs y).2 entry, hs⟩

namespace GrowthLayerWitnessCode

theorem congr_sources_below_iff
    {Qs rs μs Qs' rs' μs' L r μ birth t N z : ZFSet.{u}}
    (spaces : graphRestriction t Qs = graphRestriction t Qs')
    (orders : graphRestriction t rs = graphRestriction t rs')
    (meets : graphRestriction t μs = graphRestriction t μs') :
    GrowthLayerWitnessCode Qs rs μs L r μ birth t N z ↔
      GrowthLayerWitnessCode Qs' rs' μs' L r μ birth t N z := by
  have self : t ⊆ t := fun _ h => h
  rw [← restrict_sources_iff self, ← restrict_sources_iff (Qs := Qs') self]
  rw [spaces, orders, meets]

theorem congr_sources_below
    {Qs rs μs Qs' rs' μs' L r μ birth t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs L r μ birth t N z)
    (spaces : graphRestriction t Qs = graphRestriction t Qs')
    (orders : graphRestriction t rs = graphRestriction t rs')
    (meets : graphRestriction t μs = graphRestriction t μs') :
    GrowthLayerWitnessCode Qs' rs' μs' L r μ birth t N z :=
  (congr_sources_below_iff spaces orders meets).1 code

theorem congr_source_entries
    {Qs rs μs Qs' rs' μs' L r μ birth t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs L r μ birth t N z)
    (spaces : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ Qs ↔ ZFSet.pair s y ∈ Qs')
    (orders : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ rs ↔ ZFSet.pair s y ∈ rs')
    (meets : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ μs ↔ ZFSet.pair s y ∈ μs') :
    GrowthLayerWitnessCode Qs' rs' μs' L r μ birth t N z :=
  code.congr_sources_below (graphRestriction_eq_of_entries spaces)
    (graphRestriction_eq_of_entries orders) (graphRestriction_eq_of_entries meets)

end GrowthLayerWitnessCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainPrefixPriorLayerWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem prior_raw_witness_rank_lt (i : I) {s t Qs rs μs : ZFSet.{u}}
    (cutoff : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff)
    (before : t = s ∨ t ∈ s)
    (spaces : ∀ a ∈ t, ∀ y, ZFSet.pair a y ∈ (run.linked i).serial.fields.graph 0 ↔
      ZFSet.pair a y ∈ Qs)
    (orders : ∀ a ∈ t, ∀ y, ZFSet.pair a y ∈ (run.linked i).serial.fields.graph 1 ↔
      ZFSet.pair a y ∈ rs)
    (meets : ∀ a ∈ t, ∀ y, ZFSet.pair a y ∈ (run.linked i).serial.fields.graph 2 ↔
      ZFSet.pair a y ∈ μs)
    {o : Ordinal.{u}} (rank : ZFSet.rank run.code < o) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode Qs rs μs
      ((run.diagram.stage i).history.space s) ((run.diagram.stage i).history.order s)
      ((run.diagram.stage i).history.meetGraph s) ((run.diagram.stage i).history.birth s)
      t ZFSet.omega z ∧ ZFSet.rank z < o := by
  have hs : s ∈ insert (run.linked i).main.cutoff (run.linked i).main.cutoff := by
    simpa only [run.linked_main, ZFSet.mem_insert_iff] using cutoff
  have ht : t ∈ insert (run.linked i).main.cutoff (run.linked i).main.cutoff := by
    rcases before with rfl | earlier
    · exact hs
    · exact (run.linked i).serial.ordinal.1 s hs t earlier
  have raw := (run.linked i).serial.layer_code s hs t ht before _
    ((run.linked i).serial.layerWitness_entry hs ht before)
  have values (j : Fin 5) : (run.linked i).serial.fields.value j s =
      (run.diagram.stage i).history.fieldValue j s := by
    exact ((run.linked i).agreement j s hs).trans
      (congrArg (fun stage : GroundChronologicalMainStage M C D rD =>
        stage.history.fieldValue j s) (run.linked_main i))
  rw [values 0, values 1, values 2, values 3] at raw
  have serialBound : ZFSet.rank (run.linked i).serial.code ≤ ZFSet.rank (run.linked i).code := by
    simpa only [GroundLinkedMainStage.code, linkedMainStageCode, Fin.cases_succ] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases (run.linked i).main.stage.code
        (Fin.cases (run.linked i).main.cutoff (fun _ => (run.linked i).serial.code)))
        (0 : Fin 1).succ.succ)
  have serialRank : ZFSet.rank (run.linked i).serial.code < o :=
    serialBound.trans_lt ((run.linkedCode_rank_lt_code i).trans rank)
  exact ⟨(run.linked i).serial.layerWitness s t, (run.linked i).serial.layerWitness_ground s t,
    raw.congr_source_entries spaces orders meets,
    ((run.linked i).serial.layerWitness_rank_lt_code hs ht before).trans serialRank⟩

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyLayerRelation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem truth_chronologyLayerPairLookupFormula {n} (p T Qs rs μs births : Fin n)
    (v : Fin 6 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyLayerPairLookupFormula p T Qs rs μs births v) env ↔
      env (v 0) ∈ env T ∧ env (v 1) ∈ env T ∧
      (env (v 1) = env (v 0) ∨ env (v 1) ∈ env (v 0)) ∧
      env p = ZFSet.pair (env (v 0)) (env (v 1)) ∧
      ZFSet.pair (env (v 0)) (env (v 2)) ∈ env Qs ∧
      ZFSet.pair (env (v 0)) (env (v 3)) ∈ env rs ∧
      ZFSet.pair (env (v 0)) (env (v 4)) ∈ env μs ∧
      ZFSet.pair (env (v 0)) (env (v 5)) ∈ env births := by
  simp only [chronologyLayerPairLookupFormula, Truth, truth_disj,
    truth_orderedPairFormula, truth_pairMembershipFormula]
end BoundedFormula

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

theorem layerRelationParams_ground {N : ZFSet.{u}} (hN : N ∈ M.sets) :
    ∀ i, fields.layerRelationParams N i ∈ M.sets :=
  Fin.cases fields.time_ground (Fin.cases (fields.graph_ground 0) (Fin.cases (fields.graph_ground 1)
    (Fin.cases (fields.graph_ground 2) (Fin.cases (fields.graph_ground 3) (fun _ => hN)))))

theorem realize_chronologyLayerRelation
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
    {N z s t : ZFSet.{u}} (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    (hs : s ∈ T) (ht : t ∈ T) (earlier : t = s ∨ t ∈ s) :
    Realize M.sets chronologyLayerRelationFormula
      (extend (ZFSet.pair s t) (extend z (fields.layerRelationParams N))) ↔
      GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t N z := by
  let env := extend (ZFSet.pair s t) (extend z (fields.layerRelationParams N))
  have members : ∀ i, env i ∈ M.sets := Fin.cases
    (M.orderedPair_mem pairing (M.transitive fields.time_ground hs) (M.transitive fields.time_ground ht))
    (Fin.cases hz (fields.layerRelationParams_ground hN))
  rw [chronologyLayerRelationFormula, realize_exBlock]
  constructor
  · rintro ⟨v, ground, recognized⟩
    have allGround := extendMany_members 6 v env ground members
    have lookup := (BoundedFormula.truth_chronologyLayerPairLookupFormula
      (suffixIndex 8 6 0) (suffixIndex 8 6 2) (suffixIndex 8 6 3) (suffixIndex 8 6 4)
      (suffixIndex 8 6 5) (suffixIndex 8 6 6) (prefixIndex 8 6) (extendMany 6 v env)).1
        ((BoundedFormula.realize_toFormula M _ _ allGround).1 recognized.1)
    simp only [extendMany_prefix, extendMany_suffix] at lookup
    change v 0 ∈ T ∧ v 1 ∈ T ∧ (v 1 = v 0 ∨ v 1 ∈ v 0) ∧
      ZFSet.pair s t = ZFSet.pair (v 0) (v 1) ∧
      ZFSet.pair (v 0) (v 2) ∈ fields.graph 0 ∧
      ZFSet.pair (v 0) (v 3) ∈ fields.graph 1 ∧
      ZFSet.pair (v 0) (v 4) ∈ fields.graph 2 ∧
      ZFSet.pair (v 0) (v 5) ∈ fields.graph 3 at lookup
    have same := ZFSet.pair_inj.1 lookup.2.2.2.1
    have eL := fields.value_eq_of_entry 0 lookup.2.2.2.2.1
    have er := fields.value_eq_of_entry 1 lookup.2.2.2.2.2.1
    have eμ := fields.value_eq_of_entry 2 lookup.2.2.2.2.2.2.1
    have eb := fields.value_eq_of_entry 3 lookup.2.2.2.2.2.2.2
    have meet : MeetOrderCode (v 2) (v 3) (v 4) :=
      eL ▸ er ▸ eμ ▸ (fields.decoded_point core lookup.1).meet
    have liftedMeet : MeetOrderCode
        (extendMany 6 v env (prefixIndex 8 6 2)) (extendMany 6 v env (prefixIndex 8 6 3))
        (extendMany 6 v env (prefixIndex 8 6 4)) := by
      simpa only [extendMany_prefix] using meet
    have witness := (M.realize_growthLayerWitnessFormula unions (suffixIndex 8 6 1)
      (suffixIndex 8 6 3) (suffixIndex 8 6 4) (suffixIndex 8 6 5)
      (prefixIndex 8 6 2) (prefixIndex 8 6 3) (prefixIndex 8 6 4) (prefixIndex 8 6 5)
      (prefixIndex 8 6 1) (suffixIndex 8 6 7) (extendMany 6 v env) allGround liftedMeet).1 recognized.2
    simp only [extendMany_prefix, extendMany_suffix] at witness
    change GrowthLayerWitnessCode _ _ _ (v 2) (v 3) (v 4) (v 5) (v 1) N z at witness
    rw [← eL, ← er, ← eμ, ← eb, ← same.1, ← same.2] at witness
    exact witness
  · intro witness
    let v : Fin 6 → ZFSet.{u} := Fin.cases s (Fin.cases t (Fin.cases (fields.value 0 s)
      (Fin.cases (fields.value 1 s) (Fin.cases (fields.value 2 s) (fun _ => fields.value 3 s)))))
    have ground : ∀ i, v i ∈ M.sets := Fin.cases (M.transitive fields.time_ground hs)
      (Fin.cases (M.transitive fields.time_ground ht) (Fin.cases (fields.value_ground 0 s)
        (Fin.cases (fields.value_ground 1 s) (Fin.cases (fields.value_ground 2 s) (fun _ => fields.value_ground 3 s)))))
    have allGround := extendMany_members 6 v env ground members
    refine ⟨v, ground, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ allGround).2
      apply (BoundedFormula.truth_chronologyLayerPairLookupFormula
        (suffixIndex 8 6 0) (suffixIndex 8 6 2) (suffixIndex 8 6 3) (suffixIndex 8 6 4)
        (suffixIndex 8 6 5) (suffixIndex 8 6 6) (prefixIndex 8 6) (extendMany 6 v env)).2
      simp only [extendMany_prefix, extendMany_suffix]
      exact ⟨hs, ht, earlier, rfl, fields.value_entry 0 hs, fields.value_entry 1 hs,
        fields.value_entry 2 hs, fields.value_entry 3 hs⟩
    · have liftedMeet : MeetOrderCode
          (extendMany 6 v env (prefixIndex 8 6 2)) (extendMany 6 v env (prefixIndex 8 6 3))
          (extendMany 6 v env (prefixIndex 8 6 4)) := by
        simp only [extendMany_prefix]
        exact (fields.decoded_point core hs).meet
      apply (M.realize_growthLayerWitnessFormula unions (suffixIndex 8 6 1)
        (suffixIndex 8 6 3) (suffixIndex 8 6 4) (suffixIndex 8 6 5)
        (prefixIndex 8 6 2) (prefixIndex 8 6 3) (prefixIndex 8 6 4) (prefixIndex 8 6 5)
        (prefixIndex 8 6 1) (suffixIndex 8 6 7) (extendMany 6 v env) allGround liftedMeet).2
      simp only [extendMany_prefix, extendMany_suffix]
      exact witness

end GroundChronologyFields

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixPriorFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem serialFieldUnion_rank_le_code (j : Fin 5) :
    ZFSet.rank (run.serialFieldUnion j) ≤ ZFSet.rank run.code :=
  (familyCodeGraph_valueUnion_rank_le run.key _).trans (run.serialFieldFamily_rank_le_code j)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitChronologyCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitValueGraph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) (F : ZFSet.{u}) {V : ZFSet.{u}}
    (values : ZFSet.rank V < o) : ZFSet.rank (run.limitValueGraph F V) < o :=
  indexedValueLift_rank_lt limit run.indices run.carrierUnion F run.limitPointInclusions
    (run.limitPoints_rank_lt limit rank) values





theorem heightValueBound_rank_le_code : ZFSet.rank run.heightValueBound ≤ ZFSet.rank run.code :=
  (ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans (run.stageFieldUnion_rank_le_code 10))

theorem limitHeight_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitHeight < o :=
  run.limitValueGraph_rank_lt limit rank _ (run.heightValueBound_rank_le_code.trans_lt rank)





theorem limitBirth_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank run.limitBirth < o :=
  run.limitValueGraph_rank_lt limit rank run.birthFamily (run.cutoffLimit_rank_le_code.trans_lt rank)





theorem limitTerminalPoint : ChronologyPointCode (insert run.cutoffLimit run.cutoffLimit) C D rD
    run.cutoffLimit run.limitPoints run.limitOrder run.limitMeetGraph run.limitBirth run.limitHeight where
  meet := run.limitMeet_code
  birth_function := by
    refine ⟨?_, run.limitBirth_function.2⟩
    intro z hz
    obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 (run.limitBirth_function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_insert_of_mem _ ht⟩
  birth_bound _ _ _ entry := Or.inr (ZFSet.pair_mem_prod.1 (run.limitBirth_function.1 entry)).2
  old_meet := run.limit_old_meet
  strict_height := run.limitHeight_code

theorem limitTerminalFields_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ∀ j, ZFSet.rank (run.limitTerminalFields j) < o :=
  Fin.cases (run.limitPoints_rank_lt limit rank) (Fin.cases (run.limitOrder_rank_lt limit rank)
    (Fin.cases (run.limitMeetGraph_rank_lt limit rank) (Fin.cases (run.limitBirth_rank_lt limit rank)
      (Fin.cases (run.limitHeight_rank_lt limit rank) (fun i => Fin.elim0 i)))))





theorem limitChronologyFields_terminal (j : Fin 5) :
    run.limitChronologyFields.value j run.cutoffLimit = run.limitTerminalFields j :=
  run.limitPriorFields.appendTime_value_at pairing unions run.limitTerminalFields run.limitTerminalFields_ground j

theorem limitChronologyFields_source_entries (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (before : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) (y : ZFSet.{u}) :
    ZFSet.pair s y ∈ run.limitChronologyFields.graph j ↔
      ZFSet.pair s y ∈ (run.linked i).serial.fields.graph j := by
  have old := run.limitPriorFields.appendTime_old_entries pairing unions run.limitTerminalFields
    run.limitTerminalFields_ground j ((run.cutoffLimit_mem s).2 ⟨i, before⟩) (y := y)
  exact (old.trans (run.serialFieldUnion_at i j before y)).trans
    ((run.serialFieldGraph_entry i j s y).trans (and_iff_right before)).symm

theorem limitChronologyFields_graph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) (j : Fin 5) :
    ZFSet.rank (run.limitChronologyFields.graph j) < o :=
  run.limitPriorFields.appendTime_graph_rank_lt pairing unions run.limitTerminalFields
    run.limitTerminalFields_ground limit (run.cutoffLimit_rank_le_code.trans_lt rank)
    (fun j => (run.serialFieldUnion_rank_le_code j).trans_lt rank)
    (run.limitTerminalFields_rank_lt limit rank) j





theorem limitChronologyPoint {s : ZFSet.{u}} (hs : s ∈ insert run.cutoffLimit run.cutoffLimit) :
    ChronologyPointCode (insert run.cutoffLimit run.cutoffLimit) C D rD s
      (run.limitChronologyFields.value 0 s) (run.limitChronologyFields.value 1 s)
      (run.limitChronologyFields.value 2 s) (run.limitChronologyFields.value 3 s)
      (run.limitChronologyFields.value 4 s) := by
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · simp only [run.limitChronologyFields_terminal]
    exact run.limitTerminalPoint
  · obtain ⟨i, before⟩ := (run.cutoffLimit_mem s).1 hs
    rw [run.limitChronologyFields_values i 0 before, run.limitChronologyFields_values i 1 before,
      run.limitChronologyFields_values i 2 before, run.limitChronologyFields_values i 3 before,
      run.limitChronologyFields_values i 4 before]
    change ChronologyPointCode (insert run.cutoffLimit run.cutoffLimit) C D rD s
      ((run.diagram.stage i).history.space s) ((run.diagram.stage i).history.order s)
      ((run.diagram.stage i).history.meetGraph s) ((run.diagram.stage i).history.birth s)
      ((run.diagram.stage i).history.height s)
    have sourceTime : s ∈ insert (run.diagram.stage i).cutoff (run.diagram.stage i).cutoff :=
      ZFSet.mem_insert_iff.2 before
    refine ⟨(run.diagram.stage i).history.meet_order s sourceTime, ?_,
      (run.diagram.stage i).history.birth_bound s sourceTime,
      (run.diagram.stage i).history.old_meet s sourceTime,
      (run.diagram.stage i).history.strict_height s sourceTime⟩
    refine ⟨?_, ((run.diagram.stage i).history.birth_function s sourceTime).2⟩
    intro z hz
    obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1
      (((run.diagram.stage i).history.birth_function s sourceTime).1 hz)
    have member : t ∈ run.cutoffLimit := by
      rcases ZFSet.mem_insert_iff.1 ht with rfl | ht
      · exact run.cutoff_mem_cutoffLimit i
      · exact run.cutoffLimit_ordinal.1 _ (run.cutoff_mem_cutoffLimit i) _ ht
    exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_insert_of_mem _ member⟩

theorem limitChronologyCore : ChronologyCoreCode (insert run.cutoffLimit run.cutoffLimit)
    run.limitChronologyFields.bound C D rD run.limitChronologyFields.graph where
  function := run.limitChronologyFields.function
  point s hs L r μ birth height eL er eμ eb eh := by
    have current := run.limitChronologyPoint hs
    rw [run.limitChronologyFields.value_eq_of_entry 0 eL,
      run.limitChronologyFields.value_eq_of_entry 1 er,
      run.limitChronologyFields.value_eq_of_entry 2 eμ,
      run.limitChronologyFields.value_eq_of_entry 3 eb,
      run.limitChronologyFields.value_eq_of_entry 4 eh] at current
    exact current

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainPrefixLimitLayerWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem familyPointBound_rank_le (Qs : ZFSet.{u}) :
    ZFSet.rank (familyPointBound Qs) ≤ ZFSet.rank Qs :=
  (ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _))

namespace CountableLayerCode

theorem ground_pushforward_rank_lt
    {M : TransitiveGround.{u}} {A B old born t D N injection e : ZFSet.{u}}
    (code : CountableLayerCode A old t D N injection)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets) (he : e ∈ M.sets)
    (hD : D ∈ M.sets) (hInjection : injection ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (target : ZFSet.rank B < o) (numbers : ZFSet.rank N < o)
    (embedding : InjectionCode A B e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    ∃ D' ∈ M.sets, ∃ injection' ∈ M.sets, CountableLayerCode B born t D' N injection' ∧
      ZFSet.rank D' < o ∧ ZFSet.rank injection' < o := by
  obtain ⟨E, hE, f, hf, copied⟩ := code.ground_pushforward pairing unions powers separation
    hA hB hN he hD hInjection embedding preserves noNew
  let D' := ZFSet.sep (fun x => x ∈ B) E
  let f' := ZFSet.sep (fun z => z ∈ ZFSet.prod D' N) f
  have hD' : D' ∈ M.sets := M.bounded_separation_mem separation (.mem 0 1)
    (extend B Fin.elim0) (Fin.cases hB (fun i => Fin.elim0 i)) hE
  have hf' : f' ∈ M.sets := M.injection_restriction_mem separation hD' hN hf
  have injected : InjectionCode D' N f' :=
    copied.small.restrict (fun _ hx => (ZFSet.mem_sep.1 hx).1)
  have rankD : ZFSet.rank D' < o :=
    (ZFSet.rank_mono (show D' ⊆ B from fun _ hx => (ZFSet.mem_sep.1 hx).2)).trans_lt target
  refine ⟨D', hD', f', hf', ⟨injected, ?_⟩, rankD,
    rank_functionGraph_lt limit injected.function rankD numbers⟩
  intro x hx entry
  exact ZFSet.mem_sep.2 ⟨copied.cover x hx entry, hx⟩
end CountableLayerCode

namespace GrowthLayerWitnessCode

theorem ground_pushforward_rank_lt
    {M : TransitiveGround.{u}} {Qs rs μs A B rA rB μA μB old born t N z e : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs A rA μA old t N z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank z < o)
    (sourceGraphs : ZFSet.rank Qs < o) (target : ZFSet.rank B < o) (numbers : ZFSet.rank N < o)
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs B rB μB born t N z' ∧
      ZFSet.rank z' < o := by
  have rankU := (familyPointBound_rank_le Qs).trans_lt sourceGraphs
  have rankW := M.groundRelations_rank_lt limit rankU target
  rcases code with ⟨D, injection, rfl, code⟩ |
    ⟨I, parts, Indices, Maps, W, injection, rfl, code⟩ |
    ⟨I, Indices, Maps, W, Components, F, rfl, code⟩
  · have fields := M.nonemptyTupleCode_field_mem 2 _ hz
    obtain ⟨D', hD', injection', hInjection', copied, rankD, rankInjection⟩ :=
      code.ground_pushforward_rank_lt pairing unions powers separation hA hB hN he
        (fields 1) (fields 2) limit target numbers embedding.injection preserves noNew
    exact ⟨countableLayerWitness D' injection', M.countableLayerWitness_mem pairing hD' hInjection',
      Or.inl ⟨D', injection', rfl, copied⟩,
      countableLayerWitness_rank_lt limit rankD rankInjection⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ hz
    have ranks := fun j => (rank_nonemptyTupleCode_field_le 6 _ j).trans_lt rank
    obtain ⟨hMaps', hW', hParts', copied⟩ := code.ground_pushforward
      pairing unions powers separation hA hB he hQs (fields 1) (fields 2) (fields 4)
      embedding preserves noNew
    have rankMaps := rank_functionGraph_lt limit copied.maps (ranks 1) rankW
    have rankParts : ZFSet.rank (relationCompose I A B parts e) < o :=
      (ZFSet.rank_mono (show relationCompose I A B parts e ⊆ ZFSet.prod I B from
        fun _ hx => (ZFSet.mem_sep.1 hx).1)).trans_lt (rank_product_lt limit (ranks 1) target)
    exact ⟨copyLayerWitness I (relationCompose I A B parts e) Indices
        (M.mapFamilyPushforward I (familyPointBound Qs) A B Maps e)
        (M.groundRelations (familyPointBound Qs) B) injection,
      M.copyLayerWitness_mem pairing unions (fields 1) hParts' (fields 3) hMaps' hW' (fields 6),
      Or.inr (Or.inl ⟨I, _, Indices, _, _, injection, rfl, copied⟩),
      copyLayerWitness_rank_lt limit (ranks 1) rankParts (ranks 3) rankMaps rankW (ranks 6)⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ hz
    have ranks := fun j => (rank_nonemptyTupleCode_field_le 6 _ j).trans_lt rank
    obtain ⟨hMaps', hW', hComponents', hF', copied⟩ := code.ground_pushforward
      pairing unions powers separation hA hB he hQs (fields 1) (fields 3) (fields 5) (fields 6)
      source embedding preserves noNew
    have rankMaps := rank_functionGraph_lt limit copied.maps (ranks 1) rankW
    have rankF : ZFSet.rank (relationImage F B (layerFiberEmbedding F B e)) < o :=
      (ZFSet.rank_mono (show relationImage F B (layerFiberEmbedding F B e) ⊆ B from
        fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1)).trans_lt target
    have rankComponents := rank_functionGraph_lt limit copied.components rankF (ranks 1)
    exact ⟨separatedLayerWitness I Indices
        (M.mapFamilyPushforward I (familyPointBound Qs) A B Maps e)
        (M.groundRelations (familyPointBound Qs) B)
        (pushedHeightGraph F B I (layerFiberEmbedding F B e) Components)
        (relationImage F B (layerFiberEmbedding F B e)),
      M.separatedLayerWitness_mem pairing unions (fields 1) (fields 2) hMaps' hW' hComponents' hF',
      Or.inr (Or.inr ⟨I, Indices, _, _, _, _, rfl, copied⟩),
      separatedLayerWitness_rank_lt limit (ranks 1) (ranks 2) rankMaps rankW rankComponents rankF⟩

end GrowthLayerWitnessCode

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitTerminal_raw_witness_rank_lt (i : I) {t Qs rs μs : ZFSet.{u}}
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff)
    (spaces : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ (run.linked i).serial.fields.graph 0 ↔
      ZFSet.pair s y ∈ Qs)
    (orders : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ (run.linked i).serial.fields.graph 1 ↔
      ZFSet.pair s y ∈ rs)
    (meets : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ (run.linked i).serial.fields.graph 2 ↔
      ZFSet.pair s y ∈ μs)
    (hOmega : ZFSet.omega ∈ M.sets) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) (numbers : ZFSet.rank ZFSet.omega < o) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode Qs rs μs run.limitPoints run.limitOrder
      run.limitMeetGraph run.limitBirth t ZFSet.omega z ∧ ZFSet.rank z < o := by
  have prior : t = (run.linked i).main.cutoff ∨ t ∈ (run.linked i).main.cutoff := by
    simpa only [run.linked_main] using before
  have hs := ZFSet.mem_insert (run.linked i).main.cutoff (run.linked i).main.cutoff
  have ht := ZFSet.mem_insert_iff.2 prior
  have raw := (run.linked i).serial.layer_code _ hs _ ht prior _
    ((run.linked i).serial.layerWitness_entry hs ht prior)
  have terminal := (run.linked i).terminal_values
  have code : GrowthLayerWitnessCode
      ((run.linked i).serial.fields.graph 0) ((run.linked i).serial.fields.graph 1)
      ((run.linked i).serial.fields.graph 2)
      (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
      (run.diagram.stage i).stage.meetGraph (run.diagram.stage i).birth t ZFSet.omega
      ((run.linked i).serial.layerWitness (run.linked i).main.cutoff t) := by
    rw [terminal.1, terminal.2.1, terminal.2.2.1, terminal.2.2.2.1] at raw
    simpa only [run.linked_main] using raw
  have serialBound : ZFSet.rank (run.linked i).serial.code ≤ ZFSet.rank (run.linked i).code := by
    simpa only [GroundLinkedMainStage.code, linkedMainStageCode, Fin.cases_succ] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases (run.linked i).main.stage.code
        (Fin.cases (run.linked i).main.cutoff (fun _ => (run.linked i).serial.code)))
        (0 : Fin 1).succ.succ)
  have serialRank : ZFSet.rank (run.linked i).serial.code < o :=
    serialBound.trans_lt ((run.linkedCode_rank_lt_code i).trans rank)
  have witnessRank := ((run.linked i).serial.layerWitness_rank_lt_code hs ht prior).trans serialRank
  have sourceRank := ((run.linked i).serial.fieldGraph_rank_le_code 0).trans_lt serialRank
  obtain ⟨z, hz, copied, ranked⟩ := code.ground_pushforward_rank_lt
    pairing unions powers separation (run.diagram.stage i).stage.carrier_ground
    run.limitPoints_ground (run.limitPointMap_ground i)
    ((run.linked i).serial.fields.graph_ground 0) hOmega
    ((run.linked i).serial.layerWitness_ground _ _) limit witnessRank sourceRank
    (run.limitPoints_rank_lt limit rank) numbers (run.diagram.stage i).stage.meet
    (run.limitPointMap_meetEmbedding i) (run.limitPointMap_birth_iff i) (by
      intro q _ birth
      obtain ⟨x, hx, _, image⟩ := (run.limitBirth_old_fiber i q t before).1 birth
      exact ⟨x, hx, image⟩)
  exact ⟨z, hz, copied.congr_source_entries spaces orders meets, ranked⟩

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSerializedCandidateLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u





namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem ranked_mem_validChronologies
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {T C D rD : ZFSet.{u}} (serial : GroundSerializedChronology M T C D rD)
    (rank : ZFSet.rank serial.code < ZFSet.rank K) :
    serial.code ∈ level.validChronologies C D rD :=
  M.serializedChronology_code_mem_candidates serial
    ((level.membership _).2 ⟨serial.code_ground pairing, rank⟩)

end GroundMainCandidateLevel

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLinkedMainStageLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_linkedMainStageFormula_raw {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainStageFormula K Labels C D rD N z) env ↔
      ∃ f : Fin 24 → ZFSet.{u}, (∀ j, f j ∈ M.sets) ∧
        LinkedMainStageRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N) (env z) f := by
  rw [linkedMainStageFormula, realize_exBlock]
  have actual (f : Fin 24 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :=
    M.realize_linkedMainStageRawFormula pairing unions powers separation collection
      (suffixIndex n 24 K) (suffixIndex n 24 Labels) (suffixIndex n 24 C) (suffixIndex n 24 D)
      (suffixIndex n 24 rD) (suffixIndex n 24 N) (suffixIndex n 24 z) (prefixIndex n 24)
      (extendMany 24 f env) (extendMany_members 24 f env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f, ground, (actual f ground).1 recognized⟩
  · rintro ⟨f, ground, raw⟩
    exact ⟨f, ground, (actual f ground).2 raw⟩

theorem realize_linkedMainStageFormula {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainStageFormula K Labels C D rD N z) env ↔
      ∃ linked : GroundLinkedMainStage M (env K) (env Labels) (env C) (env D) (env rD),
        linked.code = env z := by
  rw [M.realize_linkedMainStageFormula_raw pairing unions powers separation collection
    K Labels C D rD N z env members omega ordinal]
  constructor
  · rintro ⟨f, ground, raw⟩
    exact raw.exists_linked pairing unions powers separation ground (members C) (members D) (members rD) omega
  · rintro ⟨linked, equal⟩
    refine ⟨linked.rawFields, linked.rawFields_ground pairing, ?_⟩
    rw [omega, ← equal]
    exact linked.rawFields_code

omit pairing unions powers separation collection in
theorem mem_linkedMainStageCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.linkedMainStageCandidates B K Labels C D rD ↔
      z ∈ B ∧ ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z := ZFSet.mem_sep

theorem linkedMainStageCandidates_mem (infinite : Realize M.sets infinity Fin.elim0)
    {B K Labels C D rD : ZFSet.{u}} (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (ordinal : ordinalSetProperty K) : M.linkedMainStageCandidates B K Labels C D rD ∈ M.sets := by
  let params := extend K (extend Labels (extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))))
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hK (Fin.cases hLabels (Fin.cases hC
    (Fin.cases hD (Fin.cases hrD (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))))
  have selected := M.separation_mem separation (linkedMainStageFormula 1 2 3 4 5 6 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (linkedMainStageFormula 1 2 3 4 5 6 0)
      (extend z params)) B = M.linkedMainStageCandidates B K Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_linkedMainStageCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_linkedMainStageFormula pairing unions powers separation collection
      1 2 3 4 5 6 0 (extend z params) (Fin.cases (M.transitive hB hz) ground) rfl ordinal
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSmallFamilyRangeRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundRegular
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (regular : GroundRegular M K)
include regular

theorem familyCodeGraph_valueRange_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K)
    {I : Type v} [Small.{u} I] (key value : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets) (whole : familyCodeGraph key value ∈ M.sets)
    (small : GroundBelow M (ZFSet.range key) K)
    (ranks : ∀ i, ZFSet.rank (value i) < ZFSet.rank K) :
    ZFSet.rank (ZFSet.range value) < ZFSet.rank K := by
  let R := ZFSet.range value
  have hR : R ∈ M.sets := M.familyCodeGraph_valueRange_mem unions separation key value domain whole
  have rankGround := M.cumulativeRankGraph_mem pairing unions powers separation collection hR hK
  have rankFunction : ZFSet.IsFunc R K (cumulativeRankGraph R K) := by
    apply cumulativeRankGraph_function ordinal
    intro x hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    exact ranks i
  let graph := relationCompose (ZFSet.range key) R K (familyCodeGraph key value) (cumulativeRankGraph R K)
  have ground : graph ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    domain hR hK whole rankGround
  have function : ZFSet.IsFunc (ZFSet.range key) K graph :=
    relationCompose_function_of_subset (familyCodeGraph_isFunc key value injective) rankFunction (fun _ h => h)
  obtain ⟨b, hb, bounded⟩ := regular.bound_small_domain pairing unions powers separation domain hK ground small function
  have uniform : ∀ i, ZFSet.rank (value i) < ZFSet.rank b := by
    intro i
    have hi : value i ∈ R := ZFSet.mem_range.2 ⟨i, rfl⟩
    obtain ⟨a, entry, _⟩ := rankFunction.2 (value i) hi
    have rankEntry := (pair_mem_cumulativeRankGraph R K (value i) a).1 entry
    have composite : ZFSet.pair (key i) a ∈ graph :=
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, rankEntry.2.1, value i, hi,
          (pair_mem_familyCodeGraph key value injective i _).2 rfl, entry⟩
    have rank := ZFSet.rank_lt_of_mem (bounded (key i) a composite)
    simpa only [rankEntry.2.2, rank_ordinalCode] using rank
  apply (ZFSet.rank_le_iff.2 ?_).trans_lt (ZFSet.rank_lt_of_mem hb)
  intro x hx
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
  exact uniform i

end PartitionPilot.Forcing.GroundRegular

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundChronologicalTransitionTransport
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologicalMainTransition
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target first second : GroundChronologicalMainStage M C D rD}

theorem retargetEq_points
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).map.points = transition.map.points := by
  cases sourceEqual
  cases targetEqual
  rfl

theorem retargetEq_actors
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).map.actors = transition.map.actors := by
  cases sourceEqual
  cases targetEqual
  rfl

theorem retargetEq_code
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).map.code = transition.map.code := by
  cases sourceEqual
  cases targetEqual
  rfl

end PartitionPilot.Forcing.GroundChronologicalMainTransition

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyPairRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
include conditions pairing unions powers separation collection infinite hK

theorem functionGraphOn_rank_lt_small {I f : ZFSet.{u}}
    (hI : I ∈ M.sets) (small : GroundBelow M I K)
    (inputs : ∀ i ∈ I, ZFSet.rank i < ZFSet.rank K)
    (hf : f ∈ M.sets) (function : FunctionGraphOn I f)
    (values : ∀ i ∈ I, ∀ v, ZFSet.pair i v ∈ f → ZFSet.rank v < ZFSet.rank K) :
    ZFSet.rank f < ZFSet.rank K := by
  have smallF := small.functionGraphOn pairing unions powers separation hI hf hK function
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  apply conditions.2.2.1.rank_lt_of_small pairing unions powers separation collection
    hf hK conditions.1 smallF
  intro z hz
  obtain ⟨i, hi, v, rfl⟩ := function.shape z hz
  exact rank_orderedPair_lt limit (inputs i hi) (values i hi v hz)

theorem functionGraph_rank_lt_small_cumulative {I V f : ZFSet.{u}}
    (hI : I ∈ M.sets) (small : GroundBelow M I K)
    (inputs : ∀ i ∈ I, ZFSet.rank i < ZFSet.rank K)
    (hf : f ∈ M.sets) (function : ZFSet.IsFunc I V f)
    (level : ∀ x, x ∈ V ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank K) :
    ZFSet.rank f < ZFSet.rank K := by
  apply conditions.functionGraphOn_rank_lt_small pairing unions powers separation collection
    infinite hK hI small inputs hf ⟨V, function⟩
  intro i _ v entry
  exact ((level v).1 (ZFSet.pair_mem_prod.1 (function.1 entry)).2).2

end PartitionPilot.Forcing.GroundInaccessibleConditions



namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K T : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets) (hT : T ∈ K)
include conditions pairing unions powers separation hK hT

theorem chronologyPairs_below : GroundBelow M (chronologyPairs T) K := by
  have hTM := M.transitive hK hT
  have smallT := GroundBelow.of_member pairing unions powers separation hK hT
  have smallProduct := smallT.product pairing unions powers separation hTM hTM hK
    conditions.1 conditions.2.2.2 smallT
  exact smallProduct.restrict separation
    (M.chronologyPairs_mem pairing unions powers separation hTM) hK (chronologyPairs_subset T)

theorem chronologyPairs_rank_lt (infinite : Realize M.sets infinity Fin.elim0) :
    ZFSet.rank (chronologyPairs T) < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact (ZFSet.rank_mono (chronologyPairs_subset T)).trans_lt
    (rank_product_lt limit (ZFSet.rank_lt_of_mem hT) (ZFSet.rank_lt_of_mem hT))

theorem chronologyPairs_member_rank_lt (infinite : Realize M.sets infinity Fin.elim0)
    {p : ZFSet.{u}} (hp : p ∈ chronologyPairs T) : ZFSet.rank p < ZFSet.rank K :=
  (ZFSet.rank_lt_of_mem hp).trans
    (conditions.chronologyPairs_rank_lt pairing unions powers separation hK hT infinite)

end PartitionPilot.Forcing.GroundInaccessibleConditions

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRankedLayerSelection
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem choose_layerGraph_in
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {V : ZFSet.{u}} (hV : V ∈ M.sets)
    (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
    (rawWitnesses : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
      ∃ z ∈ V, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z) :
    ∃ layers ∈ M.sets, ZFSet.IsFunc (chronologyPairs T) V layers ∧
      ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s → ∀ z,
        ZFSet.pair (ZFSet.pair s t) z ∈ layers →
          GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
            (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z := by
  have hN := M.omega_mem separation infinite
  have hPairs := M.chronologyPairs_mem pairing unions powers separation fields.time_ground
  let relation := M.definableRelation chronologyLayerRelationFormula
    (fields.layerRelationParams ZFSet.omega) (chronologyPairs T) V
  have hRelation : relation ∈ M.sets := M.definableRelation_mem pairing unions powers separation
    chronologyLayerRelationFormula (fields.layerRelationParams ZFSet.omega)
    (fields.layerRelationParams_ground hN) hPairs hV
  have total : ∀ p ∈ chronologyPairs T, ∃ z ∈ V, ZFSet.pair p z ∈ relation := by
    intro p hp
    obtain ⟨s, hs, t, ht, rfl, earlier⟩ := (mem_chronologyPairs T p).1 hp
    obtain ⟨z, hz, code⟩ := rawWitnesses s hs t ht earlier
    exact ⟨z, hz, (M.pair_mem_definableRelation chronologyLayerRelationFormula
      (fields.layerRelationParams ZFSet.omega) (chronologyPairs T) V _ z).2
        ⟨hp, hz, (fields.realize_chronologyLayerRelation pairing unions core hN
          (M.transitive hV hz) hs ht earlier).2 code⟩⟩
  obtain ⟨layers, hLayers, function, subset⟩ :=
    M.uniformize_relation pairing unions powers separation choice hPairs hV hRelation total
  refine ⟨layers, hLayers, function, ?_⟩
  intro s hs t ht earlier z entry
  have recognized := (M.pair_mem_definableRelation chronologyLayerRelationFormula
    (fields.layerRelationParams ZFSet.omega) (chronologyPairs T) V _ z).1 (subset entry)
  exact (fields.realize_chronologyLayerRelation pairing unions core hN
    (M.transitive hV recognized.2.1) hs ht earlier).1 recognized.2.2

theorem choose_rankedLayerGraph
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K V : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hT : T ∈ K) (hV : V ∈ M.sets)
    (level : ∀ x, x ∈ V ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank K)
    (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
    (rawWitnesses : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
      ∃ z ∈ M.sets, ZFSet.rank z < ZFSet.rank K ∧
        GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
          (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z) :
    ∃ layers ∈ M.sets, ZFSet.IsFunc (chronologyPairs T) V layers ∧
      ZFSet.rank layers < ZFSet.rank K ∧
      ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s → ∀ z,
        ZFSet.pair (ZFSet.pair s t) z ∈ layers →
          GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
            (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z := by
  have witnesses : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
      ∃ z ∈ V, GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z := by
    intro s hs t ht earlier
    obtain ⟨z, hz, rank, code⟩ := rawWitnesses s hs t ht earlier
    exact ⟨z, (level z).2 ⟨hz, rank⟩, code⟩
  obtain ⟨layers, hLayers, function, codes⟩ :=
    fields.choose_layerGraph_in pairing unions powers separation infinite choice hV core witnesses
  have rank := conditions.functionGraph_rank_lt_small_cumulative pairing unions powers separation
    collection infinite hK (M.chronologyPairs_mem pairing unions powers separation fields.time_ground)
    (conditions.chronologyPairs_below pairing unions powers separation hK hT)
    (fun _ hp => conditions.chronologyPairs_member_rank_lt pairing unions powers separation hK hT infinite hp)
    hLayers function level
  exact ⟨layers, hLayers, function, rank, codes⟩

end PartitionPilot.Forcing.GroundChronologyFields

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSerializedBoundNormalization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundSerializedChronology
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets)

theorem normalizeBounds_code_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (time : ZFSet.rank T < o) (graphs : ∀ j, ZFSet.rank (serial.fields.graph j) < o)
    (layers : ZFSet.rank serial.layers < o) :
    ZFSet.rank (serial.normalizeBounds pairing unions powers separation).code < o :=
  rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases (serial.fields.normalizeBound_code_rank_lt pairing unions separation limit time graphs)
      (Fin.cases ((functionGraphRange_rank_le (chronologyPairs T) serial.layers).trans_lt layers)
        (fun _ => layers)))

end PartitionPilot.Forcing.GroundSerializedChronology

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRankedSerializedChronology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD K : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

theorem exists_rankedSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hT : T ∈ K) (level : GroundMainCandidateLevel M K)
    (ordinal : ordinalSetProperty T)
    (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
    (graphs : ∀ j, ZFSet.rank (fields.graph j) < ZFSet.rank K)
    (rawWitnesses : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s →
      ∃ z ∈ M.sets, ZFSet.rank z < ZFSet.rank K ∧
        GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
          (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z) :
    ∃ serial : GroundSerializedChronology M T C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
        serial.code ∈ level.validChronologies C D rD ∧
        serial.fields.graph = fields.graph ∧
        (∀ j s, serial.fields.value j s = fields.value j s) ∧
        serial.layerBound = functionGraphRange (chronologyPairs T) serial.layers := by
  obtain ⟨layers, hLayers, function, layerRank, codes⟩ :=
    fields.choose_rankedLayerGraph pairing unions powers separation collection infinite choice
      hK conditions hT level.carrier_ground level.membership core rawWitnesses
  let selected : GroundSerializedChronology M T C D rD :=
    ⟨fields, ordinal, core, level.carrier, level.carrier_ground, layers, hLayers, function, codes⟩
  let serial := selected.normalizeBounds pairing unions powers separation
  have rank : ZFSet.rank serial.code < ZFSet.rank K :=
    selected.normalizeBounds_code_rank_lt pairing unions powers separation
      (conditions.rank_isLimit pairing unions powers separation infinite hK)
      (ZFSet.rank_lt_of_mem hT) graphs layerRank
  exact ⟨serial, serial.code_ground pairing, rank,
    level.ranked_mem_validChronologies pairing serial rank, rfl, fun _ _ => rfl, rfl⟩

end PartitionPilot.Forcing.GroundChronologyFields

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTaskBearingSuccessorDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula

theorem truth_strictSuccessorTopFormula {n} (P Q R e top : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (strictSuccessorTopFormula P Q R e top) env ↔
      StrictSuccessorTopCode (env P) (env Q) (env R) (env e) (env top) := by
  simp only [strictSuccessorTopFormula, Truth, truth_imp, truth_pairMembershipFormula]
  rfl

end BoundedFormula





namespace BoundedFormula

theorem truth_mainSuccessorOutputFormula {n} (f : Fin 30 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mainSuccessorOutputFormula f) env ↔ MainSuccessorOutputCode (fun j => env (f j)) := by
  simp only [mainSuccessorOutputFormula, Truth, truth_mainTransitionLawsFormula,
    truth_strictSuccessorTopFormula, truth_separationFulfillmentFormula,
    truth_rectangleFulfillmentFormula, truth_oldProfilePreservationFormula,
    truth_taskCapFamilyFormula, truth_compressionActorFulfillmentFormula]
  exact ⟨fun ⟨t, g, s, r, p, c, a⟩ => ⟨t, g, s, r, p, c, a⟩,
    fun code => ⟨code.transition, code.strict_top, code.separation, code.rectangles,
      code.old_profiles, code.task_caps, code.compression_actors⟩⟩

theorem realize_mainSuccessorOutputFormula (M : TransitiveGround.{u}) {n}
    (f : Fin 30 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    SetFormula.Realize M.sets (mainSuccessorOutputFormula f).toFormula env ↔
      MainSuccessorOutputCode (fun j => env (f j)) :=
  (realize_toFormula M _ env members).trans (truth_mainSuccessorOutputFormula f env)

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainSuccessorTaskBindingsFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (Labels : Fin n) (f : Fin 30 → Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (meet : MeetOrderCode (env (f 0)) (env (f 2)) (env (f 4))) :
    Realize M.sets (mainSuccessorTaskBindingsFormula Labels f) env ↔
      MainSuccessorTaskBindingsCode M (env Labels) (fun j => env (f j)) :=
  (M.realize_groundEligibleTasksFormula pairing unions powers separation
    (f 21) (f 0) (f 6) (f 2) (f 4) (f 12) Labels env members meet).and
    ((M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
      0 (f 22) (f 21) (f 0) (f 2) (f 4) Labels env members meet).and
      ((M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
        1 (f 23) (f 21) (f 0) (f 2) (f 4) Labels env members meet).and
        ((M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
          3 (f 24) (f 21) (f 0) (f 2) (f 4) Labels env members meet).and
          ((M.realize_groundLiteralTaskFieldFormula pairing unions powers separation
            4 (f 25) (f 21) (f 0) (f 2) (f 4) Labels env members meet).and
            ((M.realize_relativePowerFormula (f 0) (f 26) env members).and
              (M.realize_groundTaskRepresentativesFormula pairing unions powers separation
                (f 27) (f 0) (f 6) (f 2) (f 4) (f 12) Labels env members meet))))))

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u v w

theorem linkedSuccessorOutputFields_map {A : Type v} {B : Type w}
    (map : A → B) (s t : Fin 24 → A) (points actors : A) (extra : Fin 8 → A) :
    (fun j => map (linkedSuccessorOutputFields s t points actors extra j)) =
      linkedSuccessorOutputFields (fun j => map (s j)) (fun j => map (t j))
        (map points) (map actors) (fun j => map (extra j)) := by
  funext j
  exact Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) (Fin.cases (rfl) ((fun k => Fin.elim0 k))))))))))))))))))))))))))))))) j

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_taskBearingMainSuccessorRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : Fin n)
    (source target : Fin 24 → Fin n) (extra : Fin 8 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (taskBearingMainSuccessorRawFormula K Labels C D rD N
      sourceCode targetCode z points actors sourceBirth targetBirth source target extra) env ↔
      TaskBearingMainSuccessorRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env sourceCode) (env targetCode) (env z) (env points) (env actors)
        (env sourceBirth) (env targetBirth) (fun j => env (source j))
        (fun j => env (target j)) (fun j => env (extra j)) := by
  have links := M.realize_linkedMainTransitionRawFormula pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth
    source target env members omega ordinal
  have outputs := BoundedFormula.realize_mainSuccessorOutputFormula M
    (linkedSuccessorOutputFields source target points actors extra) env members
  rw [linkedSuccessorOutputFields_map] at outputs
  change (Realize M.sets (linkedMainTransitionRawFormula K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth source target) env ∧
    env (source 11) ∈ env (target 11) ∧
    Realize M.sets (BoundedFormula.mainSuccessorOutputFormula
      (linkedSuccessorOutputFields source target points actors extra)).toFormula env ∧
    Realize M.sets (mainSuccessorTaskBindingsFormula Labels
      (linkedSuccessorOutputFields source target points actors extra)) env) ↔ _
  rw [links, outputs]
  have bindings (raw : LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD)
      (env N) (env sourceCode) (env targetCode) (env z) (env points) (env actors)
      (env sourceBirth) (env targetBirth) (fun j => env (source j)) (fun j => env (target j))) :
      Realize M.sets (mainSuccessorTaskBindingsFormula Labels
        (linkedSuccessorOutputFields source target points actors extra)) env ↔
      MainSuccessorTaskBindingsCode M (env Labels)
        (linkedSuccessorOutputFields (fun j => env (source j)) (fun j => env (target j))
          (env points) (env actors) (fun j => env (extra j))) := by
    have recognized := M.realize_mainSuccessorTaskBindingsFormula pairing unions powers separation
      Labels (linkedSuccessorOutputFields source target points actors extra) env members
      raw.1.2.2.1.1.meet
    rwa [linkedSuccessorOutputFields_map] at recognized
  exact ⟨fun ⟨raw, cutoff, out, bound⟩ => ⟨raw, cutoff, out, (bindings raw).1 bound⟩,
    fun ⟨raw, cutoff, out, bound⟩ => ⟨raw, cutoff, out, (bindings raw).2 bound⟩⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_taskBearingMainSuccessorFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (taskBearingMainSuccessorFormula K Labels C D rD N sourceCode targetCode z) env ↔
      TaskBearingMainSuccessorCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env sourceCode) (env targetCode) (env z) := by
  rw [taskBearingMainSuccessorFormula, realize_exBlock]
  have actual (fields : Fin 60 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    M.realize_taskBearingMainSuccessorRawFormula pairing unions powers separation collection
      (suffixIndex n 60 K) (suffixIndex n 60 Labels) (suffixIndex n 60 C) (suffixIndex n 60 D)
      (suffixIndex n 60 rD) (suffixIndex n 60 N) (suffixIndex n 60 sourceCode)
      (suffixIndex n 60 targetCode) (suffixIndex n 60 z)
      (prefixIndex n 60 48) (prefixIndex n 60 49) (prefixIndex n 60 50) (prefixIndex n 60 51)
      (fun j => prefixIndex n 60 (j.castAdd 36))
      (fun j => prefixIndex n 60 (Fin.natAdd 24 (j.castAdd 12)))
      (fun j => prefixIndex n 60 (Fin.natAdd 52 j))
      (extendMany 60 fields env) (extendMany_members 60 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  exact ⟨fun ⟨fields, ground, recognized⟩ => ⟨fields, ground, (actual fields ground).1 recognized⟩,
    fun ⟨fields, ground, raw⟩ => ⟨fields, ground, (actual fields ground).2 raw⟩⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TaskBearingMainSuccessorCode
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem output_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    ∃ extra : Fin 8 → ZFSet.{u}, (∀ j, extra j ∈ M.sets) ∧
      MainSuccessorOutputCode (linkedSuccessorOutputFields source.rawFields target.rawFields
        transition.map.points transition.map.actors extra) ∧
      MainSuccessorTaskBindingsCode M Labels (linkedSuccessorOutputFields source.rawFields target.rawFields
        transition.map.points transition.map.actors extra) := by
  obtain ⟨fields, ground, raw⟩ := code
  have sourceEq := source.rawFields_code.fields_unique raw.1.1
  have targetEq := target.rawFields_code.fields_unique raw.1.2.1
  have pairEq : ZFSet.pair transition.map.points transition.map.actors =
      ZFSet.pair (fields 48) (fields 49) := raw.1.2.2.2.2.1.1
  have maps := ZFSet.pair_inj.1 pairEq
  have output := raw.2.2.1
  have bindings := raw.2.2.2
  rw [← sourceEq, ← targetEq, ← maps.1, ← maps.2] at output bindings
  exact ⟨(fun j => fields (Fin.natAdd 52 j)),
    (fun j => ground (Fin.natAdd 52 j)), output, bindings⟩

end PartitionPilot.Forcing.TaskBearingMainSuccessorCode



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_LinkedSuccessorOutputFieldEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe v

theorem linkedSuccessorOutputFields_0 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 0 = s 0 := rfl

theorem linkedSuccessorOutputFields_1 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 1 = t 0 := rfl

theorem linkedSuccessorOutputFields_2 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 2 = s 1 := rfl

theorem linkedSuccessorOutputFields_3 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 3 = t 1 := rfl

theorem linkedSuccessorOutputFields_5 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 5 = t 2 := rfl

theorem linkedSuccessorOutputFields_7 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 7 = t 3 := rfl

theorem linkedSuccessorOutputFields_13 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 13 = t 7 := rfl

theorem linkedSuccessorOutputFields_18 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 18 = points := rfl

theorem linkedSuccessorOutputFields_29 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 29 = t 9 := rfl

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOmegaOneTaskBearingSuccessorFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_taskBearingSuccessorPairFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N S V source output : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (omega : env N = ZFSet.omega)
    (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (taskBearingSuccessorPairFormula K Labels C D rD N S V source output) env ↔
      ∃ target ∈ env S, ∃ z ∈ env V, env output = ZFSet.pair target z ∧
        TaskBearingMainSuccessorCode M (env K) (env Labels) (env C) (env D) (env rD)
          (env N) (env source) target z := by
  simp only [taskBearingSuccessorPairFormula, realize_ex, Realize]
  have recognized (target z : ZFSet.{u}) (ht : target ∈ M.sets) (hz : z ∈ M.sets) :=
    M.realize_taskBearingMainSuccessorFormula pairing unions powers separation collection
      K.succ.succ Labels.succ.succ C.succ.succ D.succ.succ rD.succ.succ N.succ.succ
      source.succ.succ 1 0 (extend z (extend target env)) (Fin.cases hz (Fin.cases ht members)) omega ordinal
  have pair (target z : ZFSet.{u}) (ht : target ∈ M.sets) (hz : z ∈ M.sets) :=
    (BoundedFormula.realize_toFormula M
      (BoundedFormula.orderedPairFormula output.succ.succ 1 0)
      (extend z (extend target env)) (Fin.cases hz (Fin.cases ht members))).trans
      (BoundedFormula.truth_orderedPairFormula output.succ.succ 1 0 (extend z (extend target env)))
  constructor
  · rintro ⟨target, ht, inS, z, hz, inV, shape, code⟩
    exact ⟨target, inS, z, inV, (pair target z ht hz).1 shape, (recognized target z ht hz).1 code⟩
  · rintro ⟨target, inS, z, inV, shape, code⟩
    have ht := M.transitive (members S) inS
    have hz := M.transitive (members V) inV
    exact ⟨target, ht, inS, z, hz, inV, (pair target z ht hz).2 shape, (recognized target z ht hz).2 code⟩

theorem taskBearingSuccessorParams_ground
    (separation : SeparationSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {S V K Labels C D rD : ZFSet.{u}} (hS : S ∈ M.sets) (hV : V ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    ∀ j, taskBearingSuccessorParams S V K Labels C D rD j ∈ M.sets :=
  Fin.cases hK (Fin.cases hLabels (Fin.cases hC (Fin.cases hD (Fin.cases hrD
    (Fin.cases (M.omega_mem separation infinite) (Fin.cases hS (Fin.cases hV (fun j => Fin.elim0 j))))))))

theorem taskBearingSuccessorRelation_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {S V K Labels C D rD : ZFSet.{u}} (hS : S ∈ M.sets) (hV : V ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    M.taskBearingSuccessorRelation S V K Labels C D rD ∈ M.sets :=
  M.definableRelation_mem pairing unions powers separation _ _
    (M.taskBearingSuccessorParams_ground separation infinite hS hV hK hLabels hC hD hrD)
    hS (M.prod_mem pairing unions powers separation hV hV)

theorem taskBearingSuccessorRelation_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {S V K Labels C D rD : ZFSet.{u}} (hS : S ∈ M.sets) (hV : V ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (ordinal : ordinalSetProperty K)
    (subset : S ⊆ V) (source target z : ZFSet.{u}) :
    ZFSet.pair source (ZFSet.pair target z) ∈ M.taskBearingSuccessorRelation S V K Labels C D rD ↔
      source ∈ S ∧ target ∈ S ∧ z ∈ V ∧
        TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z := by
  rw [taskBearingSuccessorRelation, M.pair_mem_definableRelation]
  have params := M.taskBearingSuccessorParams_ground separation infinite hS hV hK hLabels hC hD hrD
  have hVV := M.prod_mem pairing unions powers separation hV hV
  have recognized (hs : source ∈ S) (hp : ZFSet.pair target z ∈ ZFSet.prod V V) :=
    M.realize_taskBearingSuccessorPairFormula pairing unions powers separation collection
      2 3 4 5 6 7 8 9 0 1
      (extend source (extend (ZFSet.pair target z) (taskBearingSuccessorParams S V K Labels C D rD)))
      (Fin.cases (M.transitive hS hs) (Fin.cases (M.transitive hVV hp) params)) rfl ordinal
  constructor
  · rintro ⟨hs, hp, relation⟩
    obtain ⟨t, ht, w, hw, equal, code⟩ := (recognized hs hp).1 relation
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hs, ht, hw, code⟩
  · rintro ⟨hs, ht, hz, code⟩
    have hp := ZFSet.pair_mem_prod.2 ⟨subset ht, hz⟩
    exact ⟨hs, hp, (recognized hs hp).2 ⟨target, ht, z, hz, rfl, code⟩⟩

theorem choose_taskBearingSuccessors
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S V K Labels C D rD : ZFSet.{u}} (hS : S ∈ M.sets) (hV : V ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (ordinal : ordinalSetProperty K) (subset : S ⊆ V)
    (total : ∀ source ∈ S, ∃ target ∈ S, ∃ z ∈ V,
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z) :
    ∃ f ∈ M.sets, ZFSet.IsFunc S (ZFSet.prod V V) f ∧
      f ⊆ M.taskBearingSuccessorRelation S V K Labels C D rD ∧
      ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
        target ∈ S ∧ z ∈ V ∧
          TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z := by
  have entries := M.taskBearingSuccessorRelation_entry pairing unions powers separation collection infinite
    hS hV hK hLabels hC hD hrD ordinal subset
  obtain ⟨f, hf, function, included⟩ := M.uniformize_relation pairing unions powers separation choice
    hS (M.prod_mem pairing unions powers separation hV hV)
    (M.taskBearingSuccessorRelation_ground pairing unions powers separation infinite hS hV hK hLabels hC hD hrD)
    (by
      intro source hs
      obtain ⟨target, ht, z, hz, code⟩ := total source hs
      exact ⟨ZFSet.pair target z, ZFSet.pair_mem_prod.2 ⟨subset ht, hz⟩,
        (entries source target z).2 ⟨hs, ht, hz, code⟩⟩)
  exact ⟨f, hf, function, included, fun source target z entry =>
    ((entries source target z).1 (included entry)).2⟩

end TransitiveGround
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_groundOmegaOneTaskBearingSuccessorFunction {K D rD c : ZFSet.{u}}
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD) (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) (level : GroundMainCandidateLevel M K) :
    ∃ f ∈ M.sets,
      ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K C C D rD)
        (ZFSet.prod level.carrier level.carrier) f ∧
      f ⊆ M.taskBearingSuccessorRelation
        (M.linkedMainStageCandidates level.carrier K C C D rD) level.carrier K C C D rD ∧
      ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
        target ∈ M.linkedMainStageCandidates level.carrier K C C D rD ∧ z ∈ level.carrier ∧
          TaskBearingMainSuccessorCode M K C C D rD ZFSet.omega source target z := by
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have hS := M.linkedMainStageCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hC hC hD hrD standard.1.1
  apply M.choose_taskBearingSuccessors pairing unions powers separation collection infinite choice
    hS level.carrier_ground hK hC hC hD hrD standard.1.1
  · intro s hs
    exact ((M.mem_linkedMainStageCandidates level.carrier K C C D rD s).1 hs).1
  · intro s hs
    exact M.omegaOne_taskBearingSuccessor_total pairing unions powers separation collection infinite choice
      hK standard hc dense above coordinateInjection level hs

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixPreservedSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source middle target first second : GroundChronologicalMainStage M C D rD}

theorem retargetEq_preservesOldProfiles_iff
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).PreservesOldProfiles ↔ transition.PreservesOldProfiles := by
  cases sourceEqual
  cases targetEqual
  rfl

end GroundChronologicalMainTransition

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLinkedProfilePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target chosenSource chosenTarget : GroundLinkedMainStage M K Labels C D rD}

theorem retargetLinked_preservesOldProfiles_iff
    (transition : GroundChronologicalMainTransition source.main target.main)
    (sourceCode : source.code = chosenSource.code) (targetCode : target.code = chosenTarget.code) :
    (transition.retargetLinked sourceCode targetCode).PreservesOldProfiles ↔
      transition.PreservesOldProfiles := by
  have first := source.same_code chosenSource sourceCode
  have second := target.same_code chosenTarget targetCode
  change OldProfilePreservationCode chosenSource.main.stage.carrier chosenSource.main.stage.order
    chosenSource.main.stage.meetGraph chosenTarget.main.stage.carrier chosenTarget.main.stage.order
    chosenTarget.main.stage.meetGraph transition.map.points (M.groundPower chosenSource.main.stage.carrier) ↔ _
  rw [← first.stage, ← second.stage]
  rfl

theorem preservesOldProfiles_iff_of_map_code
    (first second : GroundChronologicalMainTransition source.main target.main)
    (equal : first.map.code = second.map.code) :
    first.PreservesOldProfiles ↔ second.PreservesOldProfiles := by
  have points : first.map.points = second.map.points := (ZFSet.pair_inj.1 equal).1
  unfold PreservesOldProfiles
  rw [points]

end GroundChronologicalMainTransition

namespace LinkedProfilePreservingTransitionCode
variable {M : TransitiveGround.{u}} {K Labels C D rD a b z : ZFSet.{u}}

theorem exists_at (source target : GroundLinkedMainStage M K Labels C D rD)
    (code : LinkedProfilePreservingTransitionCode M K Labels C D rD source.code target.code z) :
    ∃ transition : GroundChronologicalMainTransition source.main target.main,
      transition.map.code = z ∧ transition.CoversOldBirths ∧ transition.PreservesOldProfiles := by
  obtain ⟨first, second, sourceCode, targetCode, transition, equal, covered, preserved⟩ := code
  exact ⟨transition.retargetLinked sourceCode targetCode,
    (transition.retargetLinked_code sourceCode targetCode).trans equal,
    transition.retargetLinked_coversOldBirths sourceCode targetCode covered,
    (transition.retargetLinked_preservesOldProfiles_iff sourceCode targetCode).2 preserved⟩

theorem preserves_at {source target : GroundLinkedMainStage M K Labels C D rD}
    (transition : GroundChronologicalMainTransition source.main target.main)
    (code : LinkedProfilePreservingTransitionCode M K Labels C D rD
      source.code target.code transition.map.code) : transition.PreservesOldProfiles := by
  obtain ⟨chosen, equal, _, preserved⟩ := code.exists_at source target
  exact (chosen.preservesOldProfiles_iff_of_map_code transition equal).1 preserved

end LinkedProfilePreservingTransitionCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_MainPrefixHistoryUnionRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u v

namespace MainPrefixGraphFamily
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)

theorem indexUnion_mem (x : ZFSet.{u}) : x ∈ family.indexUnion ↔ ∃ i, x ∈ family.indices i :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem stageUnion_mem (x : ZFSet.{u}) : x ∈ family.stageUnion ↔ ∃ i, x ∈ family.stages i :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem transitionUnion_mem (x : ZFSet.{u}) :
    x ∈ family.transitionUnion ↔ ∃ i, x ∈ family.transitions i :=
  familyCodeGraph_valueUnion_mem_iff _ x

theorem indexUnion_ordinal : ordinalSetProperty family.indexUnion := by
  apply ordinalSetProperty_sUnion
  intro T hT
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hT
  exact (family.valid i).ordinal

omit [Small.{u} I] in
theorem common_upper (i j : I) :
    ∃ k, family.indices i ⊆ family.indices k ∧ family.indices j ⊆ family.indices k := by
  have first := ordinalSetProperty_eq_code_rank (family.indices i) (family.valid i).ordinal
  have second := ordinalSetProperty_eq_code_rank (family.indices j) (family.valid j).ordinal
  rcases le_total (ZFSet.rank (family.indices i)) (ZFSet.rank (family.indices j)) with ij | ji
  · refine ⟨j, ?_, fun _ h => h⟩
    have subset := (SetRealization.ordinalCode_subset_iff _ _).2 ij
    simpa only [← first, ← second] using subset
  · refine ⟨i, fun _ h => h, ?_⟩
    have subset := (SetRealization.ordinalCode_subset_iff _ _).2 ji
    simpa only [← first, ← second] using subset

theorem chronologyPairs_indexUnion_mem (x : ZFSet.{u}) :
    x ∈ chronologyPairs family.indexUnion ↔ ∃ i, x ∈ chronologyPairs (family.indices i) := by
  constructor
  · intro hx
    obtain ⟨target, ht, source, _, rfl, before⟩ := (mem_chronologyPairs _ _).1 hx
    obtain ⟨i, hi⟩ := (family.indexUnion_mem target).1 ht
    have sourceMem : source ∈ family.indices i := by
      rcases before with rfl | before
      · exact hi
      · exact (family.valid i).ordinal.1 target hi source before
    exact ⟨i, (pair_mem_chronologyPairs _ _ _).2 ⟨hi, sourceMem, before⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨target, ht, source, hs, rfl, before⟩ := (mem_chronologyPairs _ _).1 hi
    exact (pair_mem_chronologyPairs _ _ _).2
      ⟨(family.indexUnion_mem target).2 ⟨i, ht⟩, (family.indexUnion_mem source).2 ⟨i, hs⟩, before⟩

theorem stageUnion_function : FunctionGraphOn family.indexUnion family.stageUnion := by
  apply functionGraphOn_sUnion
  · intro f hf
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hf
    exact ⟨family.indices i, fun x hx => (family.indexUnion_mem x).2 ⟨i, hx⟩, (family.valid i).stages⟩
  · intro x hx
    obtain ⟨i, hi⟩ := (family.indexUnion_mem x).1 hx
    obtain ⟨y, entry⟩ := (family.valid i).stages.total hi
    exact ⟨family.stages i, ZFSet.mem_range.2 ⟨i, rfl⟩, y, entry⟩
  · intro f hf g hg x y z first second
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hf
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hg
    obtain ⟨k, ik, jk⟩ := family.common_upper i j
    exact (family.valid k).stages.unique ((family.mono i k ik).1 first) ((family.mono j k jk).1 second)

theorem transitionUnion_function :
    FunctionGraphOn (chronologyPairs family.indexUnion) family.transitionUnion := by
  apply functionGraphOn_sUnion
  · intro f hf
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hf
    exact ⟨chronologyPairs (family.indices i),
      fun x hx => (family.chronologyPairs_indexUnion_mem x).2 ⟨i, hx⟩, (family.valid i).transitions⟩
  · intro x hx
    obtain ⟨i, hi⟩ := (family.chronologyPairs_indexUnion_mem x).1 hx
    obtain ⟨y, entry⟩ := (family.valid i).transitions.total hi
    exact ⟨family.transitions i, ZFSet.mem_range.2 ⟨i, rfl⟩, y, entry⟩
  · intro f hf g hg x y z first second
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hf
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hg
    obtain ⟨k, ik, jk⟩ := family.common_upper i j
    exact (family.valid k).transitions.unique
      ((family.mono i k ik).2 first) ((family.mono j k jk).2 second)

theorem stageUnion_restrict (i : I) :
    graphRestriction (family.indices i) family.stageUnion = family.stages i := by
  apply (family.stageUnion_function.restrict
    (fun x hx => (family.indexUnion_mem x).2 ⟨i, hx⟩)).eq_of_agree (family.valid i).stages
  intro x y z first second
  exact family.stageUnion_function.unique (pair_mem_graphRestriction.1 first).1
    ((family.stageUnion_mem _).2 ⟨i, second⟩)

theorem union_valid :
    MainPrefixGraphCode M K Labels C D rD family.indexUnion family.stageUnion family.transitionUnion := by
  refine ⟨family.indexUnion_ordinal, family.stageUnion_function, family.transitionUnion_function,
    ?_, ?_, ?_, ?_⟩
  · intro i a entry
    obtain ⟨k, hk⟩ := (family.stageUnion_mem _).1 entry
    exact (family.valid k).stage_valid i a hk
  · intro i j a b z first second step
    obtain ⟨k, hk⟩ := (family.transitionUnion_mem _).1 step
    have indices := (pair_mem_chronologyPairs _ _ _).1 ((family.valid k).transitions.pair_source hk)
    have firstOld : ZFSet.pair i a ∈ family.stages k := by
      rw [← family.stageUnion_restrict k]
      exact pair_mem_graphRestriction.2 ⟨first, indices.2.1⟩
    have secondOld : ZFSet.pair j b ∈ family.stages k := by
      rw [← family.stageUnion_restrict k]
      exact pair_mem_graphRestriction.2 ⟨second, indices.1⟩
    exact (family.valid k).transition_valid i j a b z firstOld secondOld hk
  · intro i p a entry
    obtain ⟨k, hk⟩ := (family.transitionUnion_mem _).1 entry
    exact (family.valid k).identity i p a hk
  · intro i j k p₁ a₁ p₂ a₂ p₃ a₃ first second third
    obtain ⟨b, hb⟩ := (family.transitionUnion_mem _).1 first
    obtain ⟨c, hc⟩ := (family.transitionUnion_mem _).1 second
    obtain ⟨d, hd⟩ := (family.transitionUnion_mem _).1 third
    obtain ⟨e, be, ce⟩ := family.common_upper b c
    obtain ⟨f, ef, df⟩ := family.common_upper e d
    exact (family.valid f).composition i j k p₁ a₁ p₂ a₂ p₃ a₃
      ((family.mono e f ef).2 ((family.mono b e be).2 hb))
      ((family.mono e f ef).2 ((family.mono c e ce).2 hc)) ((family.mono d f df).2 hd)

end MainPrefixGraphFamily

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.MainPrefixGraphFamily
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (key : I → ZFSet.{u}) (injective : Function.Injective key)
variable (domain : ZFSet.range key ∈ M.sets)
variable (whole : familyCodeGraph key family.code ∈ M.sets)
include pairing unions powers separation injective domain whole

theorem fieldFamilies_ground :
    familyCodeGraph key family.indices ∈ M.sets ∧ familyCodeGraph key family.stages ∈ M.sets ∧
      familyCodeGraph key family.transitions ∈ M.sets := by
  have encoded : familyCodeGraph key (fun i => ZFSet.pair (family.indices i)
      (ZFSet.pair (family.stages i) (family.transitions i))) ∈ M.sets := by
    change familyCodeGraph key family.code ∈ M.sets
    exact whole
  have first := M.familyCodeGraph_pair_projections pairing unions powers separation key family.indices
    (fun i => ZFSet.pair (family.stages i) (family.transitions i)) injective domain encoded
  have second := M.familyCodeGraph_pair_projections pairing unions powers separation key family.stages
    family.transitions injective domain first.2
  exact ⟨first.1, second.1, second.2⟩

theorem fieldRanges_ground :
    ZFSet.range family.indices ∈ M.sets ∧ ZFSet.range family.stages ∈ M.sets ∧
      ZFSet.range family.transitions ∈ M.sets := by
  have fields := family.fieldFamilies_ground pairing unions powers separation key injective domain whole
  exact ⟨M.familyCodeGraph_valueRange_mem unions separation key family.indices domain fields.1,
    M.familyCodeGraph_valueRange_mem unions separation key family.stages domain fields.2.1,
    M.familyCodeGraph_valueRange_mem unions separation key family.transitions domain fields.2.2⟩

theorem fieldUnions_ground :
    family.indexUnion ∈ M.sets ∧ family.stageUnion ∈ M.sets ∧ family.transitionUnion ∈ M.sets := by
  have ranges := family.fieldRanges_ground pairing unions powers separation key injective domain whole
  exact ⟨M.union_mem unions ranges.1, M.union_mem unions ranges.2.1, M.union_mem unions ranges.2.2⟩

theorem unionCode_ground : family.unionCode ∈ M.sets := by
  have grounds := family.fieldUnions_ground pairing unions powers separation key injective domain whole
  exact M.mainPrefixCode_mem pairing grounds.1 grounds.2.1 grounds.2.2

omit pairing unions powers separation injective domain whole in
theorem code_extends_union (i : I) : MainPrefixExtends (family.code i) family.unionCode := by
  apply mainPrefixExtends_iff.2
  exact ⟨fun x hx => (family.indexUnion_mem x).2 ⟨i, hx⟩,
    fun x hx => (family.stageUnion_mem x).2 ⟨i, hx⟩,
    fun x hx => (family.transitionUnion_mem x).2 ⟨i, hx⟩⟩

end PartitionPilot.Forcing.MainPrefixGraphFamily



namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem preservesOldProfiles_of_graph_code
    (code : MainPrefixProfileGraphCode M K Labels C D rD run.stageGraph run.transitionGraph) :
    run.PreservesOldProfiles := by
  intro i j before
  have entry := code (run.key i) (run.key j) (run.linked i).code (run.linked j).code
    (run.diagram.transition before).map.code
    ((run.stageGraph_entry i _).2 rfl) ((run.stageGraph_entry j _).2 rfl)
    ((run.transitionGraph_entry before _).2 rfl)
  let step := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have stepCode : step.map.code = (run.diagram.transition before).map.code :=
    (run.diagram.transition before).retargetEq_code (run.linked_main i).symm (run.linked_main j).symm
  have actual : LinkedProfilePreservingTransitionCode M K Labels C D rD
      (run.linked i).code (run.linked j).code step.map.code := stepCode.symm ▸ entry
  exact ((run.diagram.transition before).retargetEq_preservesOldProfiles_iff
    (run.linked_main i).symm (run.linked_main j).symm).1 (actual.preserves_at step)

end GroundMainPrefix

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.MainPrefixGraphFamily
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)

theorem union_profile_graph_code
    (preserved : ∀ k, MainPrefixProfileGraphCode M K Labels C D rD (family.stages k) (family.transitions k)) :
    MainPrefixProfileGraphCode M K Labels C D rD family.stageUnion family.transitionUnion := by
  intro i j a b z first second entry
  obtain ⟨k, hk⟩ := (family.transitionUnion_mem _).1 entry
  have indices := (pair_mem_chronologyPairs _ _ _).1 ((family.valid k).transitions.pair_source hk)
  have firstOld : ZFSet.pair i a ∈ family.stages k := by
    rw [← family.stageUnion_restrict k]
    exact pair_mem_graphRestriction.2 ⟨first, indices.2.1⟩
  have secondOld : ZFSet.pair j b ∈ family.stages k := by
    rw [← family.stageUnion_restrict k]
    exact pair_mem_graphRestriction.2 ⟨second, indices.1⟩
  exact preserved k i j a b z firstOld secondOld hk

end PartitionPilot.Forcing.MainPrefixGraphFamily



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

namespace PreservedMainPrefixCode
variable {M : TransitiveGround.{u}} {K Labels C D rD z : ZFSet.{u}}

theorem exists_decodedPrefix (code : PreservedMainPrefixCode M K Labels C D rD z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : z ∈ M.sets) :
    ∃ T ∈ M.sets, ∃ ordinal : ordinalSetProperty T,
      letI := ordinalMainIndexPreorder ordinal
      ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T),
        run.indices = T ∧ run.code = z ∧ run.PreservesOldProfiles := by
  obtain ⟨T, S, E, equal, raw, preserved⟩ := code
  obtain ⟨hT, hS, hE⟩ := M.mainPrefixCode_fields_mem (equal ▸ ground)
  let := ordinalMainIndexPreorder raw.ordinal
  let run := raw.decodedPrefix pairing unions powers separation hT hS hE
  refine ⟨T, hT, raw.ordinal, run,
    raw.decodedPrefix_indices pairing unions powers separation hT hS hE,
    (raw.decodedPrefix_code pairing unions powers separation hT hS hE).trans equal.symm, ?_⟩
  apply run.preservesOldProfiles_of_graph_code
  change MainPrefixProfileGraphCode M K Labels C D rD
    (raw.decodedPrefix pairing unions powers separation hT hS hE).stageGraph
    (raw.decodedPrefix pairing unions powers separation hT hS hE).transitionGraph
  rw [raw.decodedPrefix_stageGraph, raw.decodedPrefix_transitionGraph]
  exact preserved

end PreservedMainPrefixCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

namespace PreservedMainPrefixHistoryCode
variable {M : TransitiveGround.{u}} {K Labels C D rD A p : ZFSet.{u}}
variable (history : PreservedMainPrefixHistoryCode M K Labels C D rD A p)

theorem graphFamily_code_entry (i : SetMembers A) :
    ZFSet.pair (SetMembers.raw i) (history.graphFamily.code i) ∈ p := by
  change ZFSet.pair (SetMembers.raw i)
    (mainPrefixCode (insert (SetMembers.raw i) (SetMembers.raw i))
      (history.fields i).1 (history.fields i).2) ∈ p
  rw [← (history.fields_spec i).1]
  exact decodedFamilyValue_entry history.function i

theorem graphFamily_codeGraph_eq :
    familyCodeGraph (@SetMembers.raw A) history.graphFamily.code = p :=
  familyCodeGraph_eq_of_entries history.function _ _ (ordinalMainIndex_key_range A)
    history.graphFamily_code_entry

theorem graphFamily_profiles (i : SetMembers A) :
    MainPrefixProfileGraphCode M K Labels C D rD
      (history.graphFamily.stages i) (history.graphFamily.transitions i) :=
  (history.fields_spec i).2.2

theorem graphFamily_indexUnion (ordinal : ordinalSetProperty A) :
    history.graphFamily.indexUnion = A := by
  apply ZFSet.ext
  intro x
  rw [history.graphFamily.indexUnion_mem]
  constructor
  · rintro ⟨i, hi⟩
    rcases ZFSet.mem_insert_iff.1 hi with equal | below
    · exact equal.symm ▸ SetMembers.raw_mem i
    · exact ordinal.1 _ (SetMembers.raw_mem i) x below
  · intro hx
    refine ⟨SetMembers.ofMem x hx, ?_⟩
    change x ∈ insert (SetMembers.raw (SetMembers.ofMem x hx)) (SetMembers.raw (SetMembers.ofMem x hx))
    rw [SetMembers.raw_ofMem]
    exact ZFSet.mem_insert_iff.2 (Or.inl rfl)

end PreservedMainPrefixHistoryCode





theorem MainPrefixHistoryUnionCode.unique {p q r : ZFSet.{u}}
    (first : MainPrefixHistoryUnionCode p q) (second : MainPrefixHistoryUnionCode p r) : q = r := by
  obtain ⟨T, S, E, rfl, fields⟩ := first
  obtain ⟨U, F, G, rfl, fields'⟩ := second
  apply mainPrefixCode_inj.2
  exact ⟨ZFSet.ext (fun x => (fields 0 x).trans (fields' 0 x).symm),
    ZFSet.ext (fun x => (fields 1 x).trans (fields' 1 x).symm),
    ZFSet.ext (fun x => (fields 2 x).trans (fields' 2 x).symm)⟩

namespace PreservedMainPrefixHistoryCode
variable {M : TransitiveGround.{u}} {K Labels C D rD A p : ZFSet.{u}}
variable (history : PreservedMainPrefixHistoryCode M K Labels C D rD A p)

theorem field_mem_iff (j : Fin 3) (x : ZFSet.{u}) :
    MainPrefixHistoryFieldMem p x j ↔
      ∃ i : SetMembers A, x ∈ (Fin.cases (history.graphFamily.indices i)
        (Fin.cases (history.graphFamily.stages i) (fun _ => history.graphFamily.transitions i)) :
          Fin 3 → ZFSet.{u}) j := by
  constructor
  · rintro ⟨i, T, S, E, entry, member⟩
    have hi := history.function.pair_source entry
    let k := SetMembers.ofMem i hi
    have actual : ZFSet.pair i (history.graphFamily.code k) ∈ p := by
      have actual := history.graphFamily_code_entry k
      simpa only [k, SetMembers.raw_ofMem] using actual
    have equal := history.function.unique entry actual
    have fields := mainPrefixCode_inj.1 equal
    refine ⟨k, ?_⟩
    rw [fields.1, fields.2.1, fields.2.2] at member
    exact member
  · rintro ⟨i, member⟩
    exact ⟨SetMembers.raw i, history.graphFamily.indices i, history.graphFamily.stages i,
      history.graphFamily.transitions i, history.graphFamily_code_entry i, member⟩

theorem union_code : MainPrefixHistoryUnionCode p history.graphFamily.unionCode := by
  refine ⟨history.graphFamily.indexUnion, history.graphFamily.stageUnion,
    history.graphFamily.transitionUnion, rfl, ?_⟩
  intro j
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) j
  · intro x
    exact (history.graphFamily.indexUnion_mem x).trans (history.field_mem_iff 0 x).symm
  · intro x
    exact (history.graphFamily.stageUnion_mem x).trans (history.field_mem_iff 1 x).symm
  · intro x
    exact (history.graphFamily.transitionUnion_mem x).trans (history.field_mem_iff 2 x).symm

end PreservedMainPrefixHistoryCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mainPrefixHistoryFieldMem_ground {p x : ZFSet.{u}} {j : Fin 3}
    (hp : p ∈ M.sets) (member : MainPrefixHistoryFieldMem p x j) : x ∈ M.sets := by
  obtain ⟨i, T, S, E, entry, member⟩ := member
  have fields := M.mainPrefixCode_fields_mem (M.pair_right (M.transitive hp entry))
  have ground : ∀ k, (Fin.cases T (Fin.cases S (fun _ => E)) : Fin 3 → ZFSet.{u}) k ∈ M.sets :=
    Fin.cases fields.1 (Fin.cases fields.2.1 (fun _ => fields.2.2))
  exact M.transitive (ground j) member

theorem realize_mainPrefixHistoryFieldMemFormula {n} (p x : Fin n) (j : Fin 3)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (mainPrefixHistoryFieldMemFormula p x j) env ↔
      MainPrefixHistoryFieldMem (env p) (env x) j := by
  rw [mainPrefixHistoryFieldMemFormula, realize_exBlock]
  let old := suffixIndex n 5
  let field := prefixIndex n 5
  let selected : Fin 3 → Fin (n + 5) := Fin.cases (field 1) (Fin.cases (field 2) (fun _ => field 3))
  have actual (f : Fin 5 → ZFSet.{u}) (ground : ∀ k, f k ∈ M.sets) :
      Realize M.sets (BoundedFormula.conj
        (BoundedFormula.pairMembershipFormula (field 0) (field 4) (old p))
        (.conj (BoundedFormula.mainPrefixTupleFormula (field 4) (field 1) (field 2) (field 3))
          (.mem (old x) (selected j)))).toFormula (extendMany 5 f env) ↔
      ZFSet.pair (f 0) (f 4) ∈ env p ∧ f 4 = mainPrefixCode (f 1) (f 2) (f 3) ∧
        env x ∈ (Fin.cases (f 1) (Fin.cases (f 2) (fun _ => f 3)) : Fin 3 → ZFSet.{u}) j := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_pairMembershipFormula,
      BoundedFormula.truth_mainPrefixTupleFormula, old, field, extendMany_prefix, extendMany_suffix]
    refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) j <;> rfl
  constructor
  · rintro ⟨f, ground, recognized⟩
    obtain ⟨entry, equal, member⟩ := (actual f ground).1 recognized
    exact ⟨f 0, f 1, f 2, f 3, equal ▸ entry, member⟩
  · rintro ⟨i, T, S, E, entry, member⟩
    have pairGround := M.transitive (members p) entry
    have fieldsGround := M.mainPrefixCode_fields_mem (M.pair_right pairGround)
    let f : Fin 5 → ZFSet.{u} := Fin.cases i (Fin.cases T (Fin.cases S
      (Fin.cases E (fun _ => mainPrefixCode T S E))))
    have ground : ∀ k, f k ∈ M.sets := Fin.cases (M.pair_left pairGround)
      (Fin.cases fieldsGround.1 (Fin.cases fieldsGround.2.1
        (Fin.cases fieldsGround.2.2 (fun _ => M.pair_right pairGround))))
    exact ⟨f, ground, (actual f ground).2 ⟨entry, rfl, member⟩⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

theorem MainPrefixAtIndex.unique {T U q : ZFSet.{u}}
    (first : MainPrefixAtIndex T q) (second : MainPrefixAtIndex U q) : T = U := by
  obtain ⟨S, E, a⟩ := first
  obtain ⟨F, G, b⟩ := second
  exact (mainPrefixCode_inj.1 (a.symm.trans b)).1

theorem MainPrefixAtIndex.refl {T q : ZFSet.{u}} (code : MainPrefixAtIndex T q) :
    MainPrefixExtends q q := by
  obtain ⟨S, E, rfl⟩ := code
  exact MainPrefixExtends.refl T S E

theorem MainPrefixTraceStepCode.unique {B seed g α p y z : ZFSet.{u}}
    (function : FunctionGraphOn B g)
    (first : MainPrefixTraceStepCode B seed g α p y)
    (second : MainPrefixTraceStepCode B seed g α p z) : y = z := by
  rcases first.2.2.2 with ⟨zero, hy⟩ | ⟨nonzero, a, unionA, entryA⟩
  · rcases second.2.2.2 with ⟨_, hz⟩ | ⟨nonzero, _⟩
    · exact hy.trans hz.symm
    · exact False.elim (nonzero zero)
  · rcases second.2.2.2 with ⟨zero, _⟩ | ⟨_, b, unionB, entryB⟩
    · exact False.elim (nonzero zero)
    · have equal := unionA.unique unionB
      exact function.unique entryA (equal.symm ▸ entryB)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixHistoryFieldUnionFormula {n} (p output : Fin n) (j : Fin 3)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (mainPrefixHistoryFieldUnionFormula p output j) env ↔
      ∀ x, x ∈ env output ↔ MainPrefixHistoryFieldMem (env p) x j := by
  change (∀ x ∈ M.sets, Realize M.sets
    (.conj (imp (.mem 0 output.succ) (mainPrefixHistoryFieldMemFormula p.succ 0 j))
      (imp (mainPrefixHistoryFieldMemFormula p.succ 0 j) (.mem 0 output.succ))) (extend x env)) ↔ _
  simp only [Realize, realize_imp]
  have meaning (x : ZFSet.{u}) (hx : x ∈ M.sets) :
      Realize M.sets (mainPrefixHistoryFieldMemFormula p.succ 0 j) (extend x env) ↔
        MainPrefixHistoryFieldMem (env p) x j :=
    M.realize_mainPrefixHistoryFieldMemFormula p.succ 0 j (extend x env) (Fin.cases hx members)
  constructor
  · intro recognized x
    constructor
    · intro member
      have hx := M.transitive (members output) member
      exact (meaning x hx).1 ((recognized x hx).1 member)
    · intro member
      have hx := M.mainPrefixHistoryFieldMem_ground (members p) member
      exact (recognized x hx).2 ((meaning x hx).2 member)
  · intro exactFields x hx
    exact ⟨fun member => (meaning x hx).2 ((exactFields x).1 member),
      fun recognized => (exactFields x).2 ((meaning x hx).1 recognized)⟩

theorem realize_mainPrefixHistoryUnionFormula {n} (p q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (mainPrefixHistoryUnionFormula p q) env ↔
      MainPrefixHistoryUnionCode (env p) (env q) := by
  rw [mainPrefixHistoryUnionFormula, realize_exBlock]
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ k, f k ∈ M.sets) :
      (Realize M.sets (BoundedFormula.mainPrefixTupleFormula (old q) (field 0) (field 1) (field 2)).toFormula
          (extendMany 3 f env) ∧
        Realize M.sets (conjBlock 3 (fun j => mainPrefixHistoryFieldUnionFormula (old p) (field j) j))
          (extendMany 3 f env)) ↔
      env q = mainPrefixCode (f 0) (f 1) (f 2) ∧
        ∀ j x, x ∈ f j ↔ MainPrefixHistoryFieldMem (env p) x j := by
    have mems := extendMany_members 3 f env ground members
    rw [BoundedFormula.realize_mainPrefixTupleFormula M _ _ _ _ _ mems, realize_conjBlock]
    apply and_congr
    · simp only [old, field, extendMany_prefix, extendMany_suffix]
    · apply forall_congr'
      intro j
      simpa only [old, field, extendMany_prefix, extendMany_suffix] using
        M.realize_mainPrefixHistoryFieldUnionFormula (old p) (field j) j (extendMany 3 f env) mems
  constructor
  · rintro ⟨f, ground, recognized⟩
    obtain ⟨encoded, fields⟩ := (actual f ground).1 recognized
    have same : (Fin.cases (f 0) (Fin.cases (f 1) (fun _ => f 2)) : Fin 3 → ZFSet.{u}) = f := by
      funext j
      refine Fin.cases rfl (Fin.cases rfl (fun k => ?_)) j
      rw [Fin.eq_zero k]
      rfl
    refine ⟨f 0, f 1, f 2, encoded, ?_⟩
    rw [same]
    exact fields
  · rintro ⟨T, S, E, encoded, fields⟩
    have grounds := M.mainPrefixCode_fields_mem (encoded ▸ members q)
    let f : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have ground : ∀ k, f k ∈ M.sets := Fin.cases grounds.1 (Fin.cases grounds.2.1 (fun _ => grounds.2.2))
    exact ⟨f, ground, (actual f ground).2 ⟨encoded, fields⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialPreservedMainPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.MainPrefixGraphFamily
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)

theorem fieldUnions_rank_le_codeRange :
    ZFSet.rank family.indexUnion ≤ ZFSet.rank (ZFSet.range family.code) ∧
      ZFSet.rank family.stageUnion ≤ ZFSet.rank (ZFSet.range family.code) ∧
      ZFSet.rank family.transitionUnion ≤ ZFSet.rank (ZFSet.range family.code) := by
  let entries (i : I) : Fin 3 → ZFSet.{u} :=
    Fin.cases (family.indices i) (Fin.cases (family.stages i) (fun _ => family.transitions i))
  have fields (i : I) (j : Fin 3) :
      ZFSet.rank (entries i j) ≤ ZFSet.rank (family.code i) := by
    simpa only [code, mainPrefixCode, entries] using rank_nonemptyTupleCode_field_le 2
      (Fin.cases (family.indices i) (Fin.cases (family.stages i) (fun _ => family.transitions i))) j
  have bound (value : I → ZFSet.{u}) (ranks : ∀ i, ZFSet.rank (value i) ≤ ZFSet.rank (family.code i)) :
      ZFSet.rank (⋃₀ ZFSet.range value) ≤ ZFSet.rank (ZFSet.range family.code) := by
    apply ZFSet.rank_le_iff.2
    intro x hx
    obtain ⟨i, hi⟩ := (familyCodeGraph_valueUnion_mem_iff value x).1 hx
    exact ((ZFSet.rank_lt_of_mem hi).trans_le (ranks i)).trans
      (ZFSet.rank_lt_of_mem (ZFSet.mem_range.2 ⟨i, rfl⟩))
  refine ⟨bound family.indices ?_, bound family.stages ?_, bound family.transitions ?_⟩
  · intro i
    simpa only [entries, Fin.cases_zero] using fields i 0
  · intro i
    exact fields i 1
  · intro i
    exact fields i 2

theorem unionCode_rank_lt_of_codeRange {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank (ZFSet.range family.code) < o) : ZFSet.rank family.unionCode < o := by
  have fields := family.fieldUnions_rank_le_codeRange
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases (fields.1.trans_lt rank)
      (Fin.cases (fields.2.1.trans_lt rank) (fun _ => fields.2.2.trans_lt rank)))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (hK : K ∈ M.sets)
variable (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
variable (limit : Order.IsSuccLimit (ZFSet.rank K))
variable (key : I → ZFSet.{u}) (injective : Function.Injective key)
variable (domain : ZFSet.range key ∈ M.sets)
variable (whole : familyCodeGraph key family.code ∈ M.sets)
variable (small : GroundBelow M (ZFSet.range key) K)
variable (ranks : ∀ i, ZFSet.rank (family.code i) < ZFSet.rank K)
include pairing unions powers separation collection hK ordinal regular limit injective domain whole small ranks

theorem unionCode_rank_lt_small : ZFSet.rank family.unionCode < ZFSet.rank K :=
  family.unionCode_rank_lt_of_codeRange limit
    (regular.familyCodeGraph_valueRange_rank_lt pairing unions powers separation collection hK ordinal
      key family.code injective domain whole small ranks)

end PartitionPilot.Forcing.MainPrefixGraphFamily

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitIdentity_rank_lt (i : I) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank (run.limitIdentity i) < o :=
  (ZFSet.rank_lt_of_mem (run.limitIdentity_mem i)).trans (run.limitActors_rank_lt limit rank)

end GroundMainPrefix

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitChronology_source_entries (i : I) (j : Fin 5) {t : ZFSet.{u}}
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff) :
    ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ (run.linked i).serial.fields.graph j ↔
      ZFSet.pair s y ∈ run.limitChronologyFields.graph j := by
  intro s hs y
  have earlier : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff := by
    right
    rcases before with rfl | before
    · exact hs
    · exact (run.diagram.stage i).cutoff_ordinal.1 _ before _ hs
  exact (run.limitChronologyFields_source_entries i j earlier y).symm

theorem limitChronology_raw_witnesses (hOmega : ZFSet.omega ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank run.code < o)
    (numbers : ZFSet.rank ZFSet.omega < o) :
    ∀ s ∈ insert run.cutoffLimit run.cutoffLimit,
      ∀ t ∈ insert run.cutoffLimit run.cutoffLimit, t = s ∨ t ∈ s →
      ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode
        (run.limitChronologyFields.graph 0) (run.limitChronologyFields.graph 1)
        (run.limitChronologyFields.graph 2) (run.limitChronologyFields.value 0 s)
        (run.limitChronologyFields.value 1 s) (run.limitChronologyFields.value 2 s)
        (run.limitChronologyFields.value 3 s) t ZFSet.omega z := by
  intro s hs t _ before
  rcases ZFSet.mem_insert_iff.1 hs with rfl | hs
  · rw [run.limitChronologyFields_terminal 0, run.limitChronologyFields_terminal 1,
      run.limitChronologyFields_terminal 2, run.limitChronologyFields_terminal 3]
    change ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode _ _ _
      run.limitPoints run.limitOrder run.limitMeetGraph run.limitBirth t ZFSet.omega z
    rcases before with rfl | before
    · have hEmpty := M.empty_mem ⟨run.cutoffLimit, run.cutoffLimit_ground⟩
      have emptyRank : ZFSet.rank (∅ : ZFSet.{u}) < o := by
        simpa only [ZFSet.rank_empty] using limit.pos
      refine ⟨countableLayerWitness ∅ ∅, M.countableLayerWitness_mem pairing hEmpty hEmpty,
        countableLayerWitness_rank_lt limit emptyRank emptyRank,
        Or.inl ⟨∅, ∅, rfl, ⟨InjectionCode.empty ZFSet.omega, ?_⟩⟩⟩
      intro x _ birth
      exact (ZFSet.mem_irrefl _ (ZFSet.pair_mem_prod.1 (run.limitBirth_function.1 birth)).2).elim
    · obtain ⟨i, old⟩ := (run.cutoffLimit_mem t).1 before
      obtain ⟨z, hz, code, ranked⟩ := run.limitTerminal_raw_witness_rank_lt i old
        (run.limitChronology_source_entries i 0 old) (run.limitChronology_source_entries i 1 old)
        (run.limitChronology_source_entries i 2 old) hOmega limit rank numbers
      exact ⟨z, hz, ranked, code⟩
  · obtain ⟨i, old⟩ := (run.cutoffLimit_mem s).1 hs
    have oldT : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff := by
      rcases before with rfl | before
      · exact old
      · right
        rcases old with rfl | old
        · exact before
        · exact (run.diagram.stage i).cutoff_ordinal.1 _ old _ before
    obtain ⟨z, hz, code, ranked⟩ := run.prior_raw_witness_rank_lt i old before
      (run.limitChronology_source_entries i 0 oldT) (run.limitChronology_source_entries i 1 oldT)
      (run.limitChronology_source_entries i 2 oldT) rank
    rw [run.limitChronologyFields_values i 0 old, run.limitChronologyFields_values i 1 old,
      run.limitChronologyFields_values i 2 old, run.limitChronologyFields_values i 3 old]
    exact ⟨z, hz, ranked, code⟩

end GroundMainPrefix

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_limitSerialization
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K)
    (level : GroundMainCandidateLevel M K) :
    ∃ serial : GroundSerializedChronology M (insert run.cutoffLimit run.cutoffLimit) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
        serial.code ∈ level.validChronologies C D rD ∧
        serial.fields.graph = run.limitChronologyFields.graph ∧
        (∀ j s, serial.fields.value j s = run.limitChronologyFields.value j s) ∧
        serial.layerBound = functionGraphRange
          (chronologyPairs (insert run.cutoffLimit run.cutoffLimit)) serial.layers := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have numbers := standard.omega_mem pairing unions powers separation hK
  exact run.limitChronologyFields.exists_rankedSerialization
    pairing unions powers separation collection infinite choice hK conditions
    (conditions.successor_mem pairing unions powers separation infinite hK
      (run.cutoffLimit_mem_inaccessible hK standard indices))
    level (ordinalSetProperty_succ run.cutoffLimit_ordinal) run.limitChronologyCore
    (run.limitChronologyFields_graph_rank_lt limit rank)
    (run.limitChronology_raw_witnesses (M.transitive hK numbers) limit rank
      (ZFSet.rank_lt_of_mem numbers))

end GroundMainPrefix

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalChronology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_finalChronology
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K)
    (level : GroundMainCandidateLevel M K) : Nonempty (run.FinalChronology level) := by
  obtain ⟨serial, _, codeRank, candidate, graphs, values, attained⟩ :=
    run.exists_limitSerialization collection infinite choice hK standard indices rank level
  exact ⟨⟨serial, codeRank, candidate, graphs, values, attained⟩⟩

namespace FinalChronology
variable {run} {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)

theorem code_ground : chronology.serial.code ∈ M.sets := chronology.serial.code_ground pairing

theorem history_values (s : ZFSet.{u}) :
    chronology.serial.toHistory.space s = run.limitChronologyFields.value 0 s ∧
    chronology.serial.toHistory.order s = run.limitChronologyFields.value 1 s ∧
    chronology.serial.toHistory.meetGraph s = run.limitChronologyFields.value 2 s ∧
    chronology.serial.toHistory.birth s = run.limitChronologyFields.value 3 s ∧
    chronology.serial.toHistory.height s = run.limitChronologyFields.value 4 s :=
  ⟨chronology.values 0 s, chronology.values 1 s, chronology.values 2 s,
    chronology.values 3 s, chronology.values 4 s⟩

theorem terminal_values (i₀ : I) :
    chronology.serial.toHistory.space run.cutoffLimit = (run.finalGeometry i₀).carrier ∧
    chronology.serial.toHistory.order run.cutoffLimit = (run.finalGeometry i₀).order ∧
    chronology.serial.toHistory.meetGraph run.cutoffLimit = (run.finalGeometry i₀).meetGraph ∧
    chronology.serial.toHistory.birth run.cutoffLimit = (run.finalGeometry i₀).birth ∧
    chronology.serial.toHistory.height run.cutoffLimit = (run.finalGeometry i₀).height := by
  obtain ⟨space, order, meet, birth, height⟩ := chronology.history_values run.cutoffLimit
  exact ⟨space.trans (run.limitChronologyFields_terminal 0),
    order.trans (run.limitChronologyFields_terminal 1), meet.trans (run.limitChronologyFields_terminal 2),
    birth.trans (run.limitChronologyFields_terminal 3), height.trans (run.limitChronologyFields_terminal 4)⟩

end FinalChronology

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalRowTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

namespace TransitiveGround
variable (M)

theorem groundOmegaOne_member_countable {A : ZFSet.{u}}
    (member : A ∈ M.groundOmegaOne pairing unions powers separation collection infinite) :
    M.groundEmbeddable A ZFSet.omega :=
  ((M.groundOmegaOne_spec pairing unions powers separation collection infinite).2.2.1 A).1 member |>.2.2

end TransitiveGround

namespace GroundStandardInaccessible
variable {K : ZFSet.{u}} (standard : GroundStandardInaccessible M K)
include standard

theorem groundOmegaOne_mem (hK : K ∈ M.sets) :
    M.groundOmegaOne pairing unions powers separation collection infinite ∈ K :=
  (standard.to_conditions pairing unions powers separation hK).groundOmegaOne_mem
    pairing unions powers separation collection infinite hK

end GroundStandardInaccessible
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem finalGeometry_fields_rank_lt (i₀ : I) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ∀ j, ZFSet.rank ((run.finalGeometry i₀).fields j) < o :=
  Fin.cases (run.limitPoints_rank_lt limit rank) (Fin.cases (run.limitOrder_rank_lt limit rank)
    (Fin.cases (run.limitMeetGraph_rank_lt limit rank) (Fin.cases (run.limitActors_rank_lt limit rank)
      (Fin.cases (run.limitMultiplication_rank_lt limit rank) (Fin.cases (run.limitInverse_rank_lt limit rank)
        (Fin.cases (run.limitIdentity_rank_lt i₀ limit rank) (Fin.cases (run.limitAction_rank_lt limit rank)
          (Fin.cases (run.limitBottom_rank_lt limit rank i₀) (Fin.cases (run.limitHeight_rank_lt limit rank)
            (Fin.cases (run.limitBirth_rank_lt limit rank) (fun _ => run.cutoffLimit_rank_le_code.trans_lt rank)))))))))))

theorem finalGeometry_code_rank_lt (i₀ : I) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) : ZFSet.rank (run.finalGeometry i₀).code < o :=
  rank_nonemptyTupleCode_lt limit 11 _ (run.finalGeometry_fields_rank_lt i₀ limit rank)

theorem finalInclusions_rank_lt (i₀ : I) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) :
    ZFSet.rank (run.finalInclusions i₀).pointFamily < o ∧
    ZFSet.rank (run.finalInclusions i₀).actorFamily < o ∧
    ∀ i, ZFSet.rank ((run.finalInclusions i₀).pointMap i) < o ∧
      ZFSet.rank ((run.finalInclusions i₀).actorMap i) < o :=
  ⟨run.limitPointInclusions_rank_lt limit rank, run.limitActorInclusions_rank_lt limit rank,
    fun i => ⟨run.limitPointMap_rank_lt limit rank i, run.limitActorMap_rank_lt limit rank i⟩⟩

theorem finalGeometry_below (i₀ : I) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    GroundBelow M (run.finalGeometry i₀).carrier K ∧ GroundBelow M (run.finalGeometry i₀).actors K :=
  ⟨run.limitPoints_below choice hK standard indices, run.limitActors_below choice hK standard indices⟩

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixRawCoveredAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitPointMap_later_entry {i j : I} (before : i ≤ j) {x y q : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ (run.diagram.transition before).map.points)
    (image : ZFSet.pair x q ∈ run.limitPointMap i) :
    ZFSet.pair y q ∈ run.limitPointMap j :=
  (run.pointPresentation.inclusion_entry j y q).2
    ⟨(run.pointSystem.map_entry_bounds before entry).2,
      ((run.pointPresentation.inclusion_entry i x q).1 image).2.trans
        (run.pointPresentation.limitPoint_transition before entry)⟩

end GroundMainPrefix

section
open SetFormula SetRealization
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_preservedMainPrefixCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.preservedMainPrefixCandidates B K Labels C D rD ↔
      z ∈ B ∧ PreservedMainPrefixCode M K Labels C D rD z := ZFSet.mem_sep

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem mem_preservedMainPrefixes {Labels C D rD z : ZFSet.{u}} :
    z ∈ level.preservedMainPrefixes Labels C D rD ↔
      z ∈ level.carrier ∧ PreservedMainPrefixCode M K Labels C D rD z :=
  M.mem_preservedMainPrefixCandidates level.carrier K Labels C D rD z

end GroundMainCandidateLevel
end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixSelectedStepTotality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

theorem mainPrefixRecursionIndexCode_iff {Omega T S E : ZFSet.{u}} :
    MainPrefixRecursionIndexCode Omega (mainPrefixCode T S E) ↔ T ∈ Omega ∧ T ≠ ∅ := by
  constructor
  · rintro ⟨T', S', E', equal, member, nonempty⟩
    have same := (mainPrefixCode_inj.1 equal).1
    exact same.symm ▸ ⟨member, nonempty⟩
  · rintro ⟨member, nonempty⟩
    exact ⟨T, S, E, rfl, member, nonempty⟩

end

section
open SetFormula SetRealization
universe u v

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem mem_recursionPrefixes {Omega Labels C D rD z : ZFSet.{u}} :
    z ∈ level.recursionPrefixes Omega Labels C D rD ↔
      z ∈ level.preservedMainPrefixes Labels C D rD ∧ MainPrefixRecursionIndexCode Omega z :=
  ZFSet.mem_sep

end GroundMainCandidateLevel
end

open SetFormula SetRealization
universe u v w

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_MainPrefixConditionalStepCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace MainPrefixConditionalStepCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N f old next : ZFSet.{u}}
variable (code : MainPrefixConditionalStepCode M K Labels C D rD N f old next)
include code

theorem extension : MainPrefixExtends old next := by
  rcases code with selected | ⟨_, _, _, _, _, limit⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, extension, _⟩ := selected
    exact extension
  · exact limit.extension

theorem next_fields {T S E : ZFSet.{u}} (oldCode : old = mainPrefixCode T S E) :
    ∃ S' E', next = mainPrefixCode (insert T T) S' E' := by
  rcases code with selected | ⟨_, _, _, _, _, limit⟩
  · obtain ⟨b, F, G, F', G', _, _, _, first, second, _⟩ := selected
    have index := (mainPrefixCode_inj.1 (oldCode.symm.trans first)).1
    exact ⟨F', G', by simpa only [index] using second⟩
  · obtain ⟨_, _, _, T', S', E', _, nextCode, _⟩ := limit.extension
    exact ⟨S', E', by simpa only [limit.indices_successor oldCode nextCode] using nextCode⟩

theorem selected_of_successor {b S E : ZFSet.{u}}
    (oldCode : old = mainPrefixCode (insert b b) S E) :
    MainPrefixSelectedStepCode f old next := by
  rcases code with selected | ⟨T, F, G, first, limit, _⟩
  · exact selected
  · have index := (mainPrefixCode_inj.1 (oldCode.symm.trans first)).1
    exact False.elim (not_nonzeroLimitOrdinalCode_successor b (index.symm ▸ limit))

end MainPrefixConditionalStepCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PreservedMainPrefixHistoryFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace BoundedFormula

theorem truth_mainPrefixFieldExtensionFormula {n} (T S E T' S' E' : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mainPrefixFieldExtensionFormula T S E T' S' E') env ↔
      env T ⊆ env T' ∧ env S ⊆ env S' ∧ env E ⊆ env E' := by
  simp only [mainPrefixFieldExtensionFormula, Truth, truth_subsetFormula]

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixExtensionFormula {n} (old next : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixExtensionFormula old next) env ↔
      MainPrefixExtends (env old) (env next) := by
  rw [mainPrefixExtensionFormula, realize_exBlock]
  let outer := suffixIndex n 6
  let field := prefixIndex n 6
  have actual (f : Fin 6 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      (Realize M.sets (BoundedFormula.mainPrefixTupleFormula (outer old) (field 0) (field 1) (field 2)).toFormula
        (extendMany 6 f env) ∧
      Realize M.sets (BoundedFormula.mainPrefixTupleFormula (outer next) (field 3) (field 4) (field 5)).toFormula
        (extendMany 6 f env) ∧
      Realize M.sets (BoundedFormula.mainPrefixFieldExtensionFormula
        (field 0) (field 1) (field 2) (field 3) (field 4) (field 5)).toFormula (extendMany 6 f env)) ↔
      env old = mainPrefixCode (f 0) (f 1) (f 2) ∧
        env next = mainPrefixCode (f 3) (f 4) (f 5) ∧ f 0 ⊆ f 3 ∧ f 1 ⊆ f 4 ∧ f 2 ⊆ f 5 := by
    have mems := extendMany_members 6 f env ground members
    rw [BoundedFormula.realize_mainPrefixTupleFormula M _ _ _ _ _ mems,
      BoundedFormula.realize_mainPrefixTupleFormula M _ _ _ _ _ mems,
      BoundedFormula.realize_toFormula M _ _ mems, BoundedFormula.truth_mainPrefixFieldExtensionFormula]
    simp only [outer, field, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, clauses⟩
    have result := (actual f ground).1 clauses
    exact ⟨f 0, f 1, f 2, f 3, f 4, f 5, result⟩
  · rintro ⟨T, S, E, U, F, G, first, second, indices, stages, transitions⟩
    have left := M.mainPrefixCode_fields_mem (first ▸ members old)
    have right := M.mainPrefixCode_fields_mem (second ▸ members next)
    let f : Fin 6 → ZFSet.{u} := Fin.cases T (Fin.cases S (Fin.cases E
      (Fin.cases U (Fin.cases F (fun _ => G)))))
    have ground : ∀ j, f j ∈ M.sets := Fin.cases left.1 (Fin.cases left.2.1
      (Fin.cases left.2.2 (Fin.cases right.1 (Fin.cases right.2.1 (fun _ => right.2.2)))))
    exact ⟨f, ground, (actual f ground).2 ⟨first, second, indices, stages, transitions⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainPrefixTraceStepFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixAtIndexFormula {n} (T q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixAtIndexFormula T q) env ↔ MainPrefixAtIndex (env T) (env q) := by
  rw [mainPrefixAtIndexFormula, realize_exBlock]
  have actual (f : Fin 2 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :=
    BoundedFormula.realize_mainPrefixTupleFormula M (suffixIndex n 2 q)
      (suffixIndex n 2 T) (prefixIndex n 2 0) (prefixIndex n 2 1)
      (extendMany 2 f env) (extendMany_members 2 f env ground members)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f 0, f 1, (actual f ground).1 recognized⟩
  · rintro ⟨S, E, encoded⟩
    have fields := M.mainPrefixCode_fields_mem (encoded ▸ members q)
    let f : Fin 2 → ZFSet.{u} := Fin.cases S (fun _ => E)
    have ground : ∀ j, f j ∈ M.sets := Fin.cases fields.2.1 (fun _ => fields.2.2)
    exact ⟨f, ground, (actual f ground).2 encoded⟩

theorem realize_mainPrefixAtSuccessorFormula {n} (α q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixAtSuccessorFormula α q) env ↔
      MainPrefixAtIndex (insert (env α) (env α)) (env q) := by
  rw [mainPrefixAtSuccessorFormula, realize_ex]
  have actual T (ground : T ∈ M.sets) :
      Realize M.sets (.conj (BoundedFormula.successorFormula 0 α.succ).toFormula
        (mainPrefixAtIndexFormula 0 q.succ)) (extend T env) ↔
      T = insert (env α) (env α) ∧ MainPrefixAtIndex T (env q) := by
    change (_ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases ground members),
      BoundedFormula.truth_successorFormula,
      M.realize_mainPrefixAtIndexFormula _ _ _ (Fin.cases ground members)]
    rfl
  constructor
  · rintro ⟨T, ground, recognized⟩
    obtain ⟨rfl, code⟩ := (actual T ground).1 recognized
    exact code
  · intro code
    obtain ⟨S, E, equal⟩ := code
    have ground := (M.mainPrefixCode_fields_mem (equal ▸ members q)).1
    exact ⟨_, ground, (actual _ ground).2 ⟨rfl, S, E, equal⟩⟩

theorem realize_mainPrefixHistoryExtendsFormula {n} (p q : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixHistoryExtendsFormula p q) env ↔
      MainPrefixHistoryExtends (env p) (env q) := by
  change (∀ i ∈ M.sets, ∀ old ∈ M.sets, Realize M.sets
    (imp (BoundedFormula.pairMembershipFormula 1 0 p.succ.succ).toFormula
      (mainPrefixExtensionFormula 0 q.succ.succ)) (extend old (extend i env))) ↔ _
  have actual i old (hi : i ∈ M.sets) (ho : old ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.pairMembershipFormula 1 0 p.succ.succ).toFormula
          (mainPrefixExtensionFormula 0 q.succ.succ)) (extend old (extend i env)) ↔
      (ZFSet.pair i old ∈ env p → MainPrefixExtends old (env q)) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _ (Fin.cases ho (Fin.cases hi members)),
      BoundedFormula.truth_pairMembershipFormula,
      M.realize_mainPrefixExtensionFormula _ _ _ (Fin.cases ho (Fin.cases hi members))]
    rfl
  constructor
  · intro recognized i old entry
    have pairGround := M.transitive (members p) entry
    exact (actual i old (M.pair_left pairGround) (M.pair_right pairGround)).1
      (recognized i (M.pair_left pairGround) old (M.pair_right pairGround)) entry
  · intro history i hi old ho
    exact (actual i old hi ho).2 (history i old)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixTraceBranchFormula {n} (seed g α p y : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixTraceBranchFormula seed g α p y) env ↔
      ((env α = ∅ ∧ env y = env seed) ∨ (env α ≠ ∅ ∧
        ∃ input, MainPrefixHistoryUnionCode (env p) input ∧ ZFSet.pair input (env y) ∈ env g)) := by
  have empty := (BoundedFormula.realize_toFormula M (BoundedFormula.emptyFormula α) env members).trans
    (BoundedFormula.truth_emptyFormula α env)
  rw [mainPrefixTraceBranchFormula, realize_disj]
  change ((_ ∧ _) ∨ ((¬ _) ∧ _)) ↔ _
  rw [empty]
  apply or_congr Iff.rfl
  apply and_congr Iff.rfl
  rw [realize_ex]
  have actual input (ground : input ∈ M.sets) :
      Realize M.sets (.conj (mainPrefixHistoryUnionFormula p.succ 0)
        (BoundedFormula.pairMembershipFormula 0 y.succ g.succ).toFormula) (extend input env) ↔
      MainPrefixHistoryUnionCode (env p) input ∧ ZFSet.pair input (env y) ∈ env g := by
    change (_ ∧ _) ↔ _
    rw [M.realize_mainPrefixHistoryUnionFormula _ _ _ (Fin.cases ground members),
      BoundedFormula.realize_toFormula M _ _ (Fin.cases ground members),
      BoundedFormula.truth_pairMembershipFormula]
    rfl
  constructor
  · rintro ⟨input, ground, recognized⟩
    exact ⟨input, (actual input ground).1 recognized⟩
  · rintro ⟨input, union, entry⟩
    have ground := M.pair_left (M.transitive (members g) entry)
    exact ⟨input, ground, (actual input ground).2 ⟨union, entry⟩⟩

theorem realize_mainPrefixTraceStepFormula {n} (B seed g α p y : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixTraceStepFormula B seed g α p y) env ↔
      MainPrefixTraceStepCode (env B) (env seed) (env g) (env α) (env p) (env y) := by
  unfold mainPrefixTraceStepFormula MainPrefixTraceStepCode
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  rw [M.realize_mainPrefixAtSuccessorFormula _ _ _ members,
    M.realize_mainPrefixHistoryExtendsFormula _ _ _ members,
    M.realize_mainPrefixTraceBranchFormula _ _ _ _ _ _ members]
  rfl

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTaskBearingRectangles
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u v

namespace TaskBearingMainSuccessorCode
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem rectangles_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    RectangleFulfillmentCode source.main.stage.carrier source.main.stage.actors
      source.main.stage.order source.main.stage.meetGraph source.main.stage.action
      target.main.stage.carrier target.main.stage.actors target.main.stage.order
      target.main.stage.meetGraph target.main.stage.action transition.map.points transition.map.actors := by
  obtain ⟨extra, _, output, _⟩ := code.output_on_linked
  exact output.rectangles

end TaskBearingMainSuccessorCode

namespace GroundMainPrefix
open SetFormula
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem rectangles_of_taskBearing {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code) :
    RectangleFulfillmentCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.actors
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
      (run.diagram.stage i).stage.action (run.diagram.stage j).stage.carrier
      (run.diagram.stage j).stage.actors (run.diagram.stage j).stage.order
      (run.diagram.stage j).stage.meetGraph (run.diagram.stage j).stage.action
      (run.diagram.transition before).map.points (run.diagram.transition before).map.actors := by
  let transition := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code transition.map.code := by
    simpa only [transition, GroundChronologicalMainTransition.retargetEq_code] using code
  have strict := actual.rectangles_on_linked
  simpa only [transition, GroundChronologicalMainTransition.retargetEq_points,
    GroundChronologicalMainTransition.retargetEq_actors,
    run.linked_main i, run.linked_main j] using strict

end GroundMainPrefix
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixRectangleLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem rectangle_data_coverage {c b d X g h : ZFSet.{u}}
    (hc : c ∈ run.limitPoints) (hb : b ∈ run.limitPoints)
    (hd : d ∈ run.limitPoints) (hX : X ∈ run.limitPoints)
    (hg : g ∈ run.limitActors) (hh : h ∈ run.limitActors) :
    ∃ i c₀ b₀ d₀ X₀ g₀ h₀,
      c₀ ∈ (run.diagram.stage i).stage.carrier ∧ b₀ ∈ (run.diagram.stage i).stage.carrier ∧
      d₀ ∈ (run.diagram.stage i).stage.carrier ∧ X₀ ∈ (run.diagram.stage i).stage.carrier ∧
      g₀ ∈ (run.diagram.stage i).stage.actors ∧ h₀ ∈ (run.diagram.stage i).stage.actors ∧
      c = run.pointPresentation.limitPoint i c₀ ∧ b = run.pointPresentation.limitPoint i b₀ ∧
      d = run.pointPresentation.limitPoint i d₀ ∧ X = run.pointPresentation.limitPoint i X₀ ∧
      g = run.actorPresentation.limitPoint i g₀ ∧ h = run.actorPresentation.limitPoint i h₀ := by
  obtain ⟨i, c₀, b₀, d₀, hc₀, hb₀, hd₀, rfl, rfl, rfl⟩ :=
    run.pointPresentation.triple_coverage hc hb hd
  obtain ⟨j, X₀, g₀, h₀, hX₀, hg₀, hh₀, rfl, rfl, rfl⟩ :=
    run.pointPresentation.mixed_triple_coverage run.actorPresentation run.actorPresentation hX hg hh
  obtain ⟨k, ik, jk⟩ := run.common_upper i j
  obtain ⟨c', cc⟩ := run.pointSystem.map_entry_total ik hc₀
  obtain ⟨b', bb⟩ := run.pointSystem.map_entry_total ik hb₀
  obtain ⟨d', dd⟩ := run.pointSystem.map_entry_total ik hd₀
  obtain ⟨X', XX⟩ := run.pointSystem.map_entry_total jk hX₀
  obtain ⟨g', gg⟩ := run.actorSystem.map_entry_total jk hg₀
  obtain ⟨h', hhhh⟩ := run.actorSystem.map_entry_total jk hh₀
  exact ⟨k, c', b', d', X', g', h', (run.pointSystem.map_entry_bounds ik cc).2,
    (run.pointSystem.map_entry_bounds ik bb).2, (run.pointSystem.map_entry_bounds ik dd).2,
    (run.pointSystem.map_entry_bounds jk XX).2, (run.actorSystem.map_entry_bounds jk gg).2,
    (run.actorSystem.map_entry_bounds jk hhhh).2, run.pointPresentation.limitPoint_transition ik cc,
    run.pointPresentation.limitPoint_transition ik bb, run.pointPresentation.limitPoint_transition ik dd,
    run.pointPresentation.limitPoint_transition jk XX, run.actorPresentation.limitPoint_transition jk gg,
    run.actorPresentation.limitPoint_transition jk hhhh⟩

theorem limitMaps_agreement_reflect (i : I) {g h v : ZFSet.{u}}
    (hg : g ∈ (run.diagram.stage i).stage.actors)
    (hh : h ∈ (run.diagram.stage i).stage.actors)
    (hv : v ∈ (run.diagram.stage i).stage.carrier)
    (agree : ActionAgreementBelow run.limitPoints run.limitOrder run.limitAction
      (run.actorPresentation.limitPoint i g) (run.actorPresentation.limitPoint i h)
      (run.pointPresentation.limitPoint i v)) :
    ActionAgreementBelow (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
      (run.diagram.stage i).stage.action g h v := by
  intro x hx y hy lower
  have finalLower := (run.limitOrder_entry _ _).2 ((run.limitLE_at i hx hv).2 lower)
  exact (run.limitAction_at i hg hx hy).symm.trans
    ((agree _ (run.pointPresentation.limitPoint_mem hx) _ (run.pointPresentation.limitPoint_mem hy)
      finalLower).trans (run.limitAction_at i hh hx hy))

theorem limitRectangle_reflect (i : I) {c b d g h : ZFSet.{u}}
    (hc : c ∈ (run.diagram.stage i).stage.carrier)
    (hb : b ∈ (run.diagram.stage i).stage.carrier)
    (hd : d ∈ (run.diagram.stage i).stage.carrier)
    (hg : g ∈ (run.diagram.stage i).stage.actors)
    (hh : h ∈ (run.diagram.stage i).stage.actors)
    (rectangle : ExternalRectangleCode run.limitPoints run.limitActors run.limitOrder
      run.limitMeetGraph run.limitAction (run.pointPresentation.limitPoint i c)
      (run.pointPresentation.limitPoint i b) (run.pointPresentation.limitPoint i d)
      (run.actorPresentation.limitPoint i g) (run.actorPresentation.limitPoint i h)) :
    ExternalRectangleCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.actors
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
      (run.diagram.stage i).stage.action c b d g h := by
  obtain ⟨_, _, _, _, _, cd, bd, W, _, meetW, agree, separated⟩ := rectangle
  obtain ⟨w, meetw, _⟩ := (run.diagram.stage i).stage.meet.operation.2
    (ZFSet.pair c b) (ZFSet.pair_mem_prod.2 ⟨hc, hb⟩)
  have hw := (ZFSet.pair_mem_prod.1 ((run.diagram.stage i).stage.meet.operation.1 meetw)).2
  have equal : W = run.pointPresentation.limitPoint i w := run.limitMeet_unique
    ((run.limitMeetGraph_entry _ _ _).1 meetW) ((run.limitMeet_at i hc hb hw).2 meetw)
  rw [equal] at agree separated
  refine ⟨hc, hb, hd, hg, hh, (run.limitLE_at i hc hd).1 ((run.limitOrder_entry _ _).1 cd),
    (run.limitLE_at i hb hd).1 ((run.limitOrder_entry _ _).1 bd), w, hw, meetw,
    run.limitMaps_agreement_reflect i hg hh hw agree, ?_⟩
  intro y hy z hz v hv actions
  exact (run.limitMeet_at i hy hz hv).1 ((run.limitMeetGraph_entry _ _ _).1
    (separated _ (run.pointPresentation.limitPoint_mem hy) _ (run.pointPresentation.limitPoint_mem hz)
      _ (run.pointPresentation.limitPoint_mem hv)
      ⟨(run.limitAction_at i hg hd hy).2 actions.1, (run.limitAction_at i hh hd hz).2 actions.2.1,
        (run.limitAction_at i hg hw hv).2 actions.2.2⟩))

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainPrefixRectangleBoundTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitRectangleAtBound (i : I) {c b d g h X k l : ZFSet.{u}}
    (hc : c ∈ (run.diagram.stage i).stage.carrier)
    (hb : b ∈ (run.diagram.stage i).stage.carrier)
    (hd : d ∈ (run.diagram.stage i).stage.carrier)
    (hX : X ∈ (run.diagram.stage i).stage.carrier)
    (hg : g ∈ (run.diagram.stage i).stage.actors)
    (hh : h ∈ (run.diagram.stage i).stage.actors)
    (hk : k ∈ (run.diagram.stage i).stage.actors)
    (hl : l ∈ (run.diagram.stage i).stage.actors)
    (code : RectangleAtBoundCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
      (run.diagram.stage i).stage.meetGraph (run.diagram.stage i).stage.action c b d g h X k l) :
    RectangleAtBoundCode run.limitPoints run.limitOrder run.limitMeetGraph run.limitAction
      (run.pointPresentation.limitPoint i c) (run.pointPresentation.limitPoint i b)
      (run.pointPresentation.limitPoint i d) (run.actorPresentation.limitPoint i g)
      (run.actorPresentation.limitPoint i h) (run.pointPresentation.limitPoint i X)
      (run.actorPresentation.limitPoint i k) (run.actorPresentation.limitPoint i l) := by
  have imageC := (run.pointPresentation.inclusion_entry i c _).2 ⟨hc, rfl⟩
  have imageB := (run.pointPresentation.inclusion_entry i b _).2 ⟨hb, rfl⟩
  have imageG := (run.actorPresentation.inclusion_entry i g _).2 ⟨hg, rfl⟩
  have imageH := (run.actorPresentation.inclusion_entry i h _).2 ⟨hh, rfl⟩
  have imageK := (run.actorPresentation.inclusion_entry i k _).2 ⟨hk, rfl⟩
  have imageL := (run.actorPresentation.inclusion_entry i l _).2 ⟨hl, rfl⟩
  refine ⟨run.limitMaps_agreement i _ _ _ _ _ _ imageK imageG imageC code.first_agreement,
    run.limitMaps_agreement i _ _ _ _ _ _ imageL imageH imageC code.second_agreement,
    run.limitMaps_agreement i _ _ _ _ _ _ imageK imageL imageB code.common_agreement, ?_⟩
  obtain ⟨v, hv, w, hw, y, hy, z, hz, t, ht, gv, hwAct, ky, lz, kt, lt, rootK, rootL, cross⟩ := code.values
  exact ⟨run.pointPresentation.limitPoint i v, run.pointPresentation.limitPoint_mem hv,
    run.pointPresentation.limitPoint i w, run.pointPresentation.limitPoint_mem hw,
    run.pointPresentation.limitPoint i y, run.pointPresentation.limitPoint_mem hy,
    run.pointPresentation.limitPoint i z, run.pointPresentation.limitPoint_mem hz,
    run.pointPresentation.limitPoint i t, run.pointPresentation.limitPoint_mem ht,
    (run.limitAction_at i hg hc hv).2 gv, (run.limitAction_at i hh hc hw).2 hwAct,
    (run.limitAction_at i hk hd hy).2 ky, (run.limitAction_at i hl hd hz).2 lz,
    (run.limitAction_at i hk hb ht).2 kt, (run.limitAction_at i hl hb ht).2 lt,
    (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at i hy hX hv).2 rootK),
    (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at i hz hX hw).2 rootL),
    (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at i hy hz ht).2 cross)⟩

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_MainPrefixSelectedTraceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace OrdinalRecursionTrace
universe u
variable {B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem mainPrefix_values {i q : ZFSet.{u}} (entry : ZFSet.pair i q ∈ p) :
    q ∈ B ∧ MainPrefixAtIndex (insert i i) q := by
  have step := trace.2 i (trace.1.pair_source entry) q entry
  exact ⟨step.1, step.2.1⟩

theorem mainPrefix_extends {i j q r : ZFSet.{u}}
    (first : ZFSet.pair i q ∈ p) (second : ZFSet.pair j r ∈ p)
    (before : i = j ∨ i ∈ j) : MainPrefixExtends q r := by
  rcases before with rfl | before
  · have equal := trace.1.unique first second
    rw [equal]
    exact (trace.mainPrefix_values second).2.refl
  · have step := trace.2 j (trace.1.pair_source second) r second
    exact step.2.2.1 i q (pair_mem_graphRestriction.2 ⟨first, before⟩)

theorem preservedMainPrefixHistory {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
    (candidates : ∀ q ∈ B, PreservedMainPrefixCode M K Labels C D rD q) :
    PreservedMainPrefixHistoryCode M K Labels C D rD A p := by
  refine ⟨trace.1, ?_, ?_⟩
  · intro i q entry
    obtain ⟨member, S, E, equal⟩ := trace.mainPrefix_values entry
    obtain ⟨T, F, G, encoded, valid, preserved⟩ := candidates q member
    obtain ⟨rfl, rfl, rfl⟩ := mainPrefixCode_inj.1 (encoded.symm.trans equal)
    exact ⟨_, _, equal, valid, preserved⟩
  · intro i j q r first second before
    exact trace.mainPrefix_extends first second before

end OrdinalRecursionTrace

namespace PreservedMainPrefixHistoryCode
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD A p : ZFSet.{u}}
variable (history : PreservedMainPrefixHistoryCode M K Labels C D rD A p)

theorem unionCode_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (domain : A ∈ M.sets) (whole : p ∈ M.sets) :
    history.graphFamily.unionCode ∈ M.sets := by
  apply history.graphFamily.unionCode_ground pairing unions powers separation
    (@SetMembers.raw A) (SetMembers.raw_injective A)
  · rw [ordinalMainIndex_key_range]
    exact domain
  · rw [history.graphFamily_codeGraph_eq]
    exact whole

theorem ranked_union_candidate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (hK : K ∈ M.sets)
    (ordinalK : ordinalSetProperty K) (regular : GroundRegular M K)
    (limit : Order.IsSuccLimit (ZFSet.rank K))
    (domain : A ∈ M.sets) (whole : p ∈ M.sets) (small : GroundBelow M A K)
    (level : GroundMainCandidateLevel M K)
    (candidates : ∀ i q, ZFSet.pair i q ∈ p → q ∈ level.preservedMainPrefixes Labels C D rD) :
    history.graphFamily.unionCode ∈ M.sets ∧
      ZFSet.rank history.graphFamily.unionCode < ZFSet.rank K ∧
      history.graphFamily.unionCode ∈ level.preservedMainPrefixes Labels C D rD := by
  have ranks : ∀ i, ZFSet.rank (history.graphFamily.code i) < ZFSet.rank K := by
    intro i
    exact ((level.membership _).1
      ((level.mem_preservedMainPrefixes).1 (candidates _ _ (history.graphFamily_code_entry i))).1).2
  have domainRange : ZFSet.range (@SetMembers.raw A) ∈ M.sets := by
    rw [ordinalMainIndex_key_range]
    exact domain
  have wholeFamily : familyCodeGraph (@SetMembers.raw A) history.graphFamily.code ∈ M.sets := by
    rw [history.graphFamily_codeGraph_eq]
    exact whole
  have smallRange : GroundBelow M (ZFSet.range (@SetMembers.raw A)) K := by
    rw [ordinalMainIndex_key_range]
    exact small
  have rank := history.graphFamily.unionCode_rank_lt_small pairing unions powers separation collection
    hK ordinalK regular limit (@SetMembers.raw A) (SetMembers.raw_injective A) domainRange wholeFamily smallRange ranks
  have ground := history.unionCode_ground pairing unions powers separation domain whole
  refine ⟨ground, rank, level.mem_preservedMainPrefixes.2 ⟨(level.membership _).2 ⟨ground, rank⟩, ?_⟩⟩
  exact ⟨history.graphFamily.indexUnion, history.graphFamily.stageUnion, history.graphFamily.transitionUnion,
    rfl, history.graphFamily.union_valid,
    history.graphFamily.union_profile_graph_code history.graphFamily_profiles⟩

theorem union_mem_recursionPrefixes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (hK : K ∈ M.sets)
    (ordinalK : ordinalSetProperty K) (regular : GroundRegular M K)
    (limit : Order.IsSuccLimit (ZFSet.rank K))
    (domain : A ∈ M.sets) (whole : p ∈ M.sets) (small : GroundBelow M A K)
    (level : GroundMainCandidateLevel M K)
    (candidates : ∀ i q, ZFSet.pair i q ∈ p → q ∈ level.preservedMainPrefixes Labels C D rD)
    {Omega : ZFSet.{u}} (member : A ∈ Omega) (nonempty : A ≠ ∅)
    (ordinalA : ordinalSetProperty A) :
    history.graphFamily.unionCode ∈ level.recursionPrefixes Omega Labels C D rD := by
  have candidate := (history.ranked_union_candidate pairing unions powers separation collection
    hK ordinalK regular limit domain whole small level candidates).2.2
  refine level.mem_recursionPrefixes.2 ⟨candidate, mainPrefixRecursionIndexCode_iff.2 ?_⟩
  rw [history.graphFamily_indexUnion ordinalA]
  exact ⟨member, nonempty⟩

end PreservedMainPrefixHistoryCode

section
universe u

theorem MainPrefixHistoryExtends.union_code {p q T i : ZFSet.{u}}
    (history : MainPrefixHistoryExtends p q) (code : MainPrefixAtIndex T q)
    (last : ZFSet.pair i q ∈ p) : MainPrefixHistoryUnionCode p q := by
  obtain ⟨S, E, rfl⟩ := code
  refine ⟨T, S, E, rfl, ?_⟩
  intro j x
  constructor
  · intro member
    exact ⟨i, T, S, E, last, member⟩
  · rintro ⟨k, U, F, G, entry, member⟩
    have extension := mainPrefixExtends_iff.1 (history k _ entry)
    have subset : (Fin.cases U (Fin.cases F (fun _ => G)) : Fin 3 → ZFSet.{u}) j ⊆
        (Fin.cases T (Fin.cases S (fun _ => E)) : Fin 3 → ZFSet.{u}) j :=
      Fin.cases extension.1 (Fin.cases extension.2.1 (fun _ => extension.2.2)) j
    exact subset member

theorem OrdinalRecursionTrace.mainPrefix_successor_union {B seed g β p q : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) (insert β β) p)
    (last : ZFSet.pair β q ∈ p) : MainPrefixHistoryUnionCode p q := by
  have history : MainPrefixHistoryExtends p q := by
    intro i old entry
    exact trace.mainPrefix_extends entry last (ZFSet.mem_insert_iff.1 (trace.1.pair_source entry))
  exact history.union_code (trace.mainPrefix_values last).2 last

end

namespace PreservedMainPrefixHistoryCode
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD A p : ZFSet.{u}}
variable (history : PreservedMainPrefixHistoryCode M K Labels C D rD A p)
include history

theorem exists_unique_groundUnionCode
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (member : A ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    (nonempty : A ≠ ∅) (whole : p ∈ M.sets)
    (level : GroundMainCandidateLevel M K)
    (candidates : ∀ i q, ZFSet.pair i q ∈ p → q ∈ level.preservedMainPrefixes Labels C D rD) :
    ∃ q ∈ M.sets, MainPrefixHistoryUnionCode p q ∧
      q ∈ level.recursionPrefixes (M.groundOmegaOne pairing unions powers separation collection infinite)
        Labels C D rD ∧
      (∃ S E, q = mainPrefixCode A S E) ∧
      (∀ i old, ZFSet.pair i old ∈ p → MainPrefixExtends old q) ∧
      ∀ r, MainPrefixHistoryUnionCode p r → r = q := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have domain := M.transitive spec.1 member
  have ordinalA := ordinalSetProperty_member spec.2.1 member
  have small : GroundBelow M A K :=
    ⟨ZFSet.omega, conditions.2.1,
      M.groundOmegaOne_member_countable pairing unions powers separation collection infinite member⟩
  have ground := history.unionCode_ground pairing unions powers separation domain whole
  have candidate := history.union_mem_recursionPrefixes pairing unions powers separation collection
    hK conditions.1 conditions.2.2.1
    (conditions.rank_isLimit pairing unions powers separation infinite hK)
    domain whole small level candidates member nonempty ordinalA
  refine ⟨history.graphFamily.unionCode, ground, history.union_code, candidate, ?_, ?_, ?_⟩
  · refine ⟨history.graphFamily.stageUnion, history.graphFamily.transitionUnion, ?_⟩
    unfold MainPrefixGraphFamily.unionCode
    rw [history.graphFamily_indexUnion ordinalA]
  · intro i old entry
    let k := SetMembers.ofMem i (history.function.pair_source entry)
    have actual : ZFSet.pair i (history.graphFamily.code k) ∈ p := by
      simpa only [k, SetMembers.raw_ofMem] using history.graphFamily_code_entry k
    have equal := history.function.unique entry actual
    rw [equal]
    exact history.graphFamily.code_extends_union k
  · intro r code
    exact code.unique history.union_code

end PreservedMainPrefixHistoryCode

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mainPrefixTraceParams_ground {B seed g : ZFSet.{u}}
    (hB : B ∈ M.sets) (hSeed : seed ∈ M.sets) (hg : g ∈ M.sets) :
    ∀ j, mainPrefixTraceParams B seed g j ∈ M.sets :=
  Fin.cases hB (Fin.cases hSeed (fun _ => hg))

theorem realize_mainPrefixRecursionFormula {B seed g α p y : ZFSet.{u}}
    (hB : B ∈ M.sets) (hSeed : seed ∈ M.sets) (hg : g ∈ M.sets)
    (hα : α ∈ M.sets) (hp : p ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets mainPrefixRecursionFormula
      (extend α (extend p (extend y (mainPrefixTraceParams B seed g)))) ↔
      MainPrefixTraceStepCode B seed g α p y :=
  M.realize_mainPrefixTraceStepFormula 3 4 5 0 1 2 _
    (Fin.cases hα (Fin.cases hp (Fin.cases hy (M.mainPrefixTraceParams_ground hB hSeed hg))))

theorem mainPrefix_codeTrace {B seed g A p : ZFSet.{u}}
    (hB : B ∈ M.sets) (hSeed : seed ∈ M.sets) (hg : g ∈ M.sets) (hA : A ∈ M.sets)
    (trace : OrdinalRecursionTrace
      (groundRecursionStep M mainPrefixRecursionFormula (mainPrefixTraceParams B seed g)) A p) :
    OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p := by
  refine ⟨trace.1, ?_⟩
  intro α member y entry
  have step := trace.2 α member y entry
  exact (M.realize_mainPrefixRecursionFormula hB hSeed hg (M.transitive hA member) step.1 step.2.1).1
    step.2.2

end TransitiveGround

end

section
universe u

theorem MainPrefixTraceStepCode.selected_of_nonzero {B seed g α p y : ZFSet.{u}}
    (step : MainPrefixTraceStepCode B seed g α p y) (nonzero : α ≠ ∅) :
    ∃ input, MainPrefixHistoryUnionCode p input ∧ ZFSet.pair input y ∈ g := by
  rcases step.2.2.2 with ⟨zero, _⟩ | ⟨_, chosen⟩
  · exact False.elim (nonzero zero)
  · exact chosen

namespace OrdinalRecursionTrace
variable {B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem mainPrefix_successor_entry (ordinal : ordinalSetProperty A)
    {β old next : ZFSet.{u}} (member : insert β β ∈ A)
    (oldEntry : ZFSet.pair β old ∈ p) (nextEntry : ZFSet.pair (insert β β) next ∈ p) :
    ZFSet.pair old next ∈ g := by
  have ordinalIndex := ordinalSetProperty_member ordinal member
  have subset : insert β β ⊆ A := fun x hx => ordinal.1 _ member x hx
  have earlier := trace.restrict ordinalIndex subset
  have oldRestricted : ZFSet.pair β old ∈ graphRestriction (insert β β) p :=
    pair_mem_graphRestriction.2 ⟨oldEntry, ZFSet.mem_insert _ _⟩
  have unionOld := earlier.mainPrefix_successor_union oldRestricted
  have nonzero : insert β β ≠ ∅ := by
    intro zero
    exact ZFSet.notMem_empty β (zero ▸ ZFSet.mem_insert β β)
  obtain ⟨input, unionInput, entry⟩ :=
    (trace.2 _ member next nextEntry).selected_of_nonzero nonzero
  exact unionInput.unique unionOld ▸ entry

end OrdinalRecursionTrace

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mainPrefixTraceStepClosure
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) {Labels C D rD B seed g : ZFSet.{u}}
    (domain : B = level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD)
    (hB : B ∈ M.sets) (seedMember : seed ∈ B)
    (seedIndex : MainPrefixAtIndex (insert ∅ ∅) seed) (hg : g ∈ M.sets)
    (function : ZFSet.IsFunc B B g)
    (advance : ∀ old next T, ZFSet.pair old next ∈ g → MainPrefixAtIndex T old →
      MainPrefixAtIndex (insert T T) next ∧ MainPrefixExtends old next) :
    GroundOrdinalStepClosure M
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      mainPrefixRecursionFormula (mainPrefixTraceParams B seed g) := by
  have hSeed := M.transitive hB seedMember
  have hOmega := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have graph : FunctionGraphOn B g := ⟨B, function⟩
  have candidates : ∀ q ∈ B, PreservedMainPrefixCode M K Labels C D rD q := by
    intro q member
    rw [domain] at member
    exact (level.mem_preservedMainPrefixes.1 (level.mem_recursionPrefixes.1 member).1).2
  intro α member p hp trace
  have hα := M.transitive hOmega member
  have actual := M.mainPrefix_codeTrace hB hSeed hg hα trace
  have finish : ∀ y ∈ M.sets, MainPrefixTraceStepCode B seed g α p y →
      ∃ y ∈ M.sets, Realize M.sets mainPrefixRecursionFormula
        (extend α (extend p (extend y (mainPrefixTraceParams B seed g)))) ∧
        ∀ z ∈ M.sets, Realize M.sets mainPrefixRecursionFormula
          (extend α (extend p (extend z (mainPrefixTraceParams B seed g)))) → z = y := by
    intro y hy code
    refine ⟨y, hy, (M.realize_mainPrefixRecursionFormula hB hSeed hg hα hp hy).2 code, ?_⟩
    intro z hz recognized
    exact ((M.realize_mainPrefixRecursionFormula hB hSeed hg hα hp hz).1 recognized).unique graph code
  by_cases zero : α = ∅
  · apply finish seed hSeed
    refine ⟨seedMember, zero.symm ▸ seedIndex, ?_, Or.inl ⟨zero, rfl⟩⟩
    intro i old entry
    have impossible := trace.1.pair_source entry
    rw [zero] at impossible
    exact False.elim (ZFSet.notMem_empty i impossible)
  · have history := actual.preservedMainPrefixHistory candidates
    have storedCandidates : ∀ i q, ZFSet.pair i q ∈ p →
        q ∈ level.preservedMainPrefixes Labels C D rD := by
      intro i q entry
      have member := (actual.mainPrefix_values entry).1
      rw [domain] at member
      exact (level.mem_recursionPrefixes.1 member).1
    obtain ⟨input, _, unionCode, inputMember, inputIndex, extension, _⟩ :=
      history.exists_unique_groundUnionCode pairing unions powers separation collection infinite
        hK standard member zero hp level storedCandidates
    have inputB : input ∈ B := domain.symm ▸ inputMember
    obtain ⟨y, entry⟩ := graph.total inputB
    have yB := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    obtain ⟨index, stepExtension⟩ := advance input y α entry inputIndex
    apply finish y (M.transitive hB yB)
    exact ⟨yB, index, fun i old oldEntry => (extension i old oldEntry).trans stepExtension,
      Or.inr ⟨zero, input, unionCode, entry⟩⟩

theorem exists_unique_selectedMainPrefixTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) {Labels C D rD B seed g : ZFSet.{u}}
    (domain : B = level.recursionPrefixes
      (M.groundOmegaOne pairing unions powers separation collection infinite) Labels C D rD)
    (hB : B ∈ M.sets) (seedMember : seed ∈ B)
    (seedIndex : MainPrefixAtIndex (insert ∅ ∅) seed) (hg : g ∈ M.sets)
    (function : ZFSet.IsFunc B B g)
    (advance : ∀ old next T, ZFSet.pair old next ∈ g → MainPrefixAtIndex T old →
      MainPrefixAtIndex (insert T T) next ∧ MainPrefixExtends old next) :
    ∃ p ∈ M.sets,
      OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
        (M.groundOmegaOne pairing unions powers separation collection infinite) p ∧
      ∀ q, OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
        (M.groundOmegaOne pairing unions powers separation collection infinite) q → q = p := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have hSeed := M.transitive hB seedMember
  have closure := M.mainPrefixTraceStepClosure pairing unions powers separation collection infinite
    hK standard level domain hB seedMember seedIndex hg function advance
  obtain ⟨p, hp, trace, _, _⟩ := M.exists_unique_ordinalRecursionTrace pairing unions separation
    collection spec.1 spec.2.1 mainPrefixRecursionFormula (mainPrefixTraceParams B seed g)
    (M.mainPrefixTraceParams_ground hB hSeed hg) closure
  have actual := M.mainPrefix_codeTrace hB hSeed hg spec.1 trace
  refine ⟨p, hp, actual, ?_⟩
  intro q other
  exact other.unique actual spec.2.1 (fun _ hx => hx)
    (fun _ _ _ _ _ _ first second => first.unique ⟨B, function⟩ second)

end TransitiveGround

namespace OrdinalRecursionTrace
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem exists_groundTerminalPrefixCode
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (ordinal : ordinalSetProperty A) (whole : p ∈ M.sets)
    (candidates : ∀ q ∈ B, PreservedMainPrefixCode M K Labels C D rD q) :
    ∃ q ∈ M.sets, MainPrefixHistoryUnionCode p q ∧ MainPrefixAtIndex A q ∧
      PreservedMainPrefixCode M K Labels C D rD q ∧ MainPrefixHistoryExtends p q ∧
      ∀ r, MainPrefixHistoryUnionCode p r → r = q := by
  have history := trace.preservedMainPrefixHistory candidates
  let family := history.graphFamily
  have index := history.graphFamily_indexUnion ordinal
  have ground := history.unionCode_ground pairing unions powers separation hA whole
  refine ⟨family.unionCode, ground, history.union_code, ?_, ?_, ?_, ?_⟩
  · refine ⟨family.stageUnion, family.transitionUnion, ?_⟩
    change mainPrefixCode family.indexUnion family.stageUnion family.transitionUnion = _
    rw [index]
  · exact ⟨family.indexUnion, family.stageUnion, family.transitionUnion, rfl,
      family.union_valid, family.union_profile_graph_code history.graphFamily_profiles⟩
  · intro i old entry
    let k := SetMembers.ofMem i (trace.1.pair_source entry)
    have actual : ZFSet.pair i (family.code k) ∈ p := by
      simpa only [k, family, SetMembers.raw_ofMem] using history.graphFamily_code_entry k
    have equal := trace.1.unique entry actual
    rw [equal]
    exact family.code_extends_union k
  · intro r recognized
    exact recognized.unique history.union_code

end OrdinalRecursionTrace

namespace OrdinalRecursionTrace
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem exists_groundTerminalPrefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (ordinal : ordinalSetProperty A) (whole : p ∈ M.sets)
    (candidates : ∀ q ∈ B, PreservedMainPrefixCode M K Labels C D rD q) :
    ∃ ordinalA : ordinalSetProperty A,
      letI := ordinalMainIndexPreorder ordinalA
      ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers A),
        run.indices = A ∧ run.PreservesOldProfiles ∧ MainPrefixHistoryUnionCode p run.code ∧
        MainPrefixHistoryExtends p run.code ∧
        ∀ q, MainPrefixHistoryUnionCode p q → q = run.code := by
  obtain ⟨q, hq, union, index, preserved, extension, unique⟩ :=
    trace.exists_groundTerminalPrefixCode pairing unions powers separation hA ordinal whole candidates
  obtain ⟨T, _, ordinalT, run, indices, equal, profiles⟩ :=
    preserved.exists_decodedPrefix pairing unions powers separation hq
  let := ordinalMainIndexPreorder ordinalT
  have indexT : MainPrefixAtIndex T q := by
    refine ⟨run.stageGraph, run.transitionGraph, ?_⟩
    rw [← equal]
    change mainPrefixCode run.indices _ _ = _
    rw [indices]
  have same := indexT.unique index
  subst T
  refine ⟨ordinalT, run, indices, profiles, ?_, ?_, ?_⟩
  · exact equal.symm ▸ union
  · exact equal.symm ▸ extension
  · intro r recognized
    exact (unique r recognized).trans equal.symm

end OrdinalRecursionTrace

namespace OrdinalRecursionTrace
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD B seed g A p q : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem terminalCode_ranked_candidate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (hK : K ∈ M.sets)
    (ordinalK : ordinalSetProperty K) (regular : GroundRegular M K)
    (limit : Order.IsSuccLimit (ZFSet.rank K)) (hA : A ∈ M.sets) (whole : p ∈ M.sets)
    (small : GroundBelow M A K) (level : GroundMainCandidateLevel M K)
    (candidates : ∀ z ∈ B, z ∈ level.preservedMainPrefixes Labels C D rD)
    (terminal : MainPrefixHistoryUnionCode p q) :
    q ∈ M.sets ∧ ZFSet.rank q < ZFSet.rank K ∧
      q ∈ level.preservedMainPrefixes Labels C D rD := by
  have preserved : ∀ z ∈ B, PreservedMainPrefixCode M K Labels C D rD z := by
    intro z member
    exact (level.mem_preservedMainPrefixes.1 (candidates z member)).2
  have history := trace.preservedMainPrefixHistory preserved
  have ranked := history.ranked_union_candidate pairing unions powers separation collection
    hK ordinalK regular limit hA whole small level
    (fun _ z entry => candidates z (trace.mainPrefix_values entry).1)
  exact (terminal.unique history.union_code).symm ▸ ranked

theorem groundOmegaOne_terminalCode_ranked_candidate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (domain : A = M.groundOmegaOne pairing unions powers separation collection infinite)
    (whole : p ∈ M.sets) (level : GroundMainCandidateLevel M K)
    (candidateDomain : B = level.recursionPrefixes A Labels C D rD)
    (terminal : MainPrefixHistoryUnionCode p q) :
    GroundBelow M A K ∧ q ∈ M.sets ∧ ZFSet.rank q < ZFSet.rank K ∧
      q ∈ level.preservedMainPrefixes Labels C D rD := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have hA : A ∈ M.sets := domain.symm ▸
    (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have member : A ∈ K := domain.symm ▸
    standard.groundOmegaOne_mem pairing unions powers separation collection infinite hK
  have small := GroundBelow.of_member pairing unions powers separation hK member
  refine ⟨small, trace.terminalCode_ranked_candidate pairing unions powers separation collection
    hK conditions.1 conditions.2.2.1 (conditions.rank_isLimit pairing unions powers separation infinite hK)
    hA whole small level ?_ terminal⟩
  intro z hz
  rw [candidateDomain] at hz
  exact (level.mem_recursionPrefixes.1 hz).1

end OrdinalRecursionTrace

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_MainPrefixConditionalTraceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.OrdinalRecursionTrace
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD N f B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
variable (chosen : ∀ old next, ZFSet.pair old next ∈ g →
  MainPrefixConditionalStepCode M K Labels C D rD N f old next)
include trace chosen

theorem mainPrefix_selected_successor (ordinal : ordinalSetProperty A)
    {β old next : ZFSet.{u}} (member : insert β β ∈ A)
    (oldEntry : ZFSet.pair β old ∈ p) (nextEntry : ZFSet.pair (insert β β) next ∈ p) :
    MainPrefixSelectedStepCode f old next := by
  have entry := trace.mainPrefix_successor_entry ordinal member oldEntry nextEntry
  obtain ⟨S, E, oldCode⟩ := (trace.mainPrefix_values oldEntry).2
  exact (chosen old next entry).selected_of_successor oldCode

end PartitionPilot.Forcing.OrdinalRecursionTrace

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedImageCovers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_indexedImageCover (I U V maps y i : ZFSet.{u}) :
    ZFSet.pair y i ∈ indexedImageCover I U V maps ↔
      y ∈ V ∧ i ∈ I ∧ ∃ x ∈ U, ∃ f,
        ZFSet.pair i f ∈ maps ∧ ZFSet.pair x y ∈ f := by
  rw [indexedImageCover, pair_mem_relationCompose]
  constructor
  · rintro ⟨hy, hi, z, _, converse, projection⟩
    obtain ⟨j, hj, x, hx, equal⟩ := (mem_productFirst I U _).1 projection
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    have flattened := (pair_mem_relationConverse _ _ _ _ _).1 converse
    obtain ⟨_, _, _, f, indexed, entry⟩ :=
      (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).1 flattened.2.2
    exact ⟨hy, hi, x, hx, f, indexed, entry⟩
  · rintro ⟨hy, hi, x, hx, f, indexed, entry⟩
    refine ⟨hy, hi, ZFSet.pair i x, ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, ?_, ?_⟩
    · exact (pair_mem_relationConverse _ _ _ _ _).2
        ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy,
          (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).2
            ⟨hi, hx, hy, f, indexed, entry⟩⟩
    · exact (mem_productFirst I U _).2 ⟨i, hi, x, hx, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedImageCover_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I U V maps : ZFSet.{u}} (hI : I ∈ M.sets) (hU : U ∈ M.sets)
    (hV : V ∈ M.sets) (hMaps : maps ∈ M.sets) :
    indexedImageCover I U V maps ∈ M.sets := by
  have product := M.prod_mem pairing unions powers separation hI hU
  exact M.relationCompose_mem pairing unions powers separation hV product hI
    (M.relationConverse_mem pairing unions powers separation product hV
      (M.mapFamilyApplicationGraph_mem pairing unions powers separation hI hU hV hMaps))
    (M.productFirst_mem pairing unions powers separation hI hU)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalExtensionBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalChronology
open SetFormula
universe u v
variable {M N : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem exists_extension_basis (i₀ : I)
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ (run.finalGeometry i₀).order := by
  have terminal := chronology.terminal_values i₀
  have atTerminal : MeetFilterCode (chronology.serial.toHistory.space run.cutoffLimit)
      (chronology.serial.toHistory.order run.cutoffLimit)
      (chronology.serial.toHistory.meetGraph run.cutoffLimit) F := by
    simpa only [terminal.1, terminal.2.1, terminal.2.2.1] using filter
  have basis := chronology.serial.toHistory.exists_extension_basis includes pairingN unionsN powersN
    separationN infiniteN choiceN
    (M.insert_mem pairing unions run.cutoffLimit_ground run.cutoffLimit_ground)
    (run.finalGeometry i₀).columns_ground (run.finalGeometry i₀).coordinates_ground
    chronology.serial.ordinal smallD irreflexive (ZFSet.mem_insert run.cutoffLimit run.cutoffLimit)
    hF atTerminal
  simpa only [terminal.2.1] using basis

end PartitionPilot.Forcing.GroundMainPrefix.FinalChronology

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainOrdinalConstructionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMainOrdinalConstruction
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
          ∃ initial : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) pairing unions powers separation
              {i : Fin 2 // run.key i ∈ natSetCode 1},
            let B := level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode)
            B ∈ M.sets ∧ initial.code ∈ B ∧ initial.indices = natSetCode 1 ∧
            initial.PreservesOldProfiles ∧ initial.code ∈ M.sets ∧
            ZFSet.rank initial.code < ZFSet.rank K ∧
            initial.stageGraph = graphRestriction (natSetCode 1) run.stageGraph ∧
            initial.transitionGraph = graphRestriction (chronologyPairs (natSetCode 1)) run.transitionGraph ∧
            (∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = seed.source) ∧
            ∃ f ∈ M.sets,
              ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K C C
                (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode))
                (ZFSet.prod level.carrier level.carrier) f ∧
              f ⊆ M.taskBearingSuccessorRelation
                (M.linkedMainStageCandidates level.carrier K C C
                  (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode))
                level.carrier K C C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ∧
              (∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
                target ∈ M.linkedMainStageCandidates level.carrier K C C
                  (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ∧
                z ∈ level.carrier ∧ TaskBearingMainSuccessorCode M K C C
                  (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode)
                  ZFSet.omega source target z) ∧
              ∃ g ∈ M.sets, ZFSet.IsFunc B B g ∧
                g ⊆ M.mainPrefixConditionalRelation B K C C
                  (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) ZFSet.omega f ∧
                (∀ old next, ZFSet.pair old next ∈ g → next ∈ B ∧
                  MainPrefixConditionalStepCode M K C C
                    (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode)
                    ZFSet.omega f old next) ∧
                ∃ p ∈ M.sets,
                  OrdinalRecursionTrace (MainPrefixTraceStepCode B initial.code g) C p ∧
                  ∀ q, OrdinalRecursionTrace (MainPrefixTraceStepCode B initial.code g) C q → q = p := by
  dsimp only
  obtain ⟨level, seed, run, initial, domainGround, initialMember, initialIndices,
      profiles, initialGround, initialRank, stageRestriction, transitionRestriction, source⟩ :=
    M.exists_initialRecursionSeed pairing unions powers separation collection infinite choice hK standard
  have columnsGround := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  obtain ⟨f, hf, fFunction, fSelected, fEntries⟩ :=
    M.exists_groundOmegaOneTaskBearingSuccessorFunction pairing unions powers separation collection infinite choice
      hK standard seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground
      seed.injection_ground seed.dense (fun x hx => (seed.no_endpoints x hx).2) seed.injection_code level
  obtain ⟨g, hg, gFunction, gSelected, gEntries⟩ :=
    level.exists_groundConditionalPrefixFunction pairing unions powers separation collection infinite choice
      hK standard columnsGround seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground
      rfl hf fFunction fSelected
  let B := level.recursionPrefixes
    (M.groundOmegaOne pairing unions powers separation collection infinite)
    (M.groundOmegaOne pairing unions powers separation collection infinite)
    (M.groundOmegaOne pairing unions powers separation collection infinite)
    (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode)
  have seedIndex : MainPrefixAtIndex (insert ∅ ∅) initial.code := by
    refine ⟨initial.stageGraph, initial.transitionGraph, ?_⟩
    change mainPrefixCode initial.indices initial.stageGraph initial.transitionGraph = _
    rw [initialIndices]
    rfl
  have advance : ∀ old next T, ZFSet.pair old next ∈ g → MainPrefixAtIndex T old →
      MainPrefixAtIndex (insert T T) next ∧ MainPrefixExtends old next := by
    intro old next T entry index
    obtain ⟨S, E, oldCode⟩ := index
    have branch := (gEntries old next entry).2
    exact ⟨branch.next_fields oldCode, branch.extension⟩
  obtain ⟨p, hp, trace, unique⟩ := M.exists_unique_selectedMainPrefixTrace
    pairing unions powers separation collection infinite hK standard level
    (B := B) rfl domainGround initialMember seedIndex hg gFunction advance
  exact ⟨level, seed, run, initial, domainGround, initialMember, initialIndices,
    profiles, initialGround, initialRank, stageRestriction, transitionRestriction, source,
    f, hf, fFunction, fSelected, fEntries, g, hg, gFunction, gSelected, gEntries, p, hp, trace, unique⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem TransitiveGround.exists_groundMainOrdinalData (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    Nonempty (GroundMainOrdinalConstructionData M K
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      pairing unions powers separation) := by
  obtain ⟨level, seed, seedRun, initial, domainGround, initialMember, indices, profiles,
      _, rank, stages, transitions, source, f, hf, fFunction, fSelected, fEntries,
      g, hg, gFunction, gSelected, gEntries, p, hp, trace, unique⟩ :=
    M.exists_groundMainOrdinalConstruction pairing unions powers separation collection infinite choice hK standard
  exact ⟨⟨level, seed, seedRun, initial, _, rfl, domainGround, initialMember, indices,
    profiles, rank, stages, transitions, source, f, hf, fFunction, fSelected, fEntries,
    g, hg, gFunction, gSelected, gEntries, p, hp, trace, unique⟩⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixFinalDirectedness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitPoints_directed {x y : ZFSet.{u}}
    (hx : x ∈ run.limitPoints) (hy : y ∈ run.limitPoints) :
    ∃ z ∈ run.limitPoints, ZFSet.pair x z ∈ run.limitOrder ∧
      ZFSet.pair y z ∈ run.limitOrder := by
  obtain ⟨i, a, b, ha, hb, rfl, rfl⟩ := run.pointPresentation.pair_coverage hx hy
  have ht := (run.diagram.stage i).stage.top_mem
  refine ⟨run.pointPresentation.limitPoint i (run.diagram.stage i).stage.top,
    run.pointPresentation.limitPoint_mem ht, ?_, ?_⟩
  · exact (run.limitOrder_entry _ _).2 ((run.limitLE_at i ha ht).2
      ((run.diagram.stage i).stage.greatest a ha))
  · exact (run.limitOrder_entry _ _).2 ((run.limitLE_at i hb ht).2
      ((run.diagram.stage i).stage.greatest b hb))

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTaskBearingSeparation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u v

namespace TaskBearingMainSuccessorCode
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem separation_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    SeparationFulfillmentCode source.main.stage.carrier source.main.stage.order
      target.main.stage.carrier target.main.stage.order target.main.stage.meetGraph
      target.main.stage.actors target.main.stage.action transition.map.points := by
  obtain ⟨extra, _, output, _⟩ := code.output_on_linked
  have separated := output.separation
  simp only [linkedSuccessorOutputFields_0, linkedSuccessorOutputFields_2,
    linkedSuccessorOutputFields_1, linkedSuccessorOutputFields_3,
    linkedSuccessorOutputFields_5, linkedSuccessorOutputFields_7,
    linkedSuccessorOutputFields_13, linkedSuccessorOutputFields_18] at separated
  exact separated

end TaskBearingMainSuccessorCode

namespace GroundMainPrefix
open SetFormula
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem separation_of_taskBearing {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code) :
    SeparationFulfillmentCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage j).stage.carrier
      (run.diagram.stage j).stage.order (run.diagram.stage j).stage.meetGraph
      (run.diagram.stage j).stage.actors (run.diagram.stage j).stage.action
      (run.diagram.transition before).map.points := by
  let transition := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code transition.map.code := by
    simpa only [transition, GroundChronologicalMainTransition.retargetEq_code] using code
  have separated := actual.separation_on_linked
  simpa only [transition, GroundChronologicalMainTransition.retargetEq_points,
    run.linked_main i, run.linked_main j] using separated

end GroundMainPrefix
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTaskBearingStrictTop
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u v

namespace TaskBearingMainSuccessorCode
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem strict_top_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    StrictSuccessorTopCode source.main.stage.carrier target.main.stage.carrier
      target.main.stage.order transition.map.points target.main.stage.top := by
  obtain ⟨extra, _, output, _⟩ := code.output_on_linked
  have strict := output.strict_top
  rw [linkedSuccessorOutputFields_0, linkedSuccessorOutputFields_1,
    linkedSuccessorOutputFields_3, linkedSuccessorOutputFields_18,
    linkedSuccessorOutputFields_29] at strict
  exact strict

end TaskBearingMainSuccessorCode

namespace GroundMainPrefix
open SetFormula
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem strict_top_of_taskBearing {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code) :
    StrictSuccessorTopCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage j).stage.carrier (run.diagram.stage j).stage.order
      (run.diagram.transition before).map.points (run.diagram.stage j).stage.top := by
  let transition := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code transition.map.code := by
    simpa only [transition, GroundChronologicalMainTransition.retargetEq_code] using code
  have strict := actual.strict_top_on_linked
  simpa only [transition, GroundChronologicalMainTransition.retargetEq_points,
    run.linked_main i, run.linked_main j] using strict

end GroundMainPrefix
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixFinalStrictGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem selectedStep_terminal_entry {old next f : ZFSet.{u}} {i j : I}
    (before : i ≤ j) (adjacent : run.key j = insert (run.key i) (run.key i))
    (oldIndex : MainPrefixAtIndex (insert (run.key i) (run.key i)) old)
    (selected : MainPrefixSelectedStepCode f old next)
    (oldExtension : MainPrefixExtends old run.code)
    (nextExtension : MainPrefixExtends next run.code) :
    ZFSet.pair (run.linked i).code
      (ZFSet.pair (run.linked j).code (run.diagram.transition before).map.code) ∈ f := by
  obtain ⟨F, G, oldEqual⟩ := oldIndex
  obtain ⟨b, S, E, S', E', a, target, z, first, second, _, sourceEntry,
    selectedEntry, targetEntry, mapEntry⟩ := selected
  have same : b = run.key i := setSuccessor_injective
    (mainPrefixCode_inj.1 (first.symm.trans oldEqual)).1
  subst b
  rw [first] at oldExtension
  rw [second] at nextExtension
  have oldIncluded := (mainPrefixExtends_iff.1 oldExtension).2.1
  have nextIncluded := (mainPrefixExtends_iff.1 nextExtension).2
  have sourceEqual := (run.stageGraph_entry i a).1 (oldIncluded sourceEntry)
  have targetActual : ZFSet.pair (run.key j) target ∈ run.stageGraph := by
    rw [adjacent]
    exact nextIncluded.1 targetEntry
  have targetEqual := (run.stageGraph_entry j target).1 targetActual
  have mapActual : ZFSet.pair (ZFSet.pair (run.key j) (run.key i)) z ∈ run.transitionGraph := by
    rw [adjacent]
    exact nextIncluded.2 mapEntry
  have mapEqual := (run.transitionGraph_entry before z).1 mapActual
  rw [sourceEqual, targetEqual, mapEqual] at selectedEntry
  exact selectedEntry

theorem terminal_successor_entry {A B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (domain : run.indices = A) (extension : MainPrefixHistoryExtends p run.code)
    {i j : I} (before : i ≤ j)
    (adjacent : run.key j = insert (run.key i) (run.key i)) :
    ZFSet.pair (run.linked i).code
      (ZFSet.pair (run.linked j).code (run.diagram.transition before).map.code) ∈ f := by
  have oldMember : run.key i ∈ A := domain ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have nextMember : insert (run.key i) (run.key i) ∈ A := by
    rw [← adjacent]
    exact domain ▸ ZFSet.mem_range.2 ⟨j, rfl⟩
  obtain ⟨old, oldEntry⟩ := trace.1.total oldMember
  obtain ⟨next, nextEntry⟩ := trace.1.total nextMember
  have selected := trace.mainPrefix_selected_successor chosen
    (domain ▸ run.indices_ordinal) nextMember oldEntry nextEntry
  exact run.selectedStep_terminal_entry before adjacent (trace.mainPrefix_values oldEntry).2
    selected (extension _ _ oldEntry) (extension _ _ nextEntry)

theorem terminal_successor_taskBearing {A B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = A) (extension : MainPrefixHistoryExtends p run.code)
    {i j : I} (before : i ≤ j)
    (adjacent : run.key j = insert (run.key i) (run.key i)) :
    TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code :=
  tasks _ _ _ (run.terminal_successor_entry trace chosen domain extension before adjacent)

theorem final_rectangle_at_bound
    (edges : ∀ i, ∃ j, ∃ before : i ≤ j,
      RectangleFulfillmentCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.actors
        (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
        (run.diagram.stage i).stage.action (run.diagram.stage j).stage.carrier
        (run.diagram.stage j).stage.actors (run.diagram.stage j).stage.order
        (run.diagram.stage j).stage.meetGraph (run.diagram.stage j).stage.action
        (run.diagram.transition before).map.points (run.diagram.transition before).map.actors)
    {c b d g h X : ZFSet.{u}}
    (rectangle : ExternalRectangleCode run.limitPoints run.limitActors run.limitOrder
      run.limitMeetGraph run.limitAction c b d g h) (hX : X ∈ run.limitPoints)
    (firstUpper : ∀ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair g d) y ∈ run.limitAction →
      ZFSet.pair y X ∈ run.limitOrder)
    (secondUpper : ∀ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair h d) y ∈ run.limitAction →
      ZFSet.pair y X ∈ run.limitOrder) :
    ∃ k ∈ run.limitActors, ∃ l ∈ run.limitActors,
      RectangleAtBoundCode run.limitPoints run.limitOrder run.limitMeetGraph run.limitAction
        c b d g h X k l := by
  obtain ⟨i, c₀, b₀, d₀, X₀, g₀, h₀, hc, hb, hd, hXX, hg, hh,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := run.rectangle_data_coverage
      rectangle.1 rectangle.2.1 rectangle.2.2.1 hX rectangle.2.2.2.1 rectangle.2.2.2.2.1
  have localRectangle := run.limitRectangle_reflect i hc hb hd hg hh rectangle
  have firstLocal : ∀ y ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair (ZFSet.pair g₀ d₀) y ∈ (run.diagram.stage i).stage.action →
        ZFSet.pair y X₀ ∈ (run.diagram.stage i).stage.order := by
    intro y hy entry
    exact (run.limitLE_at i hy hXX).1 ((run.limitOrder_entry _ _).1
      (firstUpper _ (run.pointPresentation.limitPoint_mem hy) ((run.limitAction_at i hg hd hy).2 entry)))
  have secondLocal : ∀ y ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair (ZFSet.pair h₀ d₀) y ∈ (run.diagram.stage i).stage.action →
        ZFSet.pair y X₀ ∈ (run.diagram.stage i).stage.order := by
    intro y hy entry
    exact (run.limitLE_at i hy hXX).1 ((run.limitOrder_entry _ _).1
      (secondUpper _ (run.pointPresentation.limitPoint_mem hy) ((run.limitAction_at i hh hd hy).2 entry)))
  obtain ⟨j, before, fulfills⟩ := edges i
  obtain ⟨c', imageC⟩ := run.pointSystem.map_entry_total before hc
  obtain ⟨b', imageB⟩ := run.pointSystem.map_entry_total before hb
  obtain ⟨d', imageD⟩ := run.pointSystem.map_entry_total before hd
  obtain ⟨X', imageX⟩ := run.pointSystem.map_entry_total before hXX
  obtain ⟨g', imageG⟩ := run.actorSystem.map_entry_total before hg
  obtain ⟨h', imageH⟩ := run.actorSystem.map_entry_total before hh
  obtain ⟨k, hk, l, hl, code⟩ := (run.diagram.transition before).map.rectangle_at_bound
    fulfills localRectangle hXX firstLocal secondLocal imageC imageB imageD imageX imageG imageH
  have finalCode := run.limitRectangleAtBound j
    (run.pointSystem.map_entry_bounds before imageC).2 (run.pointSystem.map_entry_bounds before imageB).2
    (run.pointSystem.map_entry_bounds before imageD).2 (run.pointSystem.map_entry_bounds before imageX).2
    (run.actorSystem.map_entry_bounds before imageG).2 (run.actorSystem.map_entry_bounds before imageH).2
    hk hl code
  rw [← run.pointPresentation.limitPoint_transition before imageC,
    ← run.pointPresentation.limitPoint_transition before imageB,
    ← run.pointPresentation.limitPoint_transition before imageD,
    ← run.pointPresentation.limitPoint_transition before imageX,
    ← run.actorPresentation.limitPoint_transition before imageG,
    ← run.actorPresentation.limitPoint_transition before imageH] at finalCode
  exact ⟨run.actorPresentation.limitPoint j k, run.actorPresentation.limitPoint_mem hk,
    run.actorPresentation.limitPoint j l, run.actorPresentation.limitPoint_mem hl, finalCode⟩

theorem final_rectangle_at_bound_of_trace
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code)
    {c b d a a' X : ZFSet.{u}}
    (rectangle : ExternalRectangleCode run.limitPoints run.limitActors run.limitOrder
      run.limitMeetGraph run.limitAction c b d a a') (hX : X ∈ run.limitPoints)
    (firstUpper : ∀ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair a d) y ∈ run.limitAction →
      ZFSet.pair y X ∈ run.limitOrder)
    (secondUpper : ∀ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair a' d) y ∈ run.limitAction →
      ZFSet.pair y X ∈ run.limitOrder) :
    ∃ k ∈ run.limitActors, ∃ l ∈ run.limitActors,
      RectangleAtBoundCode run.limitPoints run.limitOrder run.limitMeetGraph run.limitAction
        c b d a a' X k l := by
  apply run.final_rectangle_at_bound _ rectangle hX firstUpper secondUpper
  intro i
  have member : run.key i ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    domain ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have next := M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  obtain ⟨j, adjacent⟩ := ZFSet.mem_range.1 (domain.symm ▸ next)
  have before : i ≤ j := (run.key_order i j).2 (by
    rw [adjacent]
    exact Or.inr (ZFSet.mem_insert (run.key i) (run.key i)))
  exact ⟨j, before, run.rectangles_of_taskBearing before
    (run.terminal_successor_taskBearing trace chosen tasks domain extension before adjacent)⟩

theorem limitPoints_separation
    (edges : ∀ i, ∃ j, ∃ before : i ≤ j,
      SeparationFulfillmentCode (run.diagram.stage i).stage.carrier
        (run.diagram.stage i).stage.order (run.diagram.stage j).stage.carrier
        (run.diagram.stage j).stage.order (run.diagram.stage j).stage.meetGraph
        (run.diagram.stage j).stage.actors (run.diagram.stage j).stage.action
        (run.diagram.transition before).map.points)
    {W d x : ZFSet.{u}} (hW : W ∈ run.limitPoints)
    (hd : d ∈ run.limitPoints) (hx : x ∈ run.limitPoints)
    (wd : ZFSet.pair W d ∈ run.limitOrder) (wx : ZFSet.pair W x ∈ run.limitOrder) :
    ∃ k ∈ run.limitActors,
      (∀ z ∈ run.limitPoints, ZFSet.pair z W ∈ run.limitOrder →
        ZFSet.pair (ZFSet.pair k z) z ∈ run.limitAction) ∧
      ∃ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair k d) y ∈ run.limitAction ∧
        ZFSet.pair (ZFSet.pair y x) W ∈ run.limitMeetGraph := by
  obtain ⟨i, w, d₀, x₀, hw₀, hd₀, hx₀, rfl, rfl, rfl⟩ :=
    run.pointPresentation.triple_coverage hW hd hx
  have wd' := (run.limitLE_at i hw₀ hd₀).1 ((run.limitOrder_entry _ _).1 wd)
  have wx' := (run.limitLE_at i hw₀ hx₀).1 ((run.limitOrder_entry _ _).1 wx)
  obtain ⟨j, before, fulfilled⟩ := edges i
  obtain ⟨w', ww⟩ := run.pointSystem.map_entry_total before hw₀
  obtain ⟨d', dd⟩ := run.pointSystem.map_entry_total before hd₀
  obtain ⟨x', xx⟩ := run.pointSystem.map_entry_total before hx₀
  have hw' := (run.pointSystem.map_entry_bounds before ww).2
  have hd' := (run.pointSystem.map_entry_bounds before dd).2
  have hx' := (run.pointSystem.map_entry_bounds before xx).2
  obtain ⟨k, hk, actor⟩ := fulfilled w hw₀
  obtain ⟨fixes, separates⟩ := actor w' hw' ww
  obtain ⟨y, acted, _⟩ := (run.diagram.stage j).stage.action_code.function.2
    (ZFSet.pair k d') (ZFSet.pair_mem_prod.2 ⟨hk, hd'⟩)
  have hy := (ZFSet.pair_mem_prod.1
    ((run.diagram.stage j).stage.action_code.function.1 acted)).2
  have meet := separates d₀ hd₀ x₀ hx₀ d' hd' x' hx' y hy wd' wx' dd xx acted
  have imageK := (run.actorPresentation.inclusion_entry j k _).2 ⟨hk, rfl⟩
  have imageW := (run.pointPresentation.inclusion_entry j w' _).2 ⟨hw', rfl⟩
  have identityAgreement :=
    ((run.diagram.stage j).stage.action_code.agreement_identity_iff_fixes).2 fixes
  have finalAgreement := run.limitMaps_agreement j k (run.diagram.stage j).stage.identity
    (run.actorPresentation.limitPoint j k) (run.limitIdentity j) w'
    (run.pointPresentation.limitPoint j w') imageK
    (run.limitActorMap_groupEmbedding j j).one imageW identityAgreement
  have finalFixes := ((run.limitAction_code j).agreement_identity_iff_fixes).1 finalAgreement
  rw [run.pointPresentation.limitPoint_transition before ww,
    run.pointPresentation.limitPoint_transition before dd,
    run.pointPresentation.limitPoint_transition before xx]
  refine ⟨run.actorPresentation.limitPoint j k, run.actorPresentation.limitPoint_mem hk,
    finalFixes, run.pointPresentation.limitPoint j y, run.pointPresentation.limitPoint_mem hy,
    (run.limitAction_at j hk hd' hy).2 acted, ?_⟩
  exact (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at j hy hx' hw').2 meet)

theorem limitPoints_separation_of_trace
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code)
    {W d x : ZFSet.{u}} (hW : W ∈ run.limitPoints)
    (hd : d ∈ run.limitPoints) (hx : x ∈ run.limitPoints)
    (wd : ZFSet.pair W d ∈ run.limitOrder) (wx : ZFSet.pair W x ∈ run.limitOrder) :
    ∃ k ∈ run.limitActors,
      (∀ z ∈ run.limitPoints, ZFSet.pair z W ∈ run.limitOrder →
        ZFSet.pair (ZFSet.pair k z) z ∈ run.limitAction) ∧
      ∃ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair k d) y ∈ run.limitAction ∧
        ZFSet.pair (ZFSet.pair y x) W ∈ run.limitMeetGraph := by
  apply run.limitPoints_separation _ hW hd hx wd wx
  intro i
  have member : run.key i ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    domain ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have next := M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  obtain ⟨j, adjacent⟩ := ZFSet.mem_range.1 (domain.symm ▸ next)
  have before : i ≤ j := (run.key_order i j).2 (by
    rw [adjacent]
    exact Or.inr (ZFSet.mem_insert (run.key i) (run.key i)))
  exact ⟨j, before, run.separation_of_taskBearing before
    (run.terminal_successor_taskBearing trace chosen tasks domain extension before adjacent)⟩

theorem limitPoints_strict_extension
    (growth : ∀ i, ∃ j, ∃ before : i ≤ j,
      StrictSuccessorTopCode (run.diagram.stage i).stage.carrier
        (run.diagram.stage j).stage.carrier (run.diagram.stage j).stage.order
        (run.diagram.transition before).map.points (run.diagram.stage j).stage.top)
    {x : ZFSet.{u}} (member : x ∈ run.limitPoints) :
    ∃ y ∈ run.limitPoints, ZFSet.pair x y ∈ run.limitOrder ∧
      ZFSet.pair y x ∉ run.limitOrder := by
  obtain ⟨i, a, ha, rfl⟩ := run.pointPresentation.limitPoint_coverage member
  obtain ⟨j, before, strict⟩ := growth i
  obtain ⟨b, entry⟩ := run.pointSystem.map_entry_total before ha
  have hb := (run.pointSystem.map_entry_bounds before entry).2
  have ht := (run.diagram.stage j).stage.top_mem
  have bounds := strict a ha b hb entry
  refine ⟨run.pointPresentation.limitPoint j (run.diagram.stage j).stage.top,
    run.pointPresentation.limitPoint_mem ht, ?_⟩
  rw [run.pointPresentation.limitPoint_transition before entry]
  exact ⟨(run.limitOrder_entry _ _).2 ((run.limitLE_at j hb ht).2 bounds.1),
    fun lower => bounds.2 ((run.limitLE_at j ht hb).1 ((run.limitOrder_entry _ _).1 lower))⟩

theorem terminal_adjacent_strict_top
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code) (i : I) :
    ∃ j, ∃ before : i ≤ j, run.key j = insert (run.key i) (run.key i) ∧
      StrictSuccessorTopCode (run.diagram.stage i).stage.carrier
        (run.diagram.stage j).stage.carrier (run.diagram.stage j).stage.order
        (run.diagram.transition before).map.points (run.diagram.stage j).stage.top := by
  have member : run.key i ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    domain ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have next := M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  obtain ⟨j, adjacent⟩ := ZFSet.mem_range.1 (domain.symm ▸ next)
  have before : i ≤ j := (run.key_order i j).2 (by
    rw [adjacent]
    exact Or.inr (ZFSet.mem_insert (run.key i) (run.key i)))
  exact ⟨j, before, adjacent, run.strict_top_of_taskBearing before
    (run.terminal_successor_taskBearing trace chosen tasks domain extension before adjacent)⟩

theorem limitPoints_strict_extension_of_trace
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code)
    {x : ZFSet.{u}} (member : x ∈ run.limitPoints) :
    ∃ y ∈ run.limitPoints, ZFSet.pair x y ∈ run.limitOrder ∧
      ZFSet.pair y x ∉ run.limitOrder := by
  apply run.limitPoints_strict_extension _ member
  intro i
  obtain ⟨j, before, _, strict⟩ := run.terminal_adjacent_strict_top
    collection infinite trace chosen tasks domain extension i
  exact ⟨j, before, strict⟩

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixFinalInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem pointStageCover_ground : run.pointStageCover ∈ M.sets :=
  M.indexedImageCover_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPoints_ground run.limitPointInclusions_ground

theorem pointStageCover_entry (i : I) (y : ZFSet.{u}) :
    ZFSet.pair y (run.key i) ∈ run.pointStageCover ↔
      ∃ x ∈ (run.diagram.stage i).stage.carrier, ZFSet.pair x y ∈ run.limitPointMap i := by
  rw [pointStageCover, pair_mem_indexedImageCover]
  constructor
  · rintro ⟨_, _, x, _, f, indexed, entry⟩
    have equal := (run.limitPointInclusions_entry i f).1 indexed
    subst f
    exact ⟨x, (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).1, entry⟩
  · rintro ⟨x, hx, entry⟩
    exact ⟨(ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2,
      ZFSet.mem_range.2 ⟨i, rfl⟩, x, run.pointPresentation.carrier_bound i hx,
      run.limitPointMap i, (run.limitPointInclusions_entry i _).2 rfl, entry⟩

theorem pointStageCover_total {y : ZFSet.{u}} (member : y ∈ run.limitPoints) :
    ∃ i ∈ run.indices, ZFSet.pair y i ∈ run.pointStageCover := by
  obtain ⟨i, x, hx, equal⟩ := run.pointPresentation.limitPoint_coverage member
  exact ⟨run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩,
    (run.pointStageCover_entry i y).2
      ⟨x, hx, (run.pointPresentation.inclusion_entry i x y).2 ⟨hx, equal⟩⟩⟩

theorem exists_groundPointStageCover
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X : ZFSet.{u}} (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints) :
    ∃ f ∈ M.sets, ZFSet.IsFunc X run.indices f ∧ f ⊆ run.pointStageCover ∧
      ∀ y t, ZFSet.pair y t ∈ f → ∃ i : I, run.key i = t ∧
        ∃ x ∈ (run.diagram.stage i).stage.carrier, ZFSet.pair x y ∈ run.limitPointMap i := by
  obtain ⟨f, ground, function, included⟩ :=
    M.uniformize_relation pairing unions powers separation choice hX run.indices_ground
      run.pointStageCover_ground (fun _ hy => run.pointStageCover_total (subset hy))
  refine ⟨f, ground, function, included, ?_⟩
  intro y t entry
  have index := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 index
  exact ⟨i, rfl, (run.pointStageCover_entry i y).1 (included entry)⟩

end GroundMainPrefix

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (indices : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
include collection infinite choice indices

theorem exists_countablePointStageCover {X : ZFSet.{u}}
    (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints)
    (small : M.groundEmbeddable X ZFSet.omega) :
    ∃ j : I, ∃ f ∈ M.sets, ZFSet.IsFunc X run.indices f ∧ f ⊆ run.pointStageCover ∧
      (∀ x t, ZFSet.pair x t ∈ f → t ∈ run.key j) ∧
      ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair y x ∈ run.limitPointMap j := by
  obtain ⟨f, ground, function, included, covers⟩ :=
    run.exists_groundPointStageCover choice hX subset
  have rangeGround := M.relationImage_mem separation hX run.indices_ground ground
  have rangeSmall := M.groundEmbeddable_function_image pairing unions powers separation choice
    hX run.indices_ground (M.omega_mem separation infinite) ground function small
  have rangeSubset : relationImage X run.indices f ⊆
      M.groundOmegaOne pairing unions powers separation collection infinite := by
    intro t ht
    rw [← indices]
    exact ((mem_relationImage _ _ _ _).1 ht).1
  obtain ⟨bound, inOmega, strict⟩ := M.groundOmegaOne_countable_bound
    pairing unions powers separation collection infinite choice rangeGround rangeSubset rangeSmall
  have inIndices : bound ∈ run.indices := by rw [indices]; exact inOmega
  obtain ⟨j, equal⟩ := ZFSet.mem_range.1 inIndices
  have strictEntry : ∀ x t, ZFSet.pair x t ∈ f → t ∈ run.key j := by
    intro x t entry
    rw [equal]
    have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact strict t ((mem_relationImage _ _ _ _).2 ⟨bounds.2, x, bounds.1, entry⟩)
  refine ⟨j, f, ground, function, included, strictEntry, ?_⟩
  intro x hx
  obtain ⟨t, entry, _⟩ := function.2 x hx
  obtain ⟨i, key, y, hy, image⟩ := covers x t entry
  have before : i ≤ j := (run.key_order i j).2 (Or.inr (by rw [key]; exact strictEntry x t entry))
  obtain ⟨z, transition⟩ := run.pointSystem.map_entry_total before hy
  exact ⟨z, (run.pointSystem.map_entry_bounds before transition).2,
    run.limitPointMap_later_entry before transition image⟩

theorem exists_countablePointLocalization {X : ZFSet.{u}}
    (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints)
    (small : M.groundEmbeddable X ZFSet.omega) :
    ∃ j : I, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
      ZFSet.pair y x ∈ run.limitPointMap j := by
  obtain ⟨j, _, _, _, _, _, covered⟩ :=
    run.exists_countablePointStageCover collection infinite choice indices hX subset small
  exact ⟨j, covered⟩

theorem exists_countablePointUpperBound {X : ZFSet.{u}}
    (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints)
    (small : M.groundEmbeddable X ZFSet.omega) :
    ∃ j : I, ∃ b ∈ M.sets, b ∈ run.limitPoints ∧
      ZFSet.pair (run.diagram.stage j).stage.top b ∈ run.limitPointMap j ∧
      ∀ x ∈ X, ZFSet.pair x b ∈ run.limitOrder := by
  obtain ⟨j, covered⟩ :=
    run.exists_countablePointLocalization collection infinite choice indices hX subset small
  obtain ⟨b, image, _⟩ := (run.limitPointMap_injection j).function.2
    (run.diagram.stage j).stage.top (run.diagram.stage j).stage.top_mem
  have member := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 image)).2
  refine ⟨j, b, M.transitive run.limitPoints_ground member, member, image, ?_⟩
  intro x hx
  obtain ⟨y, hy, atStage⟩ := covered x hx
  exact (run.limitPointMap_order_iff j y (run.diagram.stage j).stage.top x b atStage image).2
    ((run.diagram.stage j).stage.greatest y hy)

end GroundMainPrefix

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalFulfillmentConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.GroundMainOrdinalConstructionData
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K C : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable (data : GroundMainOrdinalConstructionData M K C pairing unions powers separation)

theorem exists_rankedTerminal
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (columns : C = M.groundOmegaOne pairing unions powers separation collection infinite) :
    ∃ ordinalC : ordinalSetProperty C,
      letI := ordinalMainIndexPreorder ordinalC
      ∃ run : GroundMainPrefix M K C C (rationalCarrier data.seed.fractionCode)
          (rationalLtGraph data.seed.fractionCode) pairing unions powers separation (SetMembers C),
        run.indices = C ∧ run.PreservesOldProfiles ∧
        MainPrefixHistoryUnionCode data.history run.code ∧
        MainPrefixHistoryExtends data.history run.code ∧
        (∀ q, MainPrefixHistoryUnionCode data.history q → q = run.code) ∧
        GroundBelow M run.indices K ∧ ZFSet.rank run.code < ZFSet.rank K ∧
        run.code ∈ data.level.preservedMainPrefixes C C (rationalCarrier data.seed.fractionCode)
          (rationalLtGraph data.seed.fractionCode) ∧
        ∃ i₀ : SetMembers C, run.key i₀ = ∅ := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have hC : C ∈ M.sets := columns.symm ▸ spec.1
  have ordinal : ordinalSetProperty C := columns.symm ▸ spec.2.1
  have candidates : ∀ q ∈ data.domain, PreservedMainPrefixCode M K C C
      (rationalCarrier data.seed.fractionCode) (rationalLtGraph data.seed.fractionCode) q := by
    intro q member
    rw [data.domain_eq] at member
    exact (data.level.mem_preservedMainPrefixes.1 (data.level.mem_recursionPrefixes.1 member).1).2
  obtain ⟨ordinalC, run, indices, profiles, terminal, extension, unique⟩ :=
    data.trace.exists_groundTerminalPrefix pairing unions powers separation hC ordinal data.history_ground candidates
  let := ordinalMainIndexPreorder ordinalC
  obtain ⟨small, _, rank, candidate⟩ :=
    data.trace.groundOmegaOne_terminalCode_ranked_candidate pairing unions powers separation collection infinite
      hK standard columns data.history_ground data.level data.domain_eq terminal
  have zero : ∅ ∈ C := by
    rw [columns]
    exact (spec.2.2.1 ∅).2
      ⟨M.empty_mem ⟨_, spec.1⟩, ordinalSetProperty_empty,
        M.empty_groundEmbeddable ZFSet.omega ⟨_, spec.1⟩⟩
  have zeroIndex : ∅ ∈ run.indices := indices.symm ▸ zero
  obtain ⟨i₀, key⟩ := ZFSet.mem_range.1 zeroIndex
  exact ⟨ordinalC, run, indices, profiles, terminal, extension, unique,
    indices.symm ▸ small, rank, candidate, i₀, key⟩

end PartitionPilot.Forcing.GroundMainOrdinalConstructionData



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMainFinalGeometry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ data : GroundMainOrdinalConstructionData M K C pairing unions powers separation,
      ∃ ordinalC : ordinalSetProperty C,
        letI := ordinalMainIndexPreorder ordinalC
        ∃ run : GroundMainPrefix M K C C (rationalCarrier data.seed.fractionCode)
            (rationalLtGraph data.seed.fractionCode) pairing unions powers separation (SetMembers C),
          run.indices = C ∧ run.PreservesOldProfiles ∧
          MainPrefixHistoryUnionCode data.history run.code ∧
          MainPrefixHistoryExtends data.history run.code ∧
          (∀ q, MainPrefixHistoryUnionCode data.history q → q = run.code) ∧
          GroundBelow M run.indices K ∧ ZFSet.rank run.code < ZFSet.rank K ∧
          ∃ i₀ : SetMembers C, run.key i₀ = ∅ ∧
            let geometry := run.finalGeometry i₀
            let inclusions := run.finalInclusions i₀
            geometry.code ∈ M.sets ∧ ZFSet.rank geometry.code < ZFSet.rank K ∧
            GroundBelow M geometry.carrier K ∧ GroundBelow M geometry.actors K ∧
            inclusions.pointFamily ∈ M.sets ∧ inclusions.actorFamily ∈ M.sets ∧
            ZFSet.rank inclusions.pointFamily < ZFSet.rank K ∧
            ZFSet.rank inclusions.actorFamily < ZFSet.rank K ∧
            (∀ X ∈ M.sets, X ⊆ geometry.carrier → M.groundEmbeddable X ZFSet.omega →
              (∃ j, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
                ZFSet.pair y x ∈ inclusions.pointMap j) ∧
              ∃ b ∈ geometry.carrier, ∀ x ∈ X, ZFSet.pair x b ∈ geometry.order) ∧
            ∀ x ∈ geometry.carrier, ∃ y ∈ geometry.carrier,
              ZFSet.pair x y ∈ geometry.order ∧ ¬ ZFSet.pair y x ∈ geometry.order := by
  dsimp only
  obtain ⟨data⟩ := M.exists_groundMainOrdinalData pairing unions powers separation
    collection infinite choice hK standard
  obtain ⟨ordinalC, run, indices, profiles, terminal, extension, unique, small, rank, _, i₀, zero⟩ :=
    data.exists_rankedTerminal collection infinite hK standard rfl
  let := ordinalMainIndexPreorder ordinalC
  have limit := (standard.to_conditions pairing unions powers separation hK).rank_isLimit
    pairing unions powers separation infinite hK
  have sizes := run.finalGeometry_below i₀ choice hK standard small
  have maps := run.finalInclusions_rank_lt i₀ limit rank
  refine ⟨data, ordinalC, run, indices, profiles, terminal, extension, unique, small, rank,
    i₀, zero, (run.finalGeometry i₀).code_ground pairing,
    run.finalGeometry_code_rank_lt i₀ limit rank, sizes.1, sizes.2,
    (run.finalInclusions i₀).pointFamily_ground, (run.finalInclusions i₀).actorFamily_ground,
    maps.1, maps.2.1, ?_, ?_⟩
  · intro X hX subset countable
    have localized := run.exists_countablePointLocalization collection infinite choice indices hX subset countable
    obtain ⟨_, b, _, hb, _, bound⟩ :=
      run.exists_countablePointUpperBound collection infinite choice indices hX subset countable
    exact ⟨localized, b, hb, bound⟩
  · intro x member
    exact run.limitPoints_strict_extension_of_trace collection infinite data.trace
      (fun old next entry => (data.steps_entries old next entry).2)
      (fun source target z entry => (data.successors_entries source target z entry).2.2)
      indices extension member

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMainFinalFulfillment_oai
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ data : GroundMainOrdinalConstructionData M K C pairing unions powers separation,
      ∃ ordinalC : ordinalSetProperty C,
        letI := ordinalMainIndexPreorder ordinalC
        ∃ run : GroundMainPrefix M K C C (rationalCarrier data.seed.fractionCode)
            (rationalLtGraph data.seed.fractionCode) pairing unions powers separation (SetMembers C),
          run.indices = C ∧ run.PreservesOldProfiles ∧
          MainPrefixHistoryUnionCode data.history run.code ∧
          MainPrefixHistoryExtends data.history run.code ∧
          (∀ q, MainPrefixHistoryUnionCode data.history q → q = run.code) ∧
          GroundBelow M run.indices K ∧ ZFSet.rank run.code < ZFSet.rank K ∧
          ∃ i₀ : SetMembers C, run.key i₀ = ∅ ∧
            ∃ fulfilled : run.FinalFulfillment data.level i₀,
              let geometry := run.finalGeometry i₀
              let inclusions := run.finalInclusions i₀
              geometry.code ∈ M.sets ∧ ZFSet.rank geometry.code < ZFSet.rank K ∧
              GroundBelow M geometry.carrier K ∧ GroundBelow M geometry.actors K ∧
              inclusions.pointFamily ∈ M.sets ∧ inclusions.actorFamily ∈ M.sets ∧
              ZFSet.rank inclusions.pointFamily < ZFSet.rank K ∧
              ZFSet.rank inclusions.actorFamily < ZFSet.rank K ∧
              fulfilled.chronology.serial.code ∈ M.sets ∧
              ∀ N : TransitiveGround.{u}, M.sets ⊆ N.sets →
                Realize N.sets SetFormula.pairing Fin.elim0 →
                Realize N.sets SetFormula.union Fin.elim0 →
                Realize N.sets powerSet Fin.elim0 → SeparationSchema N.sets →
                Realize N.sets infinity Fin.elim0 → Realize N.sets SetFormula.choice Fin.elim0 →
                ∀ F ∈ N.sets, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F →
                  ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
                    ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ geometry.order := by
  dsimp only
  obtain ⟨data, ordinalC, run, indices, profiles, terminal, extension, unique, small, rank,
    i₀, zero, codeGround, codeRank, pointSmall, actorSmall, pointMaps, actorMaps,
    pointRank, actorRank, localized, growth⟩ :=
    M.exists_groundMainFinalGeometry pairing unions powers separation collection infinite choice hK standard
  let := ordinalMainIndexPreorder ordinalC
  obtain ⟨chronology⟩ := run.exists_finalChronology collection infinite choice hK standard
    small rank data.level
  have chosen := fun old next entry => (data.steps_entries old next entry).2
  have tasks := fun source target z entry => (data.successors_entries source target z entry).2.2
  let fulfilled : run.FinalFulfillment data.level i₀ := {
    chronology := chronology
    countable_localization := localized
    growth := growth
    directed := fun _ hx _ hy => run.limitPoints_directed hx hy
    separates := fun _ hW _ hd _ hx wd wx =>
      run.limitPoints_separation_of_trace collection infinite data.trace chosen tasks
        indices extension hW hd hx wd wx
    rectangles := fun _ _ _ _ _ _ rectangle hX firstUpper secondUpper =>
      run.final_rectangle_at_bound_of_trace collection infinite data.trace chosen tasks
        indices extension rectangle hX firstUpper secondUpper }
  refine ⟨data, ordinalC, run, indices, profiles, terminal, extension, unique, small, rank,
    i₀, zero, fulfilled, codeGround, codeRank, pointSmall, actorSmall, pointMaps,
    actorMaps, pointRank, actorRank, chronology.code_ground, ?_⟩
  intro N includes pairingN unionsN powersN separationN infiniteN choiceN F hF filter
  exact chronology.exists_extension_basis i₀ includes pairingN unionsN powersN separationN infiniteN
    choiceN ⟨data.seed.coordinateInjection, data.seed.injection_ground, data.seed.injection_code⟩
    data.seed.dense.irrefl hF filter

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundMainFinalFulfillment_oai.{u}
